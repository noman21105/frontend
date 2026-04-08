// ============================================================================
// VOICE ASSISTANT — Interruptible Streaming Conversation Engine
// ============================================================================
// KEY INSIGHT: Chrome pauses SpeechRecognition while SpeechSynthesis is active.
// To work around this, we use TWO independent systems:
//   1. SpeechRecognition — for transcribing the user's speech to text
//   2. Web Audio API (getUserMedia + AnalyserNode) — a Voice Activity Detector
//      (VAD) that monitors mic volume independently and triggers interrupts
//      even while TTS is playing. When VAD detects the user's voice, it:
//        a) Cancels TTS immediately
//        b) Sends interrupt to backend
//        c) SpeechRecognition automatically resumes once TTS stops
// ============================================================================

// === App State ===
const API_BASE = "https://backend-production-0c12.up.railway.app/";
const WS_BASE = "wss://backend-production-0c12.up.railway.app/ws";

let authToken = localStorage.getItem('auth_token') || null;
let currentUser = null;
let currentThreadId = null;
let ws = null;
let reconnectAttempts = 0;
const MAX_RECONNECT_ATTEMPTS = 10;
let reconnectTimer = null;

let isListening = false;
let isSpeaking = false;
let isGenerating = false;

// Audio Streamer State
let audioStreamer = null;
let interruptSent = false;
let hadServerAudioThisTurn = false;
let browserTtsUtterance = null;

// Debounce timer for accumulating final transcript segments
let finalTranscriptAccumulator = '';
let sendDebounceTimer = null;
const SEND_DEBOUNCE_MS = 400; // Wait 0.4s after last final result before sending

// Echo suppression: block ALL mic input while TTS is playing AND for a cooldown period after
let ttsCooldownActive = false;
let ttsCooldownTimer = null;
const TTS_COOLDOWN_MS = 500; // ms to suppress mic after TTS ends

// Master flag: true from first audio chunk received until cooldown ends
// This covers the ENTIRE window where the assistant's voice could be picked up
let ttsActive = false;

// Minimum audio blob size (bytes) to consider valid for Whisper
const MIN_AUDIO_BLOB_SIZE = 5000;

// Voice Activity Detection (VAD) state — works independently of SpeechRecognition
let audioContext = null;
let analyserNode = null;
let vadStream = null;
let vadActive = false;
const VAD_THRESHOLD = 20;  // Volume level (0-255) that counts as "user is speaking"
const VAD_CONSECUTIVE_FRAMES = 3; // Need N consecutive frames above threshold to trigger
let vadFramesAbove = 0;

// PCM Capture State
let pcmBuffer = new Float32Array(0);
let pcmMsgId = 0;
let pcmFallbackText = '';
let workletNode = null;
let msgCounter = 0;
let isWaitingForResponse = false;

// DOM Elements
const authOverlay = document.getElementById('auth-overlay');
const appContainer = document.getElementById('app-container');
const authForm = document.getElementById('auth-form');
const toggleAuthBtn = document.getElementById('toggle-auth');
const authTitle = document.getElementById('auth-title');
const authError = document.getElementById('auth-error');
const usernameInput = document.getElementById('username');
const passwordInput = document.getElementById('password');

const sidebar = document.getElementById('sidebar');
const toggleSidebarBtn = document.getElementById('toggle-sidebar');
const threadList = document.getElementById('thread-list');
const newChatBtn = document.getElementById('new-chat-btn');
const logoutBtn = document.getElementById('logout-btn');
const userDisplay = document.getElementById('user-display');

const chatContainer = document.getElementById('chat-container');
const threadTitleDisplay = document.getElementById('current-thread-title');
const micBtn = document.getElementById('mic-btn');
const transcriptEl = document.getElementById('transcript');
const visualizer = document.getElementById('visualizer');
const welcomeMessage = document.getElementById('welcome-message');
const voiceSelect = document.getElementById('voice-select');

let isSignupMode = false;

// === Speech Engine Setup ===
const SpeechRecognition = window.SpeechRecognition || window.webkitSpeechRecognition;
let recognition;
let manualStop = false;

if (SpeechRecognition) {
    recognition = new SpeechRecognition();
    recognition.continuous = true;
    recognition.interimResults = true;
    recognition.lang = 'en-US';
} else {
    transcriptEl.textContent = "Browser not supported";
}

// ============================================================================
// AUDIO STREAMER — Handles Gapless Playback of Audio Chunks
// ============================================================================
class AudioStreamer {
    constructor() {
        this.queue = [];
        this.isPlaying = false;
        this.currentAudio = null;
    }

    addChunk(base64Audio) {
        const audio = new Audio(`data:audio/mp3;base64,${base64Audio}`);
        audio.preload = 'auto';
        this.queue.push(audio);
        this.playNext();
    }

    playNext() {
        if (this.isPlaying || this.queue.length === 0) return;

        this.isPlaying = true;
        this.currentAudio = this.queue.shift();

        this.currentAudio.onended = () => {
            this.isPlaying = false;
            if (this.queue.length > 0) {
                this.playNext();
                return;
            }
            isSpeaking = false;
            startPostTTSCooldown();
        };

        this.currentAudio.onerror = () => {
            console.error("[Audio] Playback error");
            this.isPlaying = false;
            if (this.queue.length > 0) {
                this.playNext();
                return;
            }
            isSpeaking = false;
            startPostTTSCooldown();
        };

        this.currentAudio.play()
            .then(() => {
                isSpeaking = true;
            })
            .catch(err => {
                console.error("Play failed:", err);
                this.isPlaying = false;
            });
    }

    stop() {
        this.queue = [];
        this.isPlaying = false;
        isSpeaking = false;

        if (this.currentAudio) {
            this.currentAudio.pause();
            this.currentAudio.currentTime = 0;
            this.currentAudio = null;
        }
    }
}

// Initialize audioStreamer on first interaction
function initAudioStreamer() {
    if (!audioStreamer) {
        audioStreamer = new AudioStreamer();
    }
}

function speakWithBrowserTTS(text) {
    if (!('speechSynthesis' in window) || !text || !text.trim()) return;
    try {
        window.speechSynthesis.cancel();
        const utterance = new SpeechSynthesisUtterance(text.trim());
        utterance.rate = 1;
        utterance.pitch = 1;
        utterance.volume = 1;
        utterance.onstart = () => {
            isSpeaking = true;
            ttsActive = true;
            ttsCooldownActive = true;
            if (ttsCooldownTimer) clearTimeout(ttsCooldownTimer);
            stopRecordingForTTS();
        };
        utterance.onend = () => {
            browserTtsUtterance = null;
            isSpeaking = false;
            startPostTTSCooldown();
        };
        utterance.onerror = () => {
            browserTtsUtterance = null;
            isSpeaking = false;
            startPostTTSCooldown();
        };
        browserTtsUtterance = utterance;
        window.speechSynthesis.speak(utterance);
    } catch (err) {
        console.warn('[BrowserTTS] Failed to speak fallback audio:', err);
    }
}

// Avoid call stack overflow on large typed arrays.
function uint8ToBase64(uint8) {
    const CHUNK_SIZE = 0x8000;
    let binary = '';
    for (let i = 0; i < uint8.length; i += CHUNK_SIZE) {
        const chunk = uint8.subarray(i, i + CHUNK_SIZE);
        binary += String.fromCharCode.apply(null, chunk);
    }
    return btoa(binary);
}

function float32ToInt16(float32) {
    const int16 = new Int16Array(float32.length);
    for (let i = 0; i < float32.length; i++) {
        const s = Math.max(-1, Math.min(1, float32[i]));
        int16[i] = s < 0 ? s * 0x8000 : s * 0x7fff;
    }
    return int16;
}

function sendPCMIfAvailable() {
    if (pcmBuffer.length === 0) {
        if (pcmFallbackText && ws && ws.readyState === WebSocket.OPEN) {
            isWaitingForResponse = true;
            ws.send(JSON.stringify({ type: "chat", content: pcmFallbackText }));
        }
        return;
    }

    const MIN_PCM_SAMPLES = 22050; // 0.5 sec at 44100 Hz
    if (pcmBuffer.length < MIN_PCM_SAMPLES) {
        console.warn(`[PCM] Buffer too small (${pcmBuffer.length} samples), using fallback text`);
        if (pcmFallbackText && ws && ws.readyState === WebSocket.OPEN) {
            isWaitingForResponse = true;
            ws.send(JSON.stringify({ type: "chat", content: pcmFallbackText }));
        }
        return;
    }

    const pcm16 = float32ToInt16(pcmBuffer);
    const uint8 = new Uint8Array(pcm16.buffer);
    const base64 = uint8ToBase64(uint8);
    if (ws && ws.readyState === WebSocket.OPEN) {
        isWaitingForResponse = true;
        ws.send(JSON.stringify({
            type: "audio_input",
            content: base64,
            format: "pcm",
            sampleRate: audioContext ? audioContext.sampleRate : 44100,
            msgId: pcmMsgId,
            fallbackText: pcmFallbackText
        }));
    }
    pcmBuffer = new Float32Array(0);
}

// Called by AudioStreamer when audio finishes — this is the correct time to suppress echo
function startPostTTSCooldown() {
    ttsCooldownActive = true;
    pcmBuffer = new Float32Array(0); // Clear PCM buffer
    if (ttsCooldownTimer) clearTimeout(ttsCooldownTimer);
    ttsCooldownTimer = setTimeout(() => {
        ttsCooldownActive = false;
        ttsActive = false; // Master TTS flag finally cleared
        pcmBuffer = new Float32Array(0); // One final clear after cooldown
        console.log('[TTS] Cooldown ended, mic is now active');
    }, TTS_COOLDOWN_MS);
}

// Stop PCM accumulation when TTS starts to avoid capturing echo
function stopRecordingForTTS() {
    pcmBuffer = new Float32Array(0); // Clear PCM buffer

    // Kill any pending send — the accumulated transcript is probably echo
    if (sendDebounceTimer) {
        clearTimeout(sendDebounceTimer);
        sendDebounceTimer = null;
    }
    finalTranscriptAccumulator = '';
}

// ============================================================================
// VOICE ACTIVITY DETECTOR (VAD) — Monitors mic via Web Audio API
// ============================================================================
// This runs independently of SpeechRecognition. It uses getUserMedia to get
// a raw audio stream, pipes it through an AnalyserNode, and polls the volume.
// When volume exceeds the threshold while the assistant is speaking, it
// immediately triggers an interrupt (cancels TTS + notifies backend).
// This solves the Chrome bug where SpeechRecognition pauses during TTS.
// ============================================================================

async function startVAD() {
    if (vadActive) return;
    try {
        vadStream = await navigator.mediaDevices.getUserMedia({
            audio: {
                echoCancellation: true,
                noiseSuppression: true,
                autoGainControl: true,
                channelCount: 1
            }
        });

        audioContext = new (window.AudioContext || window.webkitAudioContext)();
        await audioContext.audioWorklet.addModule('./audio-worklet.js');

        const source = audioContext.createMediaStreamSource(vadStream);
        analyserNode = audioContext.createAnalyser();
        analyserNode.fftSize = 512;
        analyserNode.smoothingTimeConstant = 0.3;
        source.connect(analyserNode);

        workletNode = new AudioWorkletNode(audioContext, 'pcm-capture');
        workletNode.port.onmessage = (event) => {
            if (event.data.type === 'pcm_chunk') {
                if (ttsActive || ttsCooldownActive) return;
                const newBuffer = new Float32Array(pcmBuffer.length + event.data.data.length);
                newBuffer.set(pcmBuffer);
                newBuffer.set(event.data.data, pcmBuffer.length);
                pcmBuffer = newBuffer;
            }
        };
        source.connect(workletNode);

        // Do NOT connect to audioContext.destination — we don't want to hear ourselves
        vadActive = true;
        vadFramesAbove = 0;
        pollVAD();
        console.log("[VAD] Voice Activity Detector started");
    } catch (err) {
        console.error("[VAD] Failed to start:", err);
    }
}

function stopVAD() {
    vadActive = false;
    sendPCMIfAvailable();
    pcmBuffer = new Float32Array(0);
    if (workletNode) {
        workletNode.disconnect();
        workletNode = null;
    }
    if (vadStream) {
        vadStream.getTracks().forEach(t => t.stop());
        vadStream = null;
    }
    if (audioContext && audioContext.state !== 'closed') {
        audioContext.close();
        audioContext = null;
    }
    analyserNode = null;
    vadFramesAbove = 0;
}

function pollVAD() {
    if (!vadActive || !analyserNode) return;

    const dataArray = new Uint8Array(analyserNode.frequencyBinCount);
    analyserNode.getByteFrequencyData(dataArray);

    // Calculate average volume across frequency bins
    let sum = 0;
    for (let i = 0; i < dataArray.length; i++) {
        sum += dataArray[i];
    }
    const avgVolume = sum / dataArray.length;

    // Only trigger interrupt if assistant is actively speaking or generating
    if ((isSpeaking || isGenerating) && avgVolume > VAD_THRESHOLD) {
        vadFramesAbove++;
        if (vadFramesAbove >= VAD_CONSECUTIVE_FRAMES) {
            console.log(`[VAD] User voice detected (vol: ${avgVolume.toFixed(1)}), triggering interrupt`);
            triggerInterrupt();
            vadFramesAbove = 0;
        }
    } else {
        vadFramesAbove = 0;
    }

    // Poll at ~60fps for responsive detection
    requestAnimationFrame(pollVAD);
}

// ============================================================================
// AUTH LOGIC
// ============================================================================
toggleAuthBtn.addEventListener('click', () => {
    isSignupMode = !isSignupMode;
    toggleAuthBtn.textContent = isSignupMode ? "Log in" : "Sign up";
    authTitle.textContent = isSignupMode ? "Create Account" : "Welcome Back";
    document.getElementById('auth-switch-text').firstChild.textContent = isSignupMode ? "Already have an account? " : "Don't have an account? ";
    authError.textContent = "";
});

authForm.addEventListener('submit', async (e) => {
    e.preventDefault();
    const endpoint = isSignupMode ? "/signup" : "/login";
    authError.textContent = "";
    try {
        const res = await fetch(`${API_BASE}${endpoint}`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ username: usernameInput.value, password: passwordInput.value })
        });
        const data = await res.json();
        if (res.ok) {
            authToken = data.token;
            currentUser = data.user;
            localStorage.setItem('auth_token', authToken);
            checkAuth();
        } else {
            authError.textContent = data.detail || "Authentication failed";
        }
    } catch (e) {
        authError.textContent = "Server error";
    }
});

logoutBtn.addEventListener('click', () => {
    authToken = null;
    currentUser = null;
    localStorage.removeItem('auth_token');
    if (ws) ws.close();
    stopVAD();
    checkAuth();
});

function checkAuth() {
    if (authToken) {
        authOverlay.style.display = 'none';
        appContainer.style.display = 'flex';
        userDisplay.textContent = usernameInput.value || "User";
        loadThreads();
    } else {
        authOverlay.style.display = 'flex';
        appContainer.style.display = 'none';
        usernameInput.value = '';
        passwordInput.value = '';
        if (ws) ws.close();
        stopVAD();
    }
}

// === Threads Management ===
async function loadThreads() {
    if (!authToken) return;
    try {
        const res = await fetch(`${API_BASE}/threads?token=${authToken}`);
        const threads = await res.json();
        threadList.innerHTML = '';
        threads.forEach(t => {
            const div = document.createElement('div');
            div.className = 'thread-item';
            div.textContent = t.title || "New Chat";
            if (t.id === currentThreadId) div.classList.add('active');
            div.onclick = () => selectThread(t.id, t.title);
            threadList.appendChild(div);
        });

        if (!currentThreadId && threads.length > 0) {
            selectThread(threads[0].id, threads[0].title);
        } else if (threads.length === 0) {
            createNewThread();
        }
    } catch (e) {
        console.error("Failed to load threads", e);
    }
}

async function createNewThread() {
    try {
        const res = await fetch(`${API_BASE}/threads?token=${authToken}`, { method: 'POST' });
        const thread = await res.json();
        selectThread(thread.id, thread.title);
        loadThreads();
    } catch (e) {
        console.error("Failed to create thread", e);
    }
}

newChatBtn.addEventListener('click', createNewThread);

async function selectThread(id, title) {
    currentThreadId = id;
    threadTitleDisplay.textContent = title || "Voice Assistant";
    chatContainer.innerHTML = '';
    micBtn.disabled = false;
    transcriptEl.textContent = "Tap the microphone to start";
    transcriptEl.className = 'transcript';

    Array.from(threadList.children).forEach(child => {
        child.classList.remove('active');
        if (child.textContent === title) child.classList.add('active');
    });

    if (window.innerWidth <= 768) {
        sidebar.classList.remove('open');
    }

    try {
        const res = await fetch(`${API_BASE}/threads/${id}/messages?token=${authToken}`);
        const messages = await res.json();
        if (messages.length === 0) {
            chatContainer.appendChild(welcomeMessage);
        } else {
            messages.forEach(m => addMessage(m.role, m.content));
        }
    } catch (e) {
        console.error("Failed to load messages", e);
    }

    connectWebSocket();
}

toggleSidebarBtn.addEventListener('click', () => {
    sidebar.classList.toggle('open');
});

// ============================================================================
// WEBSOCKET — Handles streaming tokens and interrupt signals
// ============================================================================
function connectWebSocket() {
    if (reconnectTimer) { clearTimeout(reconnectTimer); reconnectTimer = null; }
    if (ws && ws.readyState !== WebSocket.CLOSED) {
        ws.onclose = null;
        ws.onerror = null;
        ws.onmessage = null;
        ws.onopen = null;
        ws.close();
    }
    ws = new WebSocket(`${WS_BASE}/${authToken}/${currentThreadId}`);

    let currentAssistantMsgDiv = null;

    ws.onopen = () => {
        console.log("[WS] Connected");
        reconnectAttempts = 0; // reset on successful connection
        micBtn.disabled = false;
    };

    ws.onmessage = (event) => {
        const data = JSON.parse(event.data);

        if (data.error) {
            console.error("WS Error:", data.error);
            addMessage('error', data.error);
            isWaitingForResponse = false;
            return;
        }

        // --- PING: Keepalive from backend, ignore silently ---
        if (data.type === 'ping') return;

        // --- TRANSCRIPTION UPDATE: Replace interim user text with Whisper accuracy ---
        if (data.type === 'transcription_update') {
            const targetMsgId = data.msgId; // If backend echoed it
            const targetEl = document.getElementById("latest-user-msg");
            if (targetEl) {
                targetEl.textContent = data.content;
                targetEl.removeAttribute("id");
            }
            return;
        }

        // --- TOKEN: A piece of the assistant's streamed response ---
        if (data.type === 'token') {
            isWaitingForResponse = false;
            isGenerating = true;
            interruptSent = false;
            // Fresh assistant turn starts when first token arrives.
            if (!currentAssistantMsgDiv) hadServerAudioThisTurn = false;
            micBtn.classList.add('speaking');
            transcriptEl.textContent = "Assistant is responding...";

            if (!currentAssistantMsgDiv) {
                hideTypingIndicator();
                currentAssistantMsgDiv = createMessageDiv('assistant');
                chatContainer.appendChild(currentAssistantMsgDiv);
            }

            currentAssistantMsgDiv.textContent += data.content;
            chatContainer.scrollTop = chatContainer.scrollHeight;

            // --- AUDIO: A chunk of generated speech ---
        } else if (data.type === 'audio') {
            // Ignore stale audio from an interrupted/cancelled generation
            if (interruptSent) {
                console.log('[Audio] Ignoring stale audio chunk (interrupt active)');
                return;
            }
            hadServerAudioThisTurn = true;
            initAudioStreamer();
            // Set master TTS flag BEFORE anything else
            ttsActive = true;
            ttsCooldownActive = true;
            if (ttsCooldownTimer) clearTimeout(ttsCooldownTimer);
            // STOP the recorder entirely (not pause — pause corrupts WebM headers)
            // A fresh recorder will be created after TTS + cooldown ends
            stopRecordingForTTS();
            if (data.format === "mp3") {
                audioStreamer.addChunk(data.content);
            }

            // --- DONE: Assistant finished its response ---
        } else if (data.type === 'done') {
            isWaitingForResponse = false;
            isGenerating = false;
            const finalAssistantText = currentAssistantMsgDiv ? currentAssistantMsgDiv.textContent : '';
            currentAssistantMsgDiv = null;
            micBtn.classList.remove('speaking');
            // Keep buffered PCM clean between turns.
            pcmBuffer = new Float32Array(0);
            if (isListening) {
                transcriptEl.textContent = "Listening...";
            } else {
                transcriptEl.textContent = "Tap the microphone to start";
            }
            // Backend TTS failed silently for this turn: use browser TTS fallback.
            if (!hadServerAudioThisTurn && finalAssistantText && !interruptSent) {
                console.log('[Audio] No backend audio received, using browser TTS fallback');
                speakWithBrowserTTS(finalAssistantText);
            }

            // --- INTERRUPTED: Backend confirmed generation was cancelled ---
        } else if (data.type === 'interrupted') {
            isWaitingForResponse = false;
            isGenerating = false;
            isSpeaking = false;
            ttsActive = false; // CRITICAL: unblock mic immediately
            currentAssistantMsgDiv = null;
            if (audioStreamer) audioStreamer.stop();
            micBtn.classList.remove('speaking');
            // Clear audio and transcript accumulators
            pcmBuffer = new Float32Array(0);
            finalTranscriptAccumulator = '';
            if (sendDebounceTimer) { clearTimeout(sendDebounceTimer); sendDebounceTimer = null; }
            // Very brief cooldown to let echo dissipate, then restart recorder
            ttsCooldownActive = true;
            if (ttsCooldownTimer) clearTimeout(ttsCooldownTimer);
            ttsCooldownTimer = setTimeout(() => {
                ttsCooldownActive = false;
                pcmBuffer = new Float32Array(0);
                interruptSent = false; // Allow future interrupts
            }, 250);
            if (isListening) {
                transcriptEl.textContent = "Listening...";
            } else {
                transcriptEl.textContent = "Tap the microphone to start";
            }
        }
    };

    ws.onclose = (event) => {
        console.log(`[WS] Disconnected (code=${event.code})`);
        isGenerating = false;
        isSpeaking = false;

        // Don't reconnect if the user logged out or the tab is closing
        if (!authToken || !currentThreadId) return;

        if (reconnectAttempts < MAX_RECONNECT_ATTEMPTS) {
            const delay = Math.min(1000 * Math.pow(1.5, reconnectAttempts), 15000);
            reconnectAttempts++;
            console.log(`[WS] Reconnecting in ${Math.round(delay / 1000)}s (attempt ${reconnectAttempts})...`);
            transcriptEl.textContent = `Reconnecting... (${reconnectAttempts}/${MAX_RECONNECT_ATTEMPTS})`;
            micBtn.disabled = true;
            micBtn.classList.remove('listening', 'speaking');
            reconnectTimer = setTimeout(connectWebSocket, delay);
        } else {
            addMessage('error', "Connection lost. Please refresh the page.");
            micBtn.disabled = true;
            micBtn.classList.remove('listening', 'speaking');
            transcriptEl.textContent = "Disconnected. Refresh page.";
            if (isListening) recognition.stop();
        }
    };

    ws.onerror = (err) => {
        console.error("[WS] Error:", err);
    };
}

function cancelTTS() {
    if (audioStreamer) audioStreamer.stop();
    if ('speechSynthesis' in window) window.speechSynthesis.cancel();
    browserTtsUtterance = null;
    isSpeaking = false;
}

// ============================================================================
// INTERRUPT HANDLER
// ============================================================================
// Called by either:
//   1. VAD (voice activity detector) — when user speaks while TTS is playing
//   2. SpeechRecognition onresult — when user speaks while generating
//   3. Mic button click — manual interrupt
// ============================================================================

function triggerInterrupt() {
    if (interruptSent) return;
    interruptSent = true;

    console.log("[Interrupt] Cancelling TTS and notifying backend");

    // 1. Kill TTS immediately
    cancelTTS();

    // 2. CRITICAL: Reset ALL TTS-related flags so mic is unblocked
    ttsActive = false;
    isSpeaking = false;
    isWaitingForResponse = false;
    if (ttsCooldownTimer) { clearTimeout(ttsCooldownTimer); ttsCooldownTimer = null; }

    // 3. Tell backend to stop LLM streaming
    if (ws && ws.readyState === WebSocket.OPEN) {
        ws.send(JSON.stringify({ type: "interrupt" }));
    }

    // 4. Update UI state
    isGenerating = false;
    micBtn.classList.remove('speaking');
    transcriptEl.textContent = "Listening...";

    // 5. Clear accumulated audio (it contains echo) and pending transcript
    pcmBuffer = new Float32Array(0);
    finalTranscriptAccumulator = '';
    if (sendDebounceTimer) { clearTimeout(sendDebounceTimer); sendDebounceTimer = null; }

    // 6. Brief echo cooldown then allow mic input again
    ttsCooldownActive = true;
    setTimeout(() => {
        ttsCooldownActive = false;
        interruptSent = false; // Allow re-interrupt for next response
    }, 300);
}

// ============================================================================
// SPEECH RECOGNITION — Always-on continuous listening
// ============================================================================
if (recognition) {
    recognition.onstart = function () {
        isListening = true;
        manualStop = false;
        transcriptEl.textContent = "Listening...";
        transcriptEl.classList.add('active');
        visualizer.classList.add('active');
        micBtn.classList.add('listening');
    };

    recognition.onresult = function (event) {
        let interimTranscript = '';
        let newFinalTranscript = '';

        for (let i = event.resultIndex; i < event.results.length; ++i) {
            if (event.results[i].isFinal) {
                newFinalTranscript += event.results[i][0].transcript;
            } else {
                interimTranscript += event.results[i][0].transcript;
            }
        }

        // ECHO SUPPRESSION & RESPONDING GAP SUPPRESSION
        // We must suppress ALL recognition during TTS playback, cooldown, AND generation.
        // We also suppress it when waiting for the backend to start generating.
        if (ttsActive || ttsCooldownActive || isSpeaking || isWaitingForResponse) {
            // Silently discard — this is the assistant's own voice echoing back
            // or we are just waiting for a response to our previous input
            return;
        }
        if (isGenerating) {
            // LLM is streaming text (before audio starts) — trigger interrupt
            if (interimTranscript.trim() || newFinalTranscript.trim()) {
                triggerInterrupt();
            }
            return;
        }

        // Show the full accumulated + current interim text so user sees everything
        const displayText = (finalTranscriptAccumulator + ' ' + (newFinalTranscript || interimTranscript)).trim();
        if (displayText) {
            transcriptEl.textContent = displayText;
            transcriptEl.classList.add('active');
        }

        // When we get a final result, accumulate it
        if (newFinalTranscript.trim() !== '') {
            finalTranscriptAccumulator += (finalTranscriptAccumulator ? ' ' : '') + newFinalTranscript.trim();
        }

        // Restart debounce timer if there is ANY speech activity (interim or final)
        // This prevents cutting the user off while they are still generating interim speech
        if (newFinalTranscript.trim() !== '' || interimTranscript.trim() !== '') {
            if (sendDebounceTimer) {
                clearTimeout(sendDebounceTimer);
            }

            // Start a new debounce timer — only send after silence
            sendDebounceTimer = setTimeout(() => {
                // CRITICAL: Re-check echo suppression when debounce fires.
                // The timer may have been set BEFORE TTS started playing.
                if (ttsActive || ttsCooldownActive || isSpeaking || isGenerating || isWaitingForResponse) {
                    console.log('[Debounce] Firing during TTS/generation/wait — discarding');
                    finalTranscriptAccumulator = '';
                    sendDebounceTimer = null;
                    return;
                }

                // If there's still an active interim transcript that hasn't finalized after silence,
                // append it so we don't lose the user's trailing words.
                let rawMessage = (finalTranscriptAccumulator + ' ' + interimTranscript).trim();
                const fullMessage = normalizeTranscript(rawMessage);

                finalTranscriptAccumulator = '';
                sendDebounceTimer = null;

                if (!fullMessage) return;

                console.log(`[Speech] Sending accumulated transcript visually: "${fullMessage}"`);

                msgCounter++;
                const msgId = "msg-" + msgCounter;
                addMessage('user', fullMessage, msgId);

                // Keep track to update it when Whisper transcription arrives
                const newMsgEl = document.getElementById(msgId);
                if (newMsgEl) newMsgEl.id = "latest-user-msg";

                transcriptEl.textContent = "Thinking...";
                transcriptEl.classList.remove('active');

                if (welcomeMessage && welcomeMessage.parentNode) {
                    welcomeMessage.remove();
                }

                showTypingIndicator();

                // Send PCM audio for accurate transcription
                pcmFallbackText = fullMessage;
                sendPCMIfAvailable();

                interruptSent = false;

                // Restart browser recognition to clear its internal state
                recognition.stop();
            }, SEND_DEBOUNCE_MS);
        }
    };

    // Auto-restart: keep mic alive forever with retry on failure
    let _restartAttempts = 0;
    recognition.onend = function () {
        if (!manualStop) {
            const delay = Math.min(100 * Math.pow(2, _restartAttempts), 2000);
            setTimeout(() => {
                if (!manualStop) {
                    try {
                        recognition.start();
                        _restartAttempts = 0; // reset on success
                    } catch (e) {
                        _restartAttempts++;
                        console.warn(`[Recognition] Restart failed (attempt ${_restartAttempts}):`, e.message);
                        if (_restartAttempts < 5) {
                            // Retry: fire onend logic again by simulating the end state
                            setTimeout(() => recognition.onend(), 500);
                        } else {
                            console.error('[Recognition] Too many restart failures, giving up');
                            transcriptEl.textContent = 'Mic error. Tap to retry.';
                        }
                    }
                }
            }, delay);
        } else {
            isListening = false;
            _restartAttempts = 0;
            visualizer.classList.remove('active');
            micBtn.classList.remove('listening');
            transcriptEl.textContent = "Mic off. Tap to start";
            stopVAD();
        }
    };

    // Only fatal errors stop the mic
    recognition.onerror = function (event) {
        console.error("Recognition Error:", event.error);
        if (event.error === 'not-allowed' || event.error === 'audio-capture') {
            manualStop = true;
            isListening = false;
            visualizer.classList.remove('active');
            micBtn.classList.remove('listening');
            transcriptEl.textContent = `Mic error: ${event.error}`;
            stopVAD();
        }
    };
}

// === UI Helpers ===
micBtn.addEventListener('click', () => {
    if (isListening) {
        // --- STOP: Turn off mic ---
        manualStop = true;
        recognition.stop();
        stopVAD();
    } else {
        // --- START: Turn on mic + VAD ---
        manualStop = false;

        // Set PCM message ID
        pcmMsgId = msgCounter++;
        pcmFallbackText = '';

        // If assistant is talking when user clicks mic, interrupt first
        if (isGenerating || isSpeaking) {
            triggerInterrupt();
        }

        try {
            recognition.start();
            startVAD(); // Start independent voice activity monitoring
        } catch (e) {
            console.error(e);
        }
    }
});

function createMessageDiv(role) {
    const msgDiv = document.createElement('div');
    msgDiv.className = `message ${role}`;
    if (role === 'error') {
        msgDiv.style.borderColor = 'var(--accent-red)';
        msgDiv.style.color = 'var(--accent-red)';
    }
    return msgDiv;
}

function addMessage(role, content, msgId = null) {
    if (welcomeMessage && welcomeMessage.parentNode) {
        welcomeMessage.remove();
    }
    const msgDiv = createMessageDiv(role);
    msgDiv.textContent = content;
    if (msgId) msgDiv.id = msgId;
    chatContainer.appendChild(msgDiv);
    chatContainer.scrollTop = chatContainer.scrollHeight;

    if (role === 'user' && chatContainer.children.length === 1) {
        setTimeout(loadThreads, 1000);
    }
}

let typingDiv = null;
function showTypingIndicator() {
    hideTypingIndicator();
    typingDiv = createMessageDiv('assistant');
    typingDiv.classList.add('typing-indicator');
    typingDiv.innerHTML = '<span></span><span></span><span></span>';
    chatContainer.appendChild(typingDiv);
    chatContainer.scrollTop = chatContainer.scrollHeight;
}

function hideTypingIndicator() {
    if (typingDiv) {
        typingDiv.remove();
        typingDiv = null;
    }
}

// ============================================================================
// TRANSCRIPT NORMALIZER — Cleans up ASR/SpeechRecognition output
// ============================================================================
function normalizeTranscript(text) {
    if (!text) return '';
    // Trim whitespace
    let normalized = text.trim();
    // Collapse multiple spaces into one
    normalized = normalized.replace(/\s+/g, ' ');
    // Capitalize first letter
    if (normalized.length > 0) {
        normalized = normalized.charAt(0).toUpperCase() + normalized.slice(1);
    }
    return normalized;
}

// === Initialize ===
checkAuth();
