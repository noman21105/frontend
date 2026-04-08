// audio-worklet.js
class PCMCaptureProcessor extends AudioWorkletProcessor {
  constructor() {
    super();
    this.buffer = [];
    this.chunkSize = 4096; // ~93ms at 44.1kHz
  }

  process(inputs, outputs) {
    const input = inputs[0];
    if (input && input.length > 0) {
      const channel = input[0]; // first channel (mono)
      this.buffer.push(...channel);

      if (this.buffer.length >= this.chunkSize) {
        // Send PCM chunk
        this.port.postMessage({
          type: 'pcm_chunk',
          data: Float32Array.from(this.buffer)
        });
        this.buffer = [];
      }
    }
    return true;
  }
}

registerProcessor('pcm-capture', PCMCaptureProcessor);