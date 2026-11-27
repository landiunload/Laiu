(() => {
  const wavPrefix = 'data:audio/wav;base64,';
  const sampleRate = 48000;

  async function encodeTake(blob) {
    const context = new OfflineAudioContext(1, 1, sampleRate);
    const decoded = await context.decodeAudioData(await blob.arrayBuffer());
    const samples = decoded.getChannelData(0);
    if (!samples.some(sample => Math.abs(sample) >= 1 / 32768)) {
      throw new Error('В записи тишина. Проверьте микрофон и попробуйте ещё раз.');
    }
    const wav = new ArrayBuffer(44 + samples.length * 2);
    const header = new DataView(wav);
    header.setUint32(0, 0x52494646); // RIFF
    header.setUint32(4, wav.byteLength - 8, true);
    header.setUint32(8, 0x57415645); // WAVE
    header.setUint32(12, 0x666d7420); // fmt
    header.setUint32(16, 16, true);
    header.setUint16(20, 1, true);
    header.setUint16(22, 1, true);
    header.setUint32(24, sampleRate, true);
    header.setUint32(28, sampleRate * 2, true);
    header.setUint16(32, 2, true);
    header.setUint16(34, 16, true);
    header.setUint32(36, 0x64617461); // data
    header.setUint32(40, samples.length * 2, true);
    samples.forEach((sample, index) => {
      const clipped = Math.min(1, Math.max(-1, sample));
      header.setInt16(44 + index * 2, Math.round(clipped * (clipped < 0 ? 32768 : 32767)), true);
    });
    return new Promise((resolve, reject) => {
      const reader = new FileReader();
      reader.onload = () => resolve(reader.result);
      reader.onerror = () => reject(reader.error);
      reader.readAsDataURL(new Blob([wav], { type: 'audio/wav' }));
    });
  }

  async function fingerprint(phrases, audio) {
    const encoder = new TextEncoder();
    const chunks = [];
    for (const phrase of phrases) {
      if (!Object.hasOwn(audio, phrase)) continue;
      const url = audio[phrase];
      if (typeof url !== 'string' || !url.startsWith(wavPrefix)) throw new Error('Expected WAV.');
      const bytes = Uint8Array.from(atob(url.slice(wavPrefix.length)), char => char.charCodeAt(0));
      const header = new DataView(bytes.buffer);
      if (bytes.length <= 44 || bytes.length % 2 !== 0 ||
          header.getUint32(0) !== 0x52494646 || header.getUint32(4, true) !== bytes.length - 8 ||
          header.getUint32(8) !== 0x57415645 || header.getUint32(12) !== 0x666d7420 ||
          header.getUint32(16, true) !== 16 || header.getUint16(20, true) !== 1 ||
          header.getUint16(22, true) !== 1 || header.getUint32(24, true) !== sampleRate ||
          header.getUint16(34, true) !== 16 || header.getUint32(36) !== 0x64617461 ||
          header.getUint32(40, true) !== bytes.length - 44) throw new Error('Invalid WAV.');
      chunks.push(encoder.encode(phrase), bytes);
    }
    const joined = new Uint8Array(chunks.reduce((size, chunk) => size + chunk.length, 0));
    let offset = 0;
    for (const chunk of chunks) {
      joined.set(chunk, offset);
      offset += chunk.length;
    }
    const hash = new Uint8Array(await crypto.subtle.digest('SHA-256', joined));
    return Array.from(hash, byte => byte.toString(16).padStart(2, '0')).join('');
  }

  window.enableLaiuRecording = (phrases, { show, showMessage, downloadJson, setListeningAudio }) => {
    const element = id => document.getElementById(id);
    const capture = element('capture');
    const accept = element('acceptTake');
    const preview = element('previewTake');
    const save = element('downloadBundle');
    const use = element('useBundle');
    const back = element('backToIntro');
    const recordVoice = element('recordVoice');
    const open = element('openBundle');
    const file = element('bundleFile');
    const status = element('recordStatus');
    const canRecord = Boolean(navigator.mediaDevices?.getUserMedia && window.MediaRecorder && window.OfflineAudioContext);
    let audio = {};
    let phrase;
    let recorder;
    let stream;
    let request;

    function releaseMicrophone() {
      stream?.getTracks().forEach(track => track.stop());
      stream = undefined;
    }

    function resetPreview() {
      preview.pause();
      preview.removeAttribute('src');
      preview.load();
      preview.hidden = true;
      accept.hidden = true;
    }

    function showPhrase() {
      resetPreview();
      const count = Object.keys(audio).length;
      phrase = phrases.find(item => !Object.hasOwn(audio, item));
      element('recordProgress').textContent = `Готово ${count} из ${phrases.length}`;
      element('recordPhrase').textContent = phrase ?? 'Набор готов';
      capture.hidden = !phrase || !canRecord;
      capture.textContent = 'Записать фразу';
      save.textContent = phrase ? 'Скачать черновик' : 'Скачать набор';
      save.disabled = !count;
      use.hidden = Boolean(phrase);
      status.textContent = phrase && !canRecord ? 'Откройте страницу в браузере с доступом к микрофону.' : '';
    }

    function showRecorder() {
      show('recording');
      showPhrase();
      element('recordingTitle').focus();
    }

    capture.onclick = async () => {
      if (recorder?.state === 'recording') {
        capture.disabled = true;
        recorder.stop();
        releaseMicrophone();
        return;
      }

      element('message').hidden = true;
      resetPreview();
      status.textContent = 'Ожидаем доступ к микрофону.';
      capture.disabled = true;
      const attempt = {};
      request = attempt;
      try {
        const input = await navigator.mediaDevices.getUserMedia({
          audio: { channelCount: 1, echoCancellation: false, noiseSuppression: false, autoGainControl: false },
        });
        if (request !== attempt) {
          input.getTracks().forEach(track => track.stop());
          return;
        }
        stream = input;
        recorder = new MediaRecorder(stream);
        const chunks = [];
        const take = new Promise((resolve, reject) => {
          recorder.ondataavailable = event => chunks.push(event.data);
          recorder.onerror = event => reject(event.error);
          recorder.onstop = () => resolve(new Blob(chunks, { type: recorder.mimeType }));
          recorder.start();
        });
        back.disabled = true;
        save.disabled = true;
        capture.disabled = false;
        capture.textContent = 'Остановить запись';
        status.textContent = 'Микрофон записывает.';
        const blob = await take;
        releaseMicrophone();
        capture.disabled = true;
        status.textContent = 'Подготавливаем запись.';
        if (!blob.size) throw new Error('Запись пустая. Попробуйте ещё раз.');
        preview.src = await encodeTake(blob);
        preview.hidden = false;
        accept.hidden = false;
        status.textContent = 'Прослушайте запись или запишите фразу заново.';
        accept.focus();
      } catch (error) {
        if (request !== attempt) return;
        status.textContent = '';
        showMessage(error.name === 'NotAllowedError'
          ? 'Браузер не получил доступ к микрофону. Проверьте разрешение и попробуйте снова.'
          : error.constructor === Error
            ? error.message
            : 'Не удалось записать фразу. Проверьте микрофон и попробуйте снова.');
      } finally {
        if (request === attempt) {
          releaseMicrophone();
          recorder = undefined;
          capture.disabled = false;
          capture.textContent = accept.hidden ? 'Записать фразу' : 'Перезаписать';
          back.disabled = false;
          save.disabled = !Object.keys(audio).length;
        }
      }
    };

    accept.onclick = () => {
      audio[phrase] = preview.src;
      showPhrase();
      (phrase ? capture : save).focus();
    };

    recordVoice.onclick = showRecorder;
    back.onclick = () => {
      request = undefined;
      capture.disabled = false;
      resetPreview();
      show('intro');
      recordVoice.focus();
    };

    save.onclick = async () => {
      try {
        const snapshot = { ...audio };
        const audioSet = await fingerprint(phrases, snapshot);
        const name = Object.keys(snapshot).length === phrases.length
          ? 'laiu-voice.json' : 'laiu-voice-draft.json';
        downloadJson({ version: 1, phrases, audioSet, audio: snapshot }, name);
      } catch {
        showMessage('Не удалось сохранить файл с записями. Попробуйте ещё раз.');
      }
    };

    function useRecordings(audioSet) {
      setListeningAudio({ source: 'human', audioSet, audio: { ...audio } });
      show('intro');
      element('start').focus();
    }

    use.onclick = async () => {
      use.disabled = true;
      back.disabled = true;
      try {
        useRecordings(await fingerprint(phrases, audio));
      } catch {
        showMessage('Не удалось подготовить записи к пробе.');
      } finally {
        use.disabled = false;
        back.disabled = false;
      }
    };

    open.onclick = () => file.click();
    file.onchange = async () => {
      const selected = file.files[0];
      file.value = '';
      if (!selected) return;
      const start = element('start');
      [start, open, recordVoice].forEach(button => { button.disabled = true; });
      element('message').hidden = true;
      try {
        const bundle = JSON.parse(await selected.text());
        if (bundle.version !== 1 || !Array.isArray(bundle.phrases) ||
            bundle.phrases.length !== phrases.length || !phrases.every((item, index) => item === bundle.phrases[index])) {
          showMessage('Для этого файла нужен набор фраз из того же выпуска Laiu.');
          return;
        }
        const keys = Object.keys(bundle.audio);
        if (!keys.length || !keys.every(phrase => phrases.includes(phrase)) ||
            bundle.audioSet !== await fingerprint(phrases, bundle.audio)) throw new Error('Invalid voice bundle.');
        audio = bundle.audio;
        if (keys.length === phrases.length) useRecordings(bundle.audioSet);
        else showRecorder();
      } catch {
        showMessage('Не удалось открыть файл с записями. Выберите сохранённый набор или черновик.');
      } finally {
        [start, open, recordVoice].forEach(button => { button.disabled = false; });
        if (!element('intro').hidden && element('message').hidden) start.focus();
      }
    };

    if (window.crypto?.subtle) {
      open.disabled = false;
      recordVoice.disabled = !canRecord;
    }
  };
})();
