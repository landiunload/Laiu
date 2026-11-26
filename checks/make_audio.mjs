// Rebuild with @echogarden/espeak-ng-emscripten 0.3.5.
// Pass the absolute path to espeak-ng.js if installed outside the repository.
import { mkdir, readFile, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

const output = new URL("../Звучание/", import.meta.url);
const notes = (await readFile(new URL("../Фонология.md", import.meta.url), "utf8")).replaceAll("\r\n", "\n");
const clips = [...notes.matchAll(/!\[\[Звучание\/([^\]\n]+\.wav)\]\]\n((?:> \*\*`[^`\n]+`\*\*[^\n]*\n)+)/gu)];
if (clips.length === 0) throw new Error("В фонологии нет размеченных аудиопримеров");

const engine = process.argv[2]
  ? pathToFileURL(resolve(process.argv[2])).href
  : "@echogarden/espeak-ng-emscripten";
const { default: init } = await import(engine);
const module = await init();
const voice = new module.eSpeakNGWorker();
voice.set_voice("es");
voice.set_rate(145);
voice.set_pitch(53);

const phonemes = {
  а: "a", э: "E", и: "i", о: "o", у: "u", п: "p", б: "b", т: "t",
  к: "k", в: "v", с: "s", м: "m", н: "n", р: "*", л: "l",
};
const vowels = new Set("аэиоу");
const sampleRate = 22_050;
const ipaExceptions = { э: "ɛ", р: "ɾ" };

function pronounce(word) {
  let sounds = "";
  let stressed = false;
  let previous = "";
  for (const run of word.match(/(.)\1*/gu)) {
    const letter = run[0];
    if (!(letter in phonemes)) throw new Error(`Неизвестный знак ${letter} в слове ${word}`);
    if (!vowels.has(letter)) {
      sounds += phonemes[letter].repeat(run.length);
    } else {
      if (vowels.has(previous)) sounds += "|";
      if (!stressed) sounds += "'";
      sounds += phonemes[letter] + ":".repeat(run.length - 1);
      stressed = true;
    }
    previous = letter;
  }
  return sounds;
}

function synthesize(text) {
  const input = text.toLowerCase().split(/([,.?!])/u).map((group) => {
    if (/^[,.?!]$/u.test(group)) return group + " ";
    const words = group.trim().split(/\s+/u).filter(Boolean);
    return words.length ? `[[${words.map(pronounce).join(" ")}]]` : "";
  }).join("");
  const audio = [];
  const heard = [];
  voice.synthesize(input, (samples, events) => {
    for (const event of events) {
      if (event.type === "phoneme" && event.id) heard.push(event.id.replace(/[ˈˌː]/gu, ""));
    }
    // Copy each buffer before the synthesizer reuses it.
    if (!samples.length) return;
    const chunk = Buffer.alloc(samples.length * 2);
    for (let i = 0; i < samples.length; i++) chunk.writeInt16LE(samples[i], 2 * i);
    audio.push(chunk);
  });
  if (audio.length === 0) throw new Error(`Пустой звук для «${text}»`);
  const expected = (text.toLowerCase().match(/[а-яё]+/gu) ?? []).flatMap((word) =>
    word.match(/(.)\1*/gu).flatMap((run) =>
      Array(vowels.has(run[0]) ? 1 : run.length).fill(ipaExceptions[run[0]] ?? phonemes[run[0]]),
    ),
  );
  if (heard.join(" ") !== expected.join(" ")) {
    throw new Error(`Звуковой состав «${text}»: ожидалось ${expected.join(" ")}, получено ${heard.join(" ")}`);
  }
  return Buffer.concat(audio);
}

function wave(pcm) {
  const header = Buffer.alloc(44);
  header.write("RIFF", 0);
  header.writeUInt32LE(36 + pcm.length, 4);
  header.write("WAVEfmt ", 8);
  header.writeUInt32LE(16, 16);
  header.writeUInt16LE(1, 20);
  header.writeUInt16LE(1, 22);
  header.writeUInt32LE(sampleRate, 24);
  header.writeUInt32LE(sampleRate * 2, 28);
  header.writeUInt16LE(2, 32);
  header.writeUInt16LE(16, 34);
  header.write("data", 36);
  header.writeUInt32LE(pcm.length, 40);
  return Buffer.concat([header, pcm]);
}

await mkdir(output, { recursive: true });
for (const [, filename, transcript] of clips) {
  const lines = [...transcript.matchAll(/\*\*`([^`]+)`\*\*/gu)].map((match) => match[1]);
  const pcm = Buffer.concat(lines.flatMap((line, index) => {
    const speech = synthesize(line);
    return index === 0 ? [speech] : [Buffer.alloc(sampleRate), speech];
  }));
  await writeFile(new URL(encodeURIComponent(filename), output), wave(pcm));
  console.log(`${filename}: ${(pcm.length / (2 * sampleRate)).toFixed(2)} с`);
}
