// Rebuild with @echogarden/espeak-ng-emscripten 0.3.5.
// Pass the absolute path to espeak-ng.js if installed outside the repository.
import { createHash } from "node:crypto";
import { copyFile, mkdir, readFile, writeFile } from "node:fs/promises";
import { resolve, sep } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const output = new URL("../Звучание/", import.meta.url);
const notes = (await readFile(new URL("../Фонология.md", import.meta.url), "utf8")).replaceAll("\r\n", "\n");
const clips = [...notes.matchAll(/!\[\[Звучание\/([^\]\n]+\.wav)\]\]\n((?:> \*\*`[^`\n]+`\*\*[^\n]*\n)+)/gu)];
if (clips.length === 0) throw new Error("В фонологии нет размеченных аудиопримеров");
const transcriptLines = (transcript) => [...transcript.matchAll(/\*\*`([^`]+)`\*\*/gu)].map((match) => match[1]);
const pairs = [...notes.matchAll(/^\| `([^`\n]+)` \| `([^`\n]+)` \| (?:сохраняется|теряется) \|$/gmu)]
  .map(([, a, b], index) => ({ id: String(index + 1).padStart(2, "0"), phrases: [a, b] }));
const ratingSection = notes.split("\n### Оценка звучания\n")[1]?.split("\n> [!note]", 1)[0] ?? "";
const preference = [...ratingSection.matchAll(/^\| ([a-z]+) \| ([^|\n]+) \| `([^`\n]+)` \| `([^`\n]+)` \|$/gmu)]
  .map(([, id, title, first, second]) => ({ id, title, phrases: [first, second] }));
if (pairs.length === 0 || preference.length === 0) throw new Error("В фонологии недостаёт пар для пробы");
if (new Set(preference.map(({ id }) => id)).size !== preference.length ||
    preference.some(({ phrases }) => phrases[0] === phrases[1])) {
  throw new Error("У каждой пары для оценки должен быть свой код и две разные фразы");
}
const recordings = new Map();
for (const { id, phrases } of pairs) {
  phrases.forEach((phrase, side) => {
    if (!recordings.has(phrase)) recordings.set(phrase, `pair-${id}-${"ab"[side]}.wav`);
  });
}
for (const { id, phrases } of preference) {
  phrases.forEach((phrase, side) => {
    if (!recordings.has(phrase)) recordings.set(phrase, `${id}-${"ab"[side]}.wav`);
  });
}

const [mode, folder] = process.argv.slice(2);
if (mode === "--list") {
  for (const [phrase, file] of recordings) console.log(`${file}\t${phrase}`);
  process.exit(0);
}
const isHuman = mode === "--recordings";
let destination = output;
let makeVoice;
let voice;
if (isHuman) {
  if (!folder) throw new Error("Укажите отдельную папку со сделанными WAV-записями");
  destination = pathToFileURL(resolve(folder) + sep);
  if (resolve(fileURLToPath(destination)).toLowerCase() === resolve(fileURLToPath(output)).toLowerCase()) {
    throw new Error("Выберите отдельную папку для живых записей, чтобы сохранить синтетическую пробу");
  }
} else {
  const engine = mode ? pathToFileURL(resolve(mode)).href : "@echogarden/espeak-ng-emscripten";
  const { default: init } = await import(engine);
  makeVoice = async () => {
    const module = await init();
    const worker = new module.eSpeakNGWorker();
    worker.set_voice("es");
    worker.set_rate(145);
    worker.set_pitch(53);
    return worker;
  };
  voice = await makeVoice();
}

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

async function writeExamples(examples) {
  for (const [, filename, transcript] of examples) {
    const pcm = Buffer.concat(transcriptLines(transcript).flatMap((line, index) => {
      const speech = synthesize(line);
      return index === 0 ? [speech] : [Buffer.alloc(sampleRate), speech];
    }));
    await writeFile(new URL(encodeURIComponent(filename), output), wave(pcm));
    console.log(`${filename}: ${(pcm.length / (2 * sampleRate)).toFixed(2)} с`);
  }
}

if (!isHuman) await mkdir(output, { recursive: true });
const audio = {};
const fingerprint = createHash("sha256");
for (const [phrase, filename] of recordings) {
  const wav = isHuman ? await readFile(new URL(filename, destination)) : wave(synthesize(phrase));
  if (wav.length <= 44 || wav.toString("ascii", 0, 4) !== "RIFF" || wav.toString("ascii", 8, 12) !== "WAVE") {
    throw new Error(`Нужна непустая WAV-запись: ${filename}`);
  }
  fingerprint.update(phrase).update(wav);
  audio[phrase] = `data:audio/wav;base64,${wav.toString("base64")}`;
}
const data = { source: isHuman ? "human" : "synthetic", audioSet: fingerprint.digest("hex"), pairs, preference, audio };
await writeFile(new URL("practices.js", destination), `window.laiuListening = ${JSON.stringify(data)};\n`);
if (isHuman) {
  await Promise.all(["Проба.html", "recording.js"].map(file =>
    copyFile(new URL(file, output), new URL(file, destination))));
}
if (!isHuman) {
  // Keep synthesis state separate so changes to either group leave the other group's recordings intact.
  voice = await makeVoice();
  await writeExamples(clips);
}
console.log(`Проба на слух: ${pairs.length} пар, ${recordings.size} записей.`);
