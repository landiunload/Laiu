import Laiu

open Laiu

private def cells (line : String) : List String :=
  (line.splitOn "|").drop 1 |>.dropLast |>.map (fun cell => cell.trimAscii.toString)

private def codeWord (cell : String) : Option String :=
  match cell.splitOn "`" with
  | ["", word, ""] => some word
  | _ => none

private def dictionaryRow (line : String) : Option (String × String) := do
  let first :: second :: _ := cells line | none
  if let some digit := first.toNat? then
    return (← codeWord second, s!"число {digit}")
  else
    return (← codeWord first, second)

private def require (holds : Bool) (message : String) : IO Unit :=
  unless holds do throw (IO.userError message)

private def checkDictionary (markdown : String) : IO Unit := do
  let entries := (markdown.splitOn "\n").filterMap dictionaryRow
  if entries != Lexicon.entries then
    let mismatch := (List.zip entries Lexicon.entries).find? (fun (left, right) => left != right)
    throw (IO.userError s!"Лексика.md: {entries.length} строк, в Lean {Lexicon.entries.length}. Первое расхождение: {repr mismatch}")
  IO.println s!"Лексика: {entries.length} записей совпадают с Lean, включая значения."
  IO.println s!"Словарь и продуктивные формы: {Morphology.reservedForms.eraseDups.length} различных форм."

private def tokens (text : String) : List String :=
  (text.splitOn " ").filter (!·.isEmpty)

private def speechGroups (text : String) : List (List String) :=
  (text.toList.splitOnP (fun c => ['.', ',', '?', '!'].contains c)).map (tokens ∘ String.ofList)

private def spokenTokens (text : String) : List String := (speechGroups text).flatten

private def sharedVowelBoundaries (words : List String) : List (String × String) :=
  (words.zip words.tail).filter (fun (a, b) => Phonology.hasSameVowelBoundary a b)

private def formatBoundaries (boundaries : List (String × String)) : String :=
  String.intercalate ", " (boundaries.map fun (a, b) => s!"{a} | {b}")

#guard sharedVowelBoundaries ["а", "ки", "ииу", "эм"] == [("ки", "ииу")]
#guard (sharedVowelBoundaries ["ииу", "а", "ки", "эм"]).isEmpty

private def checkNumerals (markdown : String) : IO Unit := do
  let rows := (markdown.splitOn "\n").filterMap fun line => do
    let first :: spelling :: _ := cells line | none
    let number ← (first.replace " " "").toNat?
    return (number, ← codeWord spelling)
  require (!rows.isEmpty) "В Числа.md не найдены примеры с числовыми значениями."
  for (value, spelling) in rows do
    let written := tokens spelling
    require (NumberWords.parse written == some value && NumberWords.spell value == written)
      s!"Числа.md: «{spelling}» не соответствует {value}."
  IO.println s!"Числа: {rows.length} примеров из справочника совпадают с формальной записью."

private def cyrillicLetters (text : String) : Nat :=
  (text.toLower.toList.filter (fun c => ('а' ≤ c && c ≤ 'я') || c == 'ё')).length

private def comparison (left right : Nat) : String := s!"{left} / {right}"

private def codeSpans : List String → List String
  | _ :: code :: rest => code :: codeSpans rest
  | _ => []

private def checkFrameExamples (markdown : String) : IO Unit := do
  let examples := (markdown.splitOn "\n").flatMap (fun line => codeSpans (line.splitOn "`"))
  let framed := examples.filterMap fun exampleText =>
    let phrase := spokenTokens exampleText
    if phrase.length > 1 && (phrase.contains "тэ" || phrase.contains "эт") && !phrase.contains "…" then
      some (exampleText, phrase)
    else none
  require (!framed.isEmpty) "В проверке синтаксиса не найдены фразы с рамками."
  for (sample, phrase) in framed do
    require (Frames.balances phrase) s!"Разорванная рамка тэ … эт: «{sample}»."
  IO.println s!"Рамки: {framed.length} примеров с тэ … эт имеют ожидаемые границы."

private def checkListeningExamples (markdown : String) : IO Unit := do
  let rows := (markdown.splitOn "\n").filterMap fun line => do
    let [left, right, expected] := cells line | none
    return (← codeWord left, ← codeWord right, expected)
  require (!rows.isEmpty) "В фонологии не найдены пары для проверки звучания."
  let known := Morphology.reservedForms
  for (left, right, expected) in rows do
    let first := tokens left
    let second := tokens right
    require ((first ++ second).all known.contains) s!"Неизвестное слово в пробе «{left} / {right}»."
    let distinguishable := Phonology.withoutVowelLength (String.join first) !=
      Phonology.withoutVowelLength (String.join second)
    let actual := if distinguishable then "сохраняется" else "теряется"
    require (expected == actual) s!"Проба «{left} / {right}»: различие {actual}."
  IO.println s!"Звучание: {rows.length} пар проверены при потере долготы и границ слов."

private def checkSpatialAnswers (markdown : String) : IO Unit := do
  let rows := (markdown.splitOn "\n").filterMap fun line => do
    let [question, full, short] := cells line | none
    return (← codeWord question, ← codeWord full, ← codeWord short)
  require (!rows.isEmpty) "Не найдены короткие ответы на пространственные вопросы."
  for (question, full, short) in rows do
    let context := SpatialAnswers.readQuestion (spokenTokens question)
    let fullWords := tokens full
    let shortWords := tokens short
    require (SpatialAnswers.recover context shortWords == some fullWords)
      s!"Ответ «{short}» на «{question}» не даёт полной реплики «{full}»."
    require (SpatialAnswers.compact context fullWords == shortWords && shortWords.length < fullWords.length)
      s!"Сокращение «{full}» до «{short}» не подтверждено."
  IO.println s!"Короткие ответы: {rows.length} примера восстановлены пословно."

private def checkGardenDialogue (markdown : String) : IO Unit := do
  let turns := ((markdown.splitOn "\n").map cells).filter fun row =>
    row.head? == some "А" || row.head? == some "Б"
  require (!turns.isEmpty) "В разговоре в саду не найдены реплики."
  let known := Morphology.reservedForms
  let mut boundaries := []
  let mut wordCount := 0
  for row in turns do
    let [_, written, _] := row | throw (IO.userError s!"Неверный формат реплики: {row}.")
    let ["", text, ""] := written.splitOn "**" | throw (IO.userError s!"Не читается реплика: {written}.")
    let groups := speechGroups text
    let phrase := groups.flatten
    wordCount := wordCount + phrase.length
    for word in phrase do
      require (known.contains word) s!"Реплика «{text}»: неизвестное слово «{word}»."
    require (Frames.balances phrase) s!"Реплика «{text}»: нарушены границы рамки."
    boundaries := boundaries ++ groups.flatMap sharedVowelBoundaries
  IO.println s!"Разговор в саду: {turns.length} живых реплик сверены со словарём и рамками."
  IO.println s!"Слов в диалоге: {wordCount}."
  IO.println s!"Стыки одинаковых гласных в диалоге ({boundaries.length}): {formatBoundaries boundaries}."

private def checkBenchmarks (markdown : String) : IO Unit := do
  let table := (markdown.splitOn "\n").map cells
  let rows := table.filterMap fun row => do
    let [laiu, russian, letters, words] := row | none
    return (← codeWord laiu, russian, letters, words)
  require (!rows.isEmpty) "В формальном анализе не найдены фразы для сравнения."
  for (laiu, russian, letters, words) in rows do
    let expectedLetters := comparison (cyrillicLetters laiu) (cyrillicLetters russian)
    let expectedWords := comparison (tokens laiu).length (tokens russian).length
    require (letters == expectedLetters && words == expectedWords)
      s!"Фраза «{laiu}»: ожидается {expectedLetters} букв и {expectedWords} слов."
    require (Frames.balances (tokens laiu)) s!"Разорванная рамка тэ … эт: «{laiu}»."
    for token in tokens laiu do
      require (Morphology.reservedForms.contains token) s!"Фраза «{laiu}»: неизвестное слово «{token}»."
  let left := rows.map (fun (laiu, _, _, _) => laiu)
  let right := rows.map (fun (_, russian, _, _) => russian)
  let totalLetters := comparison (left.map cyrillicLetters).sum (right.map cyrillicLetters).sum
  let totalWords := comparison (left.flatMap tokens).length (right.flatMap tokens).length
  let totals := table.filter fun row => row.head? == some "Всего"
  require (totals == [["Всего", toString rows.length, totalLetters, totalWords]])
    s!"Строка «Всего»: ожидается {rows.length}, {totalLetters} букв, {totalWords} слов."
  let laiuWords := left.flatMap tokens
  let boundaries := left.flatMap (sharedVowelBoundaries ∘ tokens)
  IO.println s!"Краткость: {rows.length} фраз, буквы {totalLetters}, слова {totalWords} (Laiu / русский)."
  IO.println s!"Laiu: {(laiuWords.map Phonology.glyphBases).sum} основных знаков письма, {(laiuWords.map Phonology.vowelBeats).sum} гласных долей."
  let syllables := (laiuWords.map Phonology.syllableCount).sum
  let closed := (laiuWords.map Phonology.closedSyllableCount).sum
  IO.println s!"Слоги Laiu: {syllables - closed} открытых и {closed} закрытых."
  IO.println s!"Стыки одинаковых гласных ({boundaries.length}): {formatBoundaries boundaries}."

private def showLengthContrasts : IO Unit := do
  let forms := Lexicon.forms Lexicon.entries
  let profiles := forms.map Phonology.withoutVowelLength
  let groups := profiles.eraseDups.filterMap fun profile =>
    let words := (forms.zip profiles).filterMap fun (word, signature) =>
      if signature == profile then some word else none
    if words.length > 1 then some words else none
  IO.println s!"Словарные ряды, различимые только по долготе: {groups.length}."
  for group in groups do
    IO.println (String.intercalate " / " group)

def main (args : List String) : IO Unit := do
  let vault : System.FilePath ← match args with
    | [] => pure ".."
    | [path] => pure path
    | _ => throw (IO.userError "Укажи один путь к хранилищу Obsidian.")
  checkDictionary (← IO.FS.readFile (vault / "Лексика.md"))
  checkNumerals (← IO.FS.readFile (vault / "Числа.md"))
  checkFrameExamples (← IO.FS.readFile (vault / "Проверка синтаксиса.md"))
  checkListeningExamples (← IO.FS.readFile (vault / "Фонология.md"))
  checkSpatialAnswers (← IO.FS.readFile (vault / "Вопросительные слова.md"))
  checkGardenDialogue (← IO.FS.readFile (vault / "Разговор в саду.md"))
  checkBenchmarks (← IO.FS.readFile (vault / "Формальный анализ.md"))
  showLengthContrasts
