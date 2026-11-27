import Laiu

open Laiu
open Laiu.Phonology (sharedVowelBoundaries)

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

private def checkSpeechGroup (source : String) (words : List String) : IO Unit := do
  if let some window := Phonology.unwantedResemblance words then
    let phrase := String.intercalate " " words
    let exampleText := String.intercalate " " window
    throw (IO.userError s!"{source}: нежелательное созвучие «{exampleText}» в «{phrase}».")

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

private def checkSoundResemblances (vault : System.FilePath) : IO Unit := do
  let known := Morphology.reservedForms.eraseDups
  for word in known do
    checkSpeechGroup "Словарь и производные" [word]
  let mut count := 0
  for file in ← vault.readDir do
    if file.path.extension == some "md" then
      let markdown ← IO.FS.readFile file.path
      for line in markdown.splitOn "\n" do
        for exampleText in codeSpans (line.splitOn "`") do
          let groups := (speechGroups exampleText.toLower).filter (!·.isEmpty)
          if !groups.isEmpty && groups.flatten.all Phonology.hasSyllableShape then
            for group in groups do
              checkSpeechGroup file.fileName group
            count := count + 1
  require (count > 0) "Не найдены примеры для проверки созвучий."
  IO.println s!"Созвучия: проверены {known.length} слов и производных и {count} примеров в заметках."

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

private def checkSoundRatings (markdown : String) : IO Unit := do
  let sectionLines := (markdown.splitOn "\n").dropWhile (fun line => line.trimAscii.toString != "### Оценка звучания")
  let rows := (sectionLines.tail.takeWhile (!·.startsWith ">")).filterMap fun line => do
    let [code, _, first, second] := cells line | none
    return (code, ← codeWord first, ← codeWord second)
  require (rows.map (fun (code, _, _) => code) == ["order", "voice", "object", "invitation"])
    "Нужны четыре пары для оценки звучания."
  for (code, first, second) in rows do
    let before := spokenTokens first
    let after := spokenTokens second
    require (before != after && (before ++ after).all Morphology.reservedForms.contains)
      s!"Фразы для оценки должны различаться и использовать слова Laiu: «{first} / {second}»."
    let valid := match code with
      | "order" =>
        let received := TemporalAdverbs.parse before
        received.isSome && received == TemporalAdverbs.parse after
      | "voice" =>
        match Voice.parse before, Voice.parse after with
        | some (.active agent patient predicate), some passive =>
          passive == (Voice.Clause.active agent patient predicate).toPassive
        | _, _ => false
      | "object" =>
        let received := Voice.parse before
        received.isSome && received == Voice.parse after &&
          !before.contains Voice.patientMarker && after.contains Voice.patientMarker
      | "invitation" =>
        match Directives.parse none before, Directives.parse none after with
        | some base, some inclusive =>
          base.person == .we && inclusive == { base with person := .inclusive }
        | _, _ => false
      | _ => false
    require valid s!"Фразы для оценки «{first} / {second}» не соответствуют коду «{code}»."
  IO.println s!"Звучание: {rows.length} пары для оценки сверены с грамматическими моделями."

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

private def checkTransferAnswers (markdown : String) : IO Unit := do
  let sectionLines := (markdown.splitOn "\n").dropWhile (fun line =>
    line.trimAscii.toString != "### Короткие ответы о передаче")
  let rows := (sectionLines.tail.takeWhile (!·.startsWith "#")).filterMap fun line => do
    let [question, full, short, _] := cells line | none
    return (← codeWord question, ← codeWord full, ← codeWord short)
  require (!rows.isEmpty) "Не найдены короткие ответы о передаче."
  let mut removed := 0
  for (question, full, short) in rows do
    let some context := TransferAnswers.readQuestion (spokenTokens question) |
      throw (IO.userError s!"Не удалось прочитать вопрос о передаче «{question}».")
    let shortWords := spokenTokens short
    let fullWords := spokenTokens full
    require (TransferAnswers.recover (some context) shortWords == some fullWords &&
      TransferAnswers.recover (some context) (context.role.marker :: shortWords) == some fullWords &&
      TransferAnswers.compact (some context) fullWords == shortWords &&
      shortWords.length == 1)
      s!"Ответ «{short}» на «{question}» не восстанавливает «{full}»."
    removed := removed + (Phonology.sharedVowelBoundaries fullWords).length
  IO.println s!"Передача: восстановлено коротких ответов — {rows.length}, убрано стыков — {removed}."

private def checkPolarityAnswers (markdown : String) : IO Unit := do
  let rows := (markdown.splitOn "\n").filterMap fun line => do
    let [question, short, full, _] := cells line | none
    return (← codeWord question, ← codeWord short, ← codeWord full)
  require (!rows.isEmpty) "Не найдены примеры ответов ла и ли."
  for (question, short, full) in rows do
    let context := PolarityAnswers.readContext (spokenTokens question)
    let fullWords := tokens full
    let some clause := Syntax.parse fullWords |
      throw (IO.userError s!"Не удалось разобрать полную реплику «{full}».")
    let reply := tokens short
    require (PolarityAnswers.recover context reply == some clause &&
      PolarityAnswers.compact context clause == reply && reply.length < fullWords.length)
      s!"Ответ «{short}» на «{question}» не даёт полной реплики «{full}»."
  IO.println s!"Ответы ла и ли: {rows.length} примеров восстановлены пословно."

private def checkTemporalAdverbs (markdown : String) : IO Unit := do
  let rows := (markdown.splitOn "\n").filterMap fun line => do
    let [last, first, counts, preferred] := cells line | none
    return (← codeWord last, ← codeWord first, counts, preferred)
  require (!rows.isEmpty) "Не найдены примеры порядка наречий времени."
  for (last, first, counts, preferred) in rows do
    let atEnd := spokenTokens last
    let atStart := spokenTokens first
    let some timed := TemporalAdverbs.parse atEnd |
      throw (IO.userError s!"Не удалось разобрать наречие в «{last}».")
    require (timed.resolvedTime .present).isSome
      s!"Частица и наречие задают разные времена в «{last}»."
    require (TemporalAdverbs.parse atStart == some timed &&
      TemporalAdverbs.render timed .final == atEnd && TemporalAdverbs.render timed .initial == atStart)
      s!"«{last}» и «{first}» должны быть двумя порядками одной фразы."
    require (counts == comparison (TemporalAdverbs.boundaryCount atEnd) (TemporalAdverbs.boundaryCount atStart))
      s!"Неверное число стыков у «{last}» и «{first}»."
    let actual := match TemporalAdverbs.smootherPosition timed with
      | .initial => "в начале"
      | .final => "в конце"
    require (preferred == actual) s!"Для «{last}» при учёте стыков наречие ставится {actual}."
  IO.println s!"Пары с наречиями времени ({rows.length}) сверены с разбором и стыками гласных."

private def checkTimeCompaction (markdown : String) : IO Unit := do
  let sectionLines := (markdown.splitOn "\n").dropWhile (fun line =>
    line.trimAscii.toString != "### Когда частицу можно опустить")
  let body := sectionLines.tail.takeWhile (!·.startsWith "#")
  let rows := body.filterMap fun line => do
    let [original, short, time] := cells line | none
    return (← codeWord original, ← codeWord short, time)
  require (!rows.isEmpty) "Не найдены примеры сокращения частиц времени."
  for (original, short, time) in rows do
    let fullWords := spokenTokens original
    let some utterance := TemporalAdverbs.parse fullWords |
      throw (IO.userError s!"Не удалось разобрать «{original}».")
    let some actual := utterance.resolvedTime .present |
      throw (IO.userError s!"Частица и наречие задают разные времена в «{original}».")
    let actualName := match actual with
      | .past => "прошлое"
      | .present => "настоящее"
      | .future => "будущее"
    require (time == actualName) s!"В «{original}» время должно быть «{actualName}»."
    let position : TemporalAdverbs.Position :=
      if TemporalAdverbs.render utterance .initial == fullWords then .initial else .final
    let some compact := TemporalAdverbs.compact utterance .present |
      throw (IO.userError s!"Не удалось сократить «{original}».")
    require (TemporalAdverbs.render compact position == spokenTokens short)
      s!"Для «{original}» ожидается другая форма."
  IO.println s!"Время с наречиями проверено на примерах ({rows.length})."

private def checkTimeClarification (markdown : String) : IO Unit := do
  let sectionLines := (markdown.splitOn "\n").dropWhile (fun line =>
    line.trimAscii.toString != "### Если долготу трудно расслышать")
  let rows := (sectionLines.tail.takeWhile (!·.startsWith "#")).filterMap fun line => do
    let [bare, compact, clear] := cells line | none
    return (← codeWord bare, ← codeWord compact, ← codeWord clear)
  let topics : List TemporalAdverbs.Adverb := [.soon, .recently]
  require (rows.length == topics.length) "Нужны тройки со «скоро» и «недавно»."
  let sound := fun words => Phonology.withoutVowelLength (String.join words)
  for ((bare, compact, clear), topic) in rows.zip topics do
    let bareWords := spokenTokens bare
    let shortWords := spokenTokens compact
    let clearWords := spokenTokens clear
    let some explicit := Particles.parseUtterance bareWords |
      throw (IO.userError s!"Не удалось разобрать короткую реплику «{bare}».")
    let some marked := TemporalAdverbs.parse clearWords |
      throw (IO.userError s!"Не удалось разобрать уточнение «{clear}».")
    let some short := TemporalAdverbs.compact marked .present |
      throw (IO.userError s!"Частица и наречие расходятся в «{clear}».")
    let initial := TemporalAdverbs.render short .initial
    require (marked.adverb == topic && marked.body == explicit &&
      TemporalAdverbs.render marked .final == clearWords &&
      TemporalAdverbs.render short .final == shortWords && shortWords.length + 1 == clearWords.length)
      s!"«{clear}» должно добавлять только совпадающую частицу к «{compact}»."
    let junctions := TemporalAdverbs.boundaryCount
    require (junctions shortWords < junctions initial && junctions clearWords == junctions shortWords)
      s!"«{clear}» должно сохранять число стыков из «{compact}»."
    require (sound bareWords == sound shortWords && sound bareWords != sound clearWords)
      s!"Уточнение «{clear}» должно восстанавливать различие с «{bare}»."
  IO.println s!"Уточнение близкого времени: {rows.length} примера различимы без долготы."

private def checkDistinctWordSound (word : String) : IO Unit := do
  let key := Phonology.withoutVowelLength word
  let resembling := Morphology.reservedForms.filter (fun form => Phonology.withoutVowelLength form == key)
  require (resembling == [word]) s!"Созвучная форма для «{word}»: {resembling}."

private def personalPronouns : List Syntax.Person := [.speaker, .listener, .man, .woman, .neutral,
  .we, .inclusive, .exclusive, .youPlural, .polite, .men, .women, .neutralPlural]

private def movementPhrases (times : List Syntax.Time) : List Syntax.Phrase :=
  let places : List Syntax.Place := [.garden, .house, .tree]
  let relations : List Syntax.Relation := [.location, .direction, .source]
  let settings := none :: relations.flatMap fun relation => places.map fun place => some (relation, place)
  personalPronouns.flatMap fun person =>
  [false, true].flatMap fun negative =>
  [Syntax.Phase.neutral, .starts, .stops].flatMap fun phase =>
  [Syntax.Travel.go, .returnTo, .move].flatMap fun travel =>
  times.flatMap fun time =>
  [false, true].flatMap fun result =>
  settings.map fun spatial => ⟨person, negative, phase, travel, time, result, spatial⟩

private def checkMovementProfiles : IO Unit := do
  let phrases := movementPhrases [.implicit, .past, .present, .future]
  let mut profiles : Std.HashMap String Syntax.Phrase := {}
  for clause in phrases do
    let spoken := Phonology.withoutVowelLength (String.join (Syntax.render clause))
    if let some earlier := profiles[spoken]? then
      let samePersonSound := Phonology.withoutVowelLength earlier.person.word ==
        Phonology.withoutVowelLength clause.person.word
      let samePredicate := Syntax.compact { earlier with person := .speaker } ==
        Syntax.compact { clause with person := .speaker }
      require (samePersonSound && samePredicate)
        s!"Сливаются фразы движения «{String.intercalate " " (Syntax.render earlier)}» и «{String.intercalate " " (Syntax.render clause)}»."
    else
      profiles := profiles.insert spoken clause
  for marker in Syntax.Phase.stops.words do
    checkDistinctWordSound marker
  IO.println s!"Проверка слитной речи охватывает {phrases.length} фраз движения и {profiles.size} звуковых профилей."

private def checkTimeClarificationProfiles : IO Unit := do
  let clauses := movementPhrases [.past, .future]
  let questions : List (Option Particles.Question) :=
    [none, some .neutral, some (.biased .confirm), some (.biased .deny)]
  let sound := fun words => Phonology.withoutVowelLength (String.join words)
  let junctions := TemporalAdverbs.boundaryCount
  let mut repairs := 0
  for clause in clauses do
    let adverb : TemporalAdverbs.Adverb := if clause.time == .past then .recently else .soon
    for question in questions do
      let marked : TemporalAdverbs.TimedUtterance := ⟨⟨clause, question⟩, adverb⟩
      let compact := marked.withoutTimeParticle
      let bare := Particles.renderUtterance marked.body
      let clear := TemporalAdverbs.render marked .final
      let short := TemporalAdverbs.render compact .final
      require (TemporalAdverbs.compact marked .present == some compact && junctions clear ≤ junctions short &&
        sound clear != sound bare)
        s!"Не удалось уточнить время в «{String.intercalate " " short}»."
      if sound short == sound bare && junctions short < junctions (TemporalAdverbs.render compact .initial) then
        repairs := repairs + 1
  IO.println s!"Уточнение времени проверено в {clauses.length * questions.length} случаях; в {repairs} короткая форма сливается, а перенос добавляет стык."

private def checkVoiceExamples (markdown : String) : IO Unit := do
  let rows := (markdown.splitOn "\n").filterMap fun line => do
    let [active, passive, anonymous] := (cells line).map (fun cell => (cell.splitOn "`")[1]?) | none
    return (← active, ← passive, ← anonymous)
  require (!rows.isEmpty) "В заметке о залогах нет примеров с тремя вариантами."
  for (active, passive, anonymous) in rows do
    let some (.active agent patient predicate) := Voice.parse (spokenTokens active) |
      throw (IO.userError s!"Не удалось разобрать актив «{active}».")
    let activeClause : Voice.Clause := .active agent patient predicate
    require (Voice.parse (spokenTokens passive) == some activeClause.toPassive &&
      Voice.parse (spokenTokens anonymous) == some (.passive patient none predicate))
      s!"В формах залога расходятся роли или действие для «{active}»."
  IO.println s!"Сверены примеры залога ({rows.length}): актив и две формы пассива."

private def checkVoiceProfiles : IO Unit := do
  checkDistinctWordSound Voice.passiveMarker
  checkDistinctWordSound Voice.agentMarker
  checkDistinctWordSound Voice.patientMarker
  checkDistinctWordSound Syntax.Person.inclusive.word
  checkDistinctWordSound Syntax.Person.exclusive.word
  let participants := personalPronouns.map Syntax.Person.word ++ ["там", "лап"]
  let clauses : List Voice.Clause :=
    [Voice.Verb.see, .build, .love].flatMap fun verb =>
    [false, true].flatMap fun negative =>
    [Syntax.Phase.neutral, .starts, .stops].flatMap fun phase =>
    [Syntax.Time.implicit, .past, .present, .future].flatMap fun time =>
    [false, true].flatMap fun result =>
    ([none, some (.source, .house)] : List (Option (Syntax.Relation × Syntax.Place))).flatMap fun spatial =>
    participants.flatMap fun patient =>
      let predicate : Voice.Predicate := ⟨verb, negative, phase, time, result, spatial⟩
      .passive patient none predicate :: (participants.flatMap fun agent =>
        let active : Voice.Clause := .active agent patient predicate
        [active, active.toPassive])
  let mut profiles : Std.HashMap String (Bool × (Bool × Voice.Reading)) := {}
  let mut ambiguous : Std.HashSet String := {}
  let mut total := 0
  for clause in clauses do
    let voice := match clause with
      | .active .. => false
      | .passive .. => true
    let reading := clause.reading
    let time := if reading.predicate.time == .present then .implicit else reading.predicate.time
    let key := (voice, { reading with
      agent := reading.agent.map Phonology.withoutVowelLength
      patient := Phonology.withoutVowelLength reading.patient
      predicate := { reading.predicate with time } })
    for marked in (if voice then [false] else [false, true]) do
      let words := Voice.render clause marked
      unless Voice.parse words == some clause do
        throw (IO.userError s!"Разбор залога не восстанавливает «{String.intercalate " " words}».")
      let spoken := Phonology.withoutVowelLength (String.join words)
      let clear := voice || marked
      if let some (earlierClear, earlier) := profiles[spoken]? then
        if (key != earlier && (earlierClear || clear)) || (clear && ambiguous.contains spoken) then
          throw (IO.userError s!"В слитной речи меняются залог, роли или действие в «{String.intercalate " " words}».")
        if key != earlier then
          ambiguous := ambiguous.insert spoken
        if clear then
          profiles := profiles.insert spoken (true, key)
      else
        profiles := profiles.insert spoken (clear, key)
      total := total + 1
  IO.println s!"Залог: {total} фраз и {profiles.size} звуковых профилей. Совпадения только в кратком активе ({ambiguous.size})."

private def checkDeixis (markdown : String) : IO Unit := do
  let grammarRows := (markdown.splitOn "\n").map cells
  let table := grammarRows.dropWhile (· != ["На что указываем", "Рядом", "Вдали"])
  let rows := table.drop 2 |>.takeWhile (!·.isEmpty)
  let roles : List (String × Deixis.Use) :=
    [("Один предмет", .one), ("Несколько предметов", .many), ("Место", .place)]
  require (rows.length == roles.length) "Указательная таблица должна содержать три строки."
  for (row, (expectedLabel, role)) in rows.zip roles do
    let [label, nearby, distant] := row |
      throw (IO.userError "В указательной таблице нужны колонки «Рядом» и «Вдали».")
    require (label == expectedLabel) s!"В указательной таблице ожидается строка «{expectedLabel}»."
    for (cell, distance) in [(nearby, Deixis.Distance.near), (distant, .far)] do
      let some spelling := (cell.splitOn "`")[1]? |
        throw (IO.userError s!"Нет указательной формы в «{cell}».")
      require (Deixis.read spelling == some (distance, role))
        s!"В строке «{label}» ожидается форма «{Deixis.word distance role}»."
      checkDistinctWordSound spelling
  IO.println "Указательные формы: расстояние и назначение сверены с грамматикой."

private def checkConditionals (markdown : String) : IO Unit := do
  let rows := (markdown.splitOn "\n").filterMap fun line => do
    let [connector, kind, exampleText, _] := cells line | none
    return (← codeWord connector, kind, ← codeWord exampleText)
  let [(plain, _, first), (irrealis, _, second)] := rows |
    throw (IO.userError "Нужны две сопоставимые реплики с условием.")
  require (Logic.readConditional plain == some .openCondition &&
    Logic.readConditional irrealis == some .counterfactual)
    "Союзы условия расходятся со словарём Lean."
  for (marker, kind, utterance) in rows do
    checkDistinctWordSound marker
    let some connector := Logic.readConditional marker |
      throw (IO.userError s!"Неизвестный условный союз «{marker}».")
    let [opening, result] := (speechGroups utterance).filter (!·.isEmpty) |
      throw (IO.userError s!"Ожидаются условие и следствие в «{utterance}».")
    let expected := match connector with
      | .openCondition => "открытое"
      | .counterfactual => "контрфактическое"
    require (opening.head? == some marker && !opening.tail.isEmpty && !result.isEmpty &&
      expected == kind)
      s!"Тип условия или союз в «{utterance}» указан неверно."
  let content (utterance : String) := match speechGroups utterance with
    | opening :: rest => opening.tail :: rest
    | [] => []
  require (content first == content second)
    "Примеры должны различаться только условным союзом."
  IO.println "Условные союзы: реплики сверены с моделью и словарём."

private def checkChoices (markdown : String) : IO Unit := do
  let rows := (markdown.splitOn "\n").map cells
  let inclusive := Logic.Connector.any
  let exclusive := Logic.Connector.one
  require (rows.contains ["Сколько мест посетили", s!"Подходит для `{inclusive.word}`",
    s!"Подходит для `{exclusive.word}`"])
    "Заголовок таблицы выбора расходится с союзами в Lean."
  for connector in [inclusive, exclusive] do
    checkDistinctWordSound connector.word
  let observations := rows.filterMap fun row => do
    let [count, anyResult, oneResult] := row | none
    return (← count.toNat?, anyResult, oneResult)
  require (observations.map (fun (count, _, _) => count) == [0, 1, 2])
    "В таблице выбора должны быть случаи с нулём, одним и двумя посещёнными местами."
  for (count, anyResult, oneResult) in observations do
    let choices := List.replicate count true ++ List.replicate (2 - count) false
    let expected (connector : Logic.Connector) := if connector.eval choices then "да" else "нет"
    require (anyResult == expected inclusive && oneResult == expected exclusive)
      s!"Ошибка в таблице союзов при числе выбранных мест {count}."
  IO.println "Союзы выбора: таблица маршрутов сверена с логикой."

private def checkDirectives (markdown : String) : IO Unit := do
  let rows := (markdown.splitOn "\n").filterMap fun line => do
    let [address, full, short] := cells line | none
    return (← codeWord address, ← codeWord full, ← codeWord short)
  require (!rows.isEmpty) "В модальности не найдены примеры кратких побуждений."
  for (address, full, short) in rows do
    let some addressee := Directives.readAddressee address |
      throw (IO.userError s!"Неизвестный адресат «{address}».")
    let active := some addressee
    let some clause := Directives.parse active (tokens full) |
      throw (IO.userError s!"Не удалось разобрать побуждение «{full}».")
    let shortened := tokens short
    require (Directives.parse active shortened == some clause && Directives.compact active clause == shortened)
      s!"«{short}» не сохраняет разбор «{full}» для адресата «{address}»."
  IO.println s!"Проверены примеры побуждений ({rows.length}). Адресат и действие сохраняются."

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
    for group in groups do
      checkSpeechGroup "Разговор в саду.md" group
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
  checkDeixis (← IO.FS.readFile (vault / "Грамматика.md"))
  checkNumerals (← IO.FS.readFile (vault / "Числа.md"))
  checkFrameExamples (← IO.FS.readFile (vault / "Проверка синтаксиса.md"))
  let sounds ← IO.FS.readFile (vault / "Фонология.md")
  checkListeningExamples sounds
  checkSoundRatings sounds
  checkMovementProfiles
  checkVoiceExamples (← IO.FS.readFile (vault / "Залоги.md"))
  checkVoiceProfiles
  let questions ← IO.FS.readFile (vault / "Вопросительные слова.md")
  checkSpatialAnswers questions
  checkPolarityAnswers questions
  checkTransferAnswers (← IO.FS.readFile (vault / "Обладание и передача.md"))
  let adverbs ← IO.FS.readFile (vault / "Наречия.md")
  checkTemporalAdverbs adverbs
  checkTimeCompaction adverbs
  checkTimeClarification adverbs
  checkTimeClarificationProfiles
  let connectors ← IO.FS.readFile (vault / "Подчинительные союзы.md")
  checkConditionals connectors
  checkChoices connectors
  checkDirectives (← IO.FS.readFile (vault / "Модальность.md"))
  checkGardenDialogue (← IO.FS.readFile (vault / "Разговор в саду.md"))
  checkBenchmarks (← IO.FS.readFile (vault / "Формальный анализ.md"))
  checkSoundResemblances vault
  showLengthContrasts
