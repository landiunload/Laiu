import Std

namespace Laiu.Lexicon

/-- Snapshot of the active word entries in Лексика.md. Each row assigns a lexical gloss. -/
def entries : List (String × String) := [
  ("и", "я"),
  ("ии", "мы без уточнения"),
  ("ииа", "мы вместе с адресатом"),
  ("ииэ", "мы без адресата"),
  ("а", "ты"),
  ("аа", "вы"),
  ("ааа", "вы, особо вежливое обращение"),
  ("у", "он"),
  ("уу", "они мужского рода"),
  ("о", "она"),
  ("оо", "они женского рода"),
  ("э", "третье лицо без указания пола"),
  ("ээ", "третье лицо множественного числа, нейтральное или смешанное"),
  ("ли", "логическое отрицание"),
  ("ла", "подтверждение пропозиции"),
  ("ло", "прошлое"),
  ("лэ", "настоящее"),
  ("лу", "будущее"),
  ("эм", "нейтральный вопрос"),
  ("лам", "вопрос с ожидаемым `ла`"),
  ("лим", "вопрос с ожидаемым `ли`"),
  ("тэ", "начало вложенной части"),
  ("эт", "конец вложенной части"),
  ("тэр", "явная отсылка к имени внутри определительной части"),
  ("ка", "достигнутый результат"),
  ("тиа", "начало действия"),
  ("эо", "прекращение действия"),
  ("эс", "пассивный залог"),
  ("мо", "повелительное наклонение"),
  ("эли", "возможность события"),
  ("сии", "возвратная ссылка к субъекту глагола"),
  ("наа", "взаимная направленность действия"),
  ("ам", "все"),
  ("ами", "каждый по отдельности"),
  ("иам", "хотя бы один"),
  ("ув", "более выраженный признак"),
  ("ов", "менее выраженный признак"),
  ("нал", "равенство признака"),
  ("ин", "нахождение внутри"),
  ("эн", "источник или точка отсчёта"),
  ("ба", "соприкосновение сверху"),
  ("бо", "выше ориентира"),
  ("ни", "ниже ориентира"),
  ("куа", "цель направления или передачи"),
  ("си", "принадлежность"),
  ("на", "И"),
  ("эу", "хотя бы один вариант"),
  ("эуу", "ровно один вариант"),
  ("им", "если"),
  ("иим", "если бы"),
  ("риа", "потому что"),
  ("луа", "когда"),
  ("оту", "после того как"),
  ("каи", "чтобы"),
  ("эна", "но"),
  ("эни", "хотя"),
  ("эмир", "кто"),
  ("эмас", "что"),
  ("эмси", "чей"),
  ("эмбо", "где"),
  ("эмкуа", "какова цель направления или передачи"),
  ("эмэн", "каков источник"),
  ("эмлу", "когда"),
  ("эмри", "почему"),
  ("эмти", "каким способом"),
  ("эмки", "сколько"),
  ("ки", "передвигаться пешком"),
  ("роки", "возвращаться к прежнему месту"),
  ("ру", "перемещаться"),
  ("но", "спать"),
  ("нум", "пить"),
  ("ву", "есть, принимать пищу"),
  ("сум", "обладать"),
  ("ку", "брать"),
  ("му", "передавать вещь"),
  ("мут", "вызывать чужое действие"),
  ("ко", "делать"),
  ("лиси", "управлять"),
  ("пи", "видеть"),
  ("рис", "воспринимать"),
  ("мит", "говорить"),
  ("та", "знать"),
  ("ра", "верить"),
  ("мил", "любить"),
  ("ми", "хотеть"),
  ("лип", "быть в состоянии сделать"),
  ("тал", "иметь разрешение"),
  ("тил", "быть обязанным"),
  ("ри", "быть (с результативной `ка` — стать)"),
  ("ар", "солнце"),
  ("ну", "луна"),
  ("ари", "звезда"),
  ("боа", "небо"),
  ("са", "земля"),
  ("со", "камень"),
  ("сок", "гора"),
  ("ти", "дерево"),
  ("ил", "вода"),
  ("или", "река"),
  ("лап", "огонь"),
  ("ир", "человек"),
  ("ур", "мужчина"),
  ("ор", "женщина"),
  ("иру", "ребёнок"),
  ("кам", "рука"),
  ("пис", "глаз"),
  ("кув", "голова"),
  ("ник", "нога"),
  ("вим", "сердце"),
  ("тив", "сад"),
  ("там", "дом"),
  ("вус", "еда"),
  ("кири", "странствие"),
  ("лури", "время"),
  ("мири", "мечта"),
  ("рари", "вера"),
  ("лиил", "власть"),
  ("ви", "маленький"),
  ("ва", "большой"),
  ("ал", "хороший"),
  ("эл", "плохой"),
  ("ул", "новый"),
  ("ол", "старый"),
  ("пар", "горячий"),
  ("нар", "холодный"),
  ("сим", "красивый"),
  ("лик", "сильный"),
  ("ма", "богатый"),
  ("боу", "наверху"),
  ("ниу", "внизу"),
  ("ину", "внутри"),
  ("эну", "снаружи"),
  ("тоу", "здесь"),
  ("тооу", "там"),
  ("то", "вот это"),
  ("тоо", "вон то"),
  ("том", "вот эти"),
  ("тоом", "вон те"),
  ("ииу", "сейчас"),
  ("ооу", "слабо"),
  ("виу", "мало"),
  ("ааму", "очень"),
  ("вилу", "иногда"),
  ("иииу", "чрезвычайно"),
  ("мии", "чрезмерно"),
  ("вио", "недостаточно"),
  ("ваау", "с наибольшим размахом"),
  ("вииу", "в наименьшей степени"),
  ("луу", "скоро"),
  ("лоо", "недавно"),
  ("нуу", "ночью"),
  ("аруу", "днём"),
  ("катии", "всегда"),
  ("нэлу", "никогда"),
  ("наау", "совместно"),
  ("сиу", "быстро"),
  ("носу", "медленно"),
  ("мали", "приветствие"),
  ("малу", "благодарность"),
  ("нэ", "число 0"),
  ("кати", "число 1"),
  ("кити", "число 2"),
  ("коти", "число 3"),
  ("оти", "число 4"),
  ("ото", "число 5"),
  ("уки", "число 6"),
  ("ики", "число 7"),
  ("оки", "число 8"),
  ("ати", "число 9"),
  ("па", "граница семиразрядного блока"),
  ("ит", "порядковое числительное"),
  ("тэл", "граница между числителем и знаменателем")
]

def forms (dictionary : List (String × String)) : List String :=
  dictionary.map Prod.fst

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem entries_have_no_duplicate_forms : (forms entries).Nodup := by
  decide

/-- A well-formed table never assigns two different entries to one written form. -/
theorem unique_lookup (dictionary : List (String × String))
    (h : (forms dictionary).Nodup) :
    ∀ {form first second : String},
      (form, first) ∈ dictionary → (form, second) ∈ dictionary → first = second := by
  induction dictionary with
  | nil => simp
  | cons entry rest ih =>
    rcases entry with ⟨key, gloss⟩
    simp only [forms, List.map_cons, List.nodup_cons] at h
    intro form first second left right
    simp only [List.mem_cons] at left right
    rcases left with left | left <;> rcases right with right | right
    · exact congrArg Prod.snd (left.trans right.symm)
    · have keyEq : form = key := congrArg Prod.fst left
      exact (h.1 (by
        rw [← keyEq]
        exact List.mem_map.mpr ⟨(form, second), right, rfl⟩)).elim
    · have keyEq : form = key := congrArg Prod.fst right
      exact (h.1 (by
        rw [← keyEq]
        exact List.mem_map.mpr ⟨(form, first), left, rfl⟩)).elim
    · exact ih h.2 left right

theorem active_lookup_unambiguous {form first second : String}
    (hl : (form, first) ∈ entries) (hr : (form, second) ∈ entries) :
    first = second :=
  unique_lookup entries entries_have_no_duplicate_forms hl hr

def beforeComparativeSplit : List (String × String) :=
  [("у", "third person masculine"), ("о", "third person feminine"),
   ("у", "more"), ("о", "less")]

theorem canon40_comparatives_collided : ¬ (forms beforeComparativeSplit).Nodup := by
  decide

def vowels : List Char := ['а', 'э', 'и', 'о', 'у']

def containsVowel (word : List Char) : Prop :=
  ∃ character ∈ word, character ∈ vowels

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem all_single_vowel_words_taken (character : Char) (h : character ∈ vowels) :
    String.ofList [character] ∈ forms entries := by
  simp [vowels] at h
  rcases h with h | h | h | h | h <;> subst character <;> decide

/-- Every fresh native form with a vowel is at least two letters long. -/
theorem fresh_form_needs_two_letters (word : List Char) (voice : containsVowel word)
    (available : String.ofList word ∉ forms entries) : 2 ≤ word.length := by
  cases word with
  | nil => simp [containsVowel] at voice
  | cons first rest =>
    cases rest with
    | nil =>
      have h : first ∈ vowels := by simpa [containsVowel] using voice
      exact (available (all_single_vowel_words_taken first h)).elim
    | cons second tail => simp

theorem comparisons_attain_two_letters :
    "ув".length = 2 ∧ "ов".length = 2 ∧
    "ув" ∈ forms entries ∧ "ов" ∈ forms entries := by decide

end Laiu.Lexicon
