import Math.Language.Defs

inductive Regex (σ: Type*) where
| empty
| single (a: σ)
| alt (a b: Regex σ)
| seq (a b: Regex σ)
| star (a: Regex σ)

namespace Regex

inductive Matches {σ: Type*} : Regex σ -> List σ -> Prop where
| empty : Matches .empty []
| single (a: σ) : Matches (.single a) [a]
| alt_left (a b: Regex σ) (word: List σ) : Matches a word -> Matches (.alt a b) word
| alt_right (a b: Regex σ) (word: List σ) : Matches b word -> Matches (.alt a b) word
| star_nil (a: Regex σ) : Matches (.star a) []
| star_cons (a: Regex σ) (left right: List σ) : Matches a left -> Matches (.star a) right -> Matches (.star a) (left ++ right)
| seq (a b: Regex σ) (left right: List σ) : Matches a left -> Matches b right -> Matches (.seq a b) (left ++ right)

protected def Langauge (r: Regex σ) : Langauge σ where
  Mem := r.Matches

def language_empty : (Regex.empty: Regex σ).Langauge = {[]} := by
  ext
  simp [Regex.Langauge]
  apply Iff.intro
  intro h; cases h
  rfl
  rintro rfl
  apply Matches.empty

def language_single : (Regex.single a).Langauge = {[a]} := by
  ext
  simp [Regex.Langauge]
  apply Iff.intro
  intro h; cases h
  rfl
  rintro rfl
  apply Matches.single

def language_alt (a b: Regex σ) : (Regex.alt a b).Langauge = a.Langauge ∪ b.Langauge := by
  ext
  simp [Regex.Langauge]
  apply Iff.intro
  intro h; cases h
  left; assumption
  right; assumption
  rintro h
  cases h
  apply Matches.alt_left; assumption
  apply Matches.alt_right; assumption

def language_seq (a b: Regex σ) : (Regex.seq a b).Langauge = a.Langauge.seq b.Langauge := by
  ext
  simp [Regex.Langauge]
  apply Iff.intro
  intro h; cases h
  apply Langauge.SeqMatches.mk
  assumption
  assumption
  intro h
  cases h
  apply Matches.seq
  assumption
  assumption

def language_star (a: Regex σ) : (Regex.star a).Langauge = a.Langauge.star := by
  ext
  simp [Regex.Langauge]
  apply Iff.intro
  · generalize ha':a.star = a'
    intro h
    induction h with
    | empty | single | alt_left | alt_right | seq => contradiction
    | star_nil => apply Langauge.StarMatches.nil
    | star_cons _ _ _ _ _ ih₀ ih₁ =>
      apply Langauge.StarMatches.cons; cases ha'; assumption
      apply ih₁
      assumption
  . intro h
    induction h with
    | nil => apply Matches.star_nil
    | cons =>
      apply Matches.star_cons
      assumption
      assumption

end Regex
