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

protected def Language (r: Regex σ) : Langauge σ where
  words := Set.mk r.Matches

end Regex
