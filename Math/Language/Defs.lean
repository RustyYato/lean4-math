import Math.Data.Set.Basic

abbrev Language (σ: Type*) := Set (List σ)

namespace Language

inductive SeqMatches (a b: Language σ) : List σ -> Prop where
| mk (left right: List σ) :
  left ∈ a -> right ∈ b ->
  SeqMatches a b (left ++ right)

def seq (a b: Language σ) : Language σ where
  Mem := SeqMatches a b

inductive StarMatches (a: Language σ) : List σ -> Prop where
| nil : StarMatches a []
| cons (left right: List σ) :
  left ∈ a ->
  StarMatches a right ->
  StarMatches a (left ++ right)

def star (a: Language σ) : Language σ where
  Mem := StarMatches a

end Language
