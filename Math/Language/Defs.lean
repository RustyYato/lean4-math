import Math.Data.Set.Basic

abbrev Langauge (σ: Type*) := Set (List σ)

namespace Langauge

inductive SeqMatches (a b: Langauge σ) : List σ -> Prop where
| mk (left right: List σ) :
  left ∈ a -> right ∈ b ->
  SeqMatches a b (left ++ right)

def seq (a b: Langauge σ) : Langauge σ where
  Mem := SeqMatches a b

inductive StarMatches (a: Langauge σ) : List σ -> Prop where
| nil : StarMatches a []
| cons (left right: List σ) :
  left ∈ a ->
  StarMatches a right ->
  StarMatches a (left ++ right)

def star (a: Langauge σ) : Langauge σ where
  Mem := StarMatches a

end Langauge
