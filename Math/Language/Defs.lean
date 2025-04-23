import Math.Data.Set.Basic

-- a language is a set of words
structure Langauge (σ: Type*) where
  words: Set (List σ)

instance : Membership (Langauge σ) (List σ) where
  mem w l := w ∈ l.words
