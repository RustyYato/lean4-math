import Math.Language.Defs

structure Nfa (σ α: Type*) where
  step: σ -> α -> Set α
  start: Set α
  accept: Set α

namespace Nfa

def stepAll (nfa: Nfa σ α) (states: Set α) (a: σ) : Set α := (⋃states.image (nfa.step a))

def runWith (nfa: Nfa σ α) (states: Set α) : List σ -> Set α
| [] => states
| a::as => nfa.runWith (nfa.stepAll states a) as

def run (nfa: Nfa σ α) (word: List σ) : Set α :=
  nfa.runWith nfa.start word

def Matches (nfa: Nfa σ α) (word: List σ) : Prop :=
  (nfa.run word ∩ nfa.accept).Nonempty

def Language (nfa: Nfa σ α) : Langauge σ where
  words := Set.mk nfa.Matches

end Nfa
