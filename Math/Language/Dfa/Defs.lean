import Math.Language.Defs

structure Dfa (σ α: Type*) where
  step: σ -> α -> α
  start: α
  accept: Set α

namespace Dfa

def runWith (nfa: Dfa σ α) (state: α) : List σ -> α
| [] => state
| a::as => nfa.runWith (nfa.step a state) as

def run (nfa: Dfa σ α) (word: List σ) : α :=
  nfa.runWith nfa.start word

def Matches (nfa: Dfa σ α) (word: List σ) : Prop :=
  nfa.run word ∈ nfa.accept

def Language (dfa: Dfa σ α) : Language σ where
  Mem := dfa.Matches

end Dfa
