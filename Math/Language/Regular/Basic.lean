import Math.Language.Dfa.Defs
import Math.Language.Nfa.Defs
import Math.Language.Regex.Defs

namespace Nfa

-- def ofRegex {σ: Type u} : ∀r: Regex σ, Σ'(α: Type u) (nfa: Nfa σ α), nfa.Language = r.Language
-- | .empty => sorry
-- | .single a => sorry
-- | .alt a b => sorry
-- | .seq a b => sorry
-- | .star a => sorry

end Nfa

namespace Dfa

-- a nfa->dfa construction using the subset method
def ofNfa (nfa: Nfa σ α) : Dfa σ (Set α) where
  step := nfa.stepSet
  start := nfa.start
  accept := Set.mk fun S => ∃s ∈ S, s ∈ nfa.accepting_states

end Dfa
