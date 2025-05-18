import Math.TypeTheory.Lambda.OpSem

namespace LamTerm

def weaken_by (term: LamTerm) : Nat -> LamTerm
| 0 => term
| n + 1 => term.weaken.weaken_by n

def substAll (term: LamTerm) : List LamTerm -> LamTerm
| [] => term
| subst::substs =>
  (term.subst (subst.weaken_by substs.length)).substAll substs

def IsWellTyped.substAll :
  IsWellTyped ctx ty term ->
  ctx.length = substs.length ->
  (∀s ∈ substs, ∃ty', IsWellTyped [] ty' s) ->
  IsWellTyped [] ty (term.substAll substs) := by
  intro wt h substwt
  induction substs generalizing ctx term with
  | nil =>
    cases ctx
    assumption
    contradiction
  | cons s substs ih =>
    have ⟨sty, swt⟩ := substwt s (List.Mem.head _)
    apply ih
    apply IsWellTyped.subst _ (s.weaken_by _)
    exact swt


    sorry
    sorry

end LamTerm
