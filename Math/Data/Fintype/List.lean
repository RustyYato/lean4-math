import Math.Data.Fintype.Defs

namespace List

private def buildFrom (source: List α) : ∀n, List { x: List α // x.length = n }
| 0 => [⟨[], rfl⟩]
| n + 1 => by
  apply (buildFrom source n).flatMap
  intro ⟨as, len_eq⟩
  apply source.map
  intro x
  refine ⟨x::as, ?_⟩
  rw [←len_eq]; rfl

end List

instance List.VectorFintype [f: Fintype α] : Fintype { x: List α // x.length = n } where
  all := List.buildFrom f.all n
  nodup := by
    cases f with | mk all nodup complete =>
    unfold Fintype.all
    dsimp
    clear complete
    induction n with
    | zero =>
      apply List.Pairwise.cons
      intros; contradiction
      apply List.Pairwise.nil
    | succ n ih =>
      apply List.nodup_flatMap
      assumption
      · intro ⟨as, as_len⟩
        dsimp
        apply List.nodup_map
        intro _ _ eq
        dsimp at eq
        cases eq
        rfl
        assumption
      · intro ⟨x,xlen⟩ ⟨y, ylen⟩  xmem ymem z zmemx zmemy
        dsimp at zmemx zmemy
        have ⟨_, _, eq⟩  := List.mem_map.mp zmemx
        have ⟨_, _, eq⟩  := List.mem_map.mp zmemy
        cases eq; cases eq
        rfl
  complete := by
    intro ⟨x, xlen⟩
    induction n generalizing x with
    | zero =>
      cases x
      apply List.Mem.head
      contradiction
    | succ n ih =>
      cases x
      contradiction
      rename_i a as
      apply List.mem_flatMap.mpr
      refine ⟨⟨as, ?_⟩ , ?_⟩
      apply Nat.succ.inj xlen
      apply And.intro
      apply ih
      dsimp
      apply List.mem_map.mpr
      refine ⟨a, ?_, ?_⟩
      apply Fintype.complete
      rfl

def List.card (f: Fintype α) : Fintype.card { x: List α // x.length = n } = f.card ^ n := by
  show (List.length (List.buildFrom _ _)) = _
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold List.buildFrom
    rw [Nat.pow_succ, List.length_flatMap, List.sum_const' (a := Fintype.card α)]
    rw [List.length_map, ih, Nat.mul_comm]
    intro x mem
    replace ⟨⟨xs, len_eq⟩ , mem, eq⟩  := List.mem_map.mp mem
    dsimp at *
    rw [List.length_map] at eq
    exact eq.symm
