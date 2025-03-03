import Math.Data.Fintype.Defs

namespace Array

private def buildFrom (source: List α) : ∀n, List { x: Array α // x.size = n }
| 0 => [⟨#[], rfl⟩]
| n + 1 => by
  apply (buildFrom source n).flatMap
  intro ⟨as, len_eq⟩
  apply source.map
  intro x
  refine ⟨as.push x, ?_⟩
  rw [Array.size_push, ←len_eq]

end Array

instance Array.VectorFintype [f: Fintype α] : Fintype { x: Array α // x.size = n } where
  all := Array.buildFrom f.all n
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
        replace eq := Subtype.mk.inj eq
        exact Array.push_inj_right.mp eq
        assumption
      · intro ⟨x,xlen⟩ ⟨y, ylen⟩ xmem ymem z zmemx zmemy
        dsimp at zmemx zmemy
        have ⟨_, _, xeq⟩ := List.mem_map.mp zmemx
        have ⟨_, _, yeq⟩ := List.mem_map.mp zmemy
        congr
        have eq := (Subtype.mk.inj (xeq.trans yeq.symm))
        have ⟨_, _⟩  := Array.push_eq_push.mp eq
        assumption
  complete := by
    intro ⟨x, xlen⟩
    induction n generalizing x with
    | zero =>
      cases x with | mk x =>
      cases x
      apply List.Mem.head
      contradiction
    | succ n ih =>
      have ⟨as, a, eq⟩ := Array.eq_push_of_size_ne_zero (fun h => Nat.noConfusion (h ▸ xlen))
      subst eq
      apply List.mem_flatMap.mpr
      refine ⟨⟨as, ?_⟩ , ?_⟩
      rw [Array.size_push] at xlen
      exact Nat.succ.inj xlen
      apply And.intro
      apply ih
      dsimp
      apply List.mem_map.mpr
      refine ⟨a, ?_, ?_⟩
      apply Fintype.complete
      rfl

def Array.card (f: Fintype α) : Fintype.card { x: Array α // x.size = n } = f.card ^ n := by
  show (List.length (Array.buildFrom _ _)) = _
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Array.buildFrom
    rw [Nat.pow_succ, List.length_flatMap, List.sum_const' (a := Fintype.card α)]
    rw [List.length_map, ih, Nat.mul_comm]
    intro x mem
    replace ⟨⟨xs, len_eq⟩ , mem, eq⟩  := List.mem_map.mp mem
    dsimp at *
    rw [List.length_map] at eq
    exact eq.symm
