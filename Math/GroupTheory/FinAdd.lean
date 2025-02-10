import Math.GroupTheory.Subgroup
import Math.Algebra.Fin
import Math.Data.StdNat.Gcd
import Math.Relation.Basic
import Math.Data.Set.Finite

namespace Group

def Cyclic (n: Nat) [h: NeZero n] : Group (Fin n) :=
  have := h.ne
  match n with
  | _ + 1 => Group.ofAdd _

open Classical

variable (g: Subgroup (Cyclic (n + 1))) (h:∃x ∈ g.set, x.val ≠ 0)

instance : Set.IsFinite g.set := by
  have : IsFinite (Fin (n + 1)) := inferInstance
  apply Set.IsFinite.ofSubset (α := Fin (n + 1)) _ ⊤
  apply Set.sub_univ

private
noncomputable
def multiplier: Fin (n + 1) :=
    Classical.choose <| Relation.exists_min (· < ·) h

private
def multiplier_min: ∀x: Fin (n + 1), x ∈ g.set -> x < multiplier g h -> x.val = 0 := by
  unfold Group.multiplier
  intro x hx h'
  have ⟨⟨_, _⟩, ismin⟩ := Classical.choose_spec (Relation.exists_min (α := Fin (n + 1)) (· < ·) h)
  have := ismin x h'
  rw [not_and, Decidable.not_not] at this
  apply this
  assumption

private
def multiplier_nonzero: multiplier g h ≠ 0 := by
  have ⟨⟨_, _⟩, ismin⟩ := Classical.choose_spec (Relation.exists_min (α := Fin (n + 1)) (· < ·) h)
  intro g
  rw [←Fin.val_inj] at g
  contradiction

private
def multiplier_mem: multiplier g h ∈ g.set := by
  have ⟨⟨_, _⟩, ismin⟩ := Classical.choose_spec (Relation.exists_min (α := Fin (n + 1)) (· < ·) h)
  assumption

private
def multiplier_dvd (x: g.toGroup): (multiplier g h).val ∣ Fin.val (Subtype.val x) := by
  obtain ⟨⟨x, xLt⟩, xmem⟩ := x
  dsimp
  refine Nat.dvd_of_mod_eq_zero ?_

  sorry

def sub_cyclic:
  ∃m, ∃_: NeZero m, Nonempty (g.toGroup ≃* Cyclic m) := by
  by_cases h:∃x ∈ g.set, x.val ≠ 0
  · replace h: ∃x: Fin (n + 1), x ∈ g.set ∧ x.val ≠ 0 := h
    replace h := Relation.exists_min (fun x y => x.val < y.val) h
    obtain ⟨x, ⟨xmem, x_ne_zero⟩, xmin⟩ := h
    refine ⟨(n + 1) / x.val, ⟨?_⟩, ⟨?_⟩⟩
    · intro h
      have := (Nat.div_eq_zero_iff_lt (Nat.zero_lt_of_ne_zero x_ne_zero)).mp h
      exact Nat.lt_irrefl _ (Nat.lt_trans this x.isLt)
    dsimp at *
    conv at xmin => {
      intro y hy
      rw [not_and, Decidable.not_not]
    }

    have : ∀a ∈ g.set, x.val ∣ a.val := by
      intro ⟨a, aLt⟩ amem
      cases x with | mk x xLt =>
      dsimp at *
      have := Nat.div_add_mod a x

      apply Decidable.byContradiction
      intro h
      sorry
    apply GroupEquiv.mk _ _ _
    · apply _root_.Equiv.mk
      case toFun =>
        intro ⟨a, ha⟩
        -- refine ⟨?_, ?_⟩
        sorry
      case invFun => sorry
      case leftInv => sorry
      case rightInv => sorry
    sorry
    sorry
  · conv at h => {
      rw [not_exists]
      intro ;rw [not_and, Decidable.not_not]
    }
    refine ⟨1, ?_, ⟨?_⟩⟩
    infer_instance
    apply GroupEquiv.mk
    case neg.refine_2.toEquiv =>
      apply _root_.Equiv.mk
      case toFun =>
        intro x
        exact 1
      case invFun =>
        intro
        exact ⟨1, Subgroup.one_mem _⟩
      case leftInv =>
        intro x
        dsimp
        congr
        apply Fin.val_inj.mp
        apply Fin.val_inj.mpr
        dsimp
        symm
        apply Fin.val_inj.mp
        apply h
        exact x.property
      case rightInv =>
        intro x
        apply Fin.val_inj.mp
        apply Fin.val_inj.mpr
        dsimp
        apply Subsingleton.allEq
    rfl
    intro x y
    dsimp
    rw [one_mul]

def IsSimple.Cyclic [h: NeZero n] :
  n.IsAtomic ↔ (Cyclic n).IsSimple := by
  have := h.ne
  match n, h with
  | n + 1, h =>
  unfold Group.Cyclic
  dsimp; clear h this; clear h
  rename_i m; clear m
  apply Iff.intro
  · intro h
    sorry
  · sorry

end Group
