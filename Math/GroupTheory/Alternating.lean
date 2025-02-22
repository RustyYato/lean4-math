import Math.GroupTheory.Subgroup
import Math.GroupTheory.Perm

open Classical

def Equiv.is_one_swap_away (h g: α ≃ α) : Prop :=
  ∃x y: α, x ≠ y ∧ g = h.trans (Equiv.swap x y)

inductive Equiv.IsEven: α ≃ α -> Prop where
| refl : IsEven .refl
| cons : is_one_swap_away a k -> is_one_swap_away k b -> IsEven b -> IsEven a

def Equiv.is_one_swap_away.symm (a b: α ≃ α) :
  is_one_swap_away a b -> is_one_swap_away b a := by
  intro h
  obtain ⟨x, y, ne, prf⟩ := h
  refine ⟨y, x, ne.symm, ?_⟩
  rw [prf, Equiv.trans_trans, ←Equiv.swap_symm, Equiv.symm_trans_self]
  rfl

def Equiv.IsEven.of_trans
  (a b: α ≃ α) :
  (a.trans b).IsEven -> b.IsEven -> a.IsEven := by
  intro hab hb
  induction hb with
  | refl => assumption
  | cons bx bz hb ih =>
    apply ih
    rename_i x y z
    apply IsEven.cons _ _ hab
    exact (a.trans y)
    have ⟨x₀, x₁, ne, spec⟩ := bz.symm
    rw [spec]
    rw [←Equiv.trans_trans]
    refine ⟨x₀, x₁, ne, ?_⟩
    rfl
    have ⟨x₀, x₁, ne, spec⟩ := bx.symm
    rw [spec]
    rw [←Equiv.trans_trans]
    refine ⟨x₀, x₁, ne, ?_⟩
    rfl

def Equiv.IsEven.symm {h: α ≃ α} (hx: IsEven h) : IsEven h.symm := by
  apply Equiv.IsEven.of_trans h.symm h
  rw [Equiv.symm_trans]
  exact Equiv.IsEven.refl
  assumption

def Equiv.IsEven.trans {h g: α ≃ α} (hx: IsEven h) (gx: IsEven g) : IsEven (h.trans g) := by
  show ((h.trans g).trans .refl).IsEven
  apply Equiv.IsEven.of_trans (h.trans g) g.symm
  apply Equiv.IsEven.of_trans _ h.symm
  rw [Equiv.trans_assoc h, g.trans_symm]
  show (h.trans h.symm).IsEven
  rw [h.trans_symm]
  exact Equiv.IsEven.refl
  exact hx.symm
  exact gx.symm

namespace Group

structure EvenPermType (α: Type*) where
  perm: α ≃ α
  isEven: perm.IsEven

instance : One (EvenPermType α) where
  one := ⟨.refl, .refl⟩

instance : Inv (EvenPermType α) where
  inv h := ⟨h.perm.symm, h.isEven.symm⟩

instance : Mul (EvenPermType α) where
  mul a b := ⟨a.perm.trans b.perm, a.isEven.trans b.isEven⟩

def EvenPerm (α: Type*) : Group (EvenPermType α) := by
  apply Group.ofAxiomsLeft
  intro
  rfl
  intro x
  · cases x with | mk x hx =>
    show EvenPermType.mk _ _ = EvenPermType.mk _ _
    congr
    apply Equiv.symm_trans_self
  intro  _ _ _; rfl

-- the alternating group embeds directly into the symmetric group
-- this proves that EvenPerm is a subgroup of Perm (see [`ofEmbed`])
def embedPerm : EvenPerm α ↪* Perm α where
  toFun x := x.perm
  inj' := by
    intro x y eq
    cases x; congr
  resp_mul := rfl
  resp_one := rfl

end Group
