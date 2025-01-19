import Math.Data.Group.Basic

namespace Group

-- the symmetric group of all permutations
def Permuatation (α: Type*) : Group where
  ty := α ≃ α
  one' := Equiv.refl
  mul' := Equiv.trans
  inv' := Equiv.symm
  one_mul' := by
    intro a
    rfl
  mul_assoc' := by
    intro a b c
    rfl
  inv_mul' := by
    intro a
    apply Equiv.toFun_inj'
    ext x
    show (a (a.symm x)) = x
    rw [a.symm_coe]

def IsoClass.Symmetric (α: Type*) : IsoClass := ⟦Permuatation α⟧

private def to_perm {g: Group} (a: g.ty) : g.ty ≃ g.ty where
  toFun b := b * a
  invFun b := b * a⁻¹
  leftInv := by
    intro x
    dsimp
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rightInv := by
    intro b
    dsimp
    rw [mul_assoc, inv_mul_cancel, mul_one]

def Permuatation.sub (g: Group) : SubgroupEmbedding g (Permuatation g.ty) where
  toFun a := to_perm a
  inj := by
    unfold to_perm
    intro a b eq
    dsimp at eq
    replace ⟨eq, eq'⟩ := Equiv.mk.inj eq
    clear eq'
    replace eq := fun x => congrFun eq x
    have := eq 1
    rw [one_mul, one_mul] at this
    assumption
  resp_mul' := by
    intro a b
    apply Equiv.invFun_inj'
    ext x
    show _ = Equiv.invFun (Equiv.trans _ _) _
    unfold Equiv.trans
    dsimp [to_perm]
    rw [inv_mul_rev, mul_assoc]
  resp_inv' := by
    intro a
    apply Equiv.invFun_inj'
    ext x
    show _ = Equiv.invFun (Equiv.symm _) _
    unfold Equiv.symm
    dsimp [to_perm]
    rw [inv_inv]

def gsub_perm (g: Group) : g ⊆ Permuatation g.ty := by
  apply IsSubgroup.ofSub
  apply Permuatation.sub

-- Cayley's Theorem - every group is a subgroup of the symmetric group
def IsoClass.gsub_symm (g: IsoClass) : ∃α, g ⊆ Symmetric α := by
  induction g with | mk g =>
  exists g.ty
  apply gsub_perm

end Group
