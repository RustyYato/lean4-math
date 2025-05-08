import Math.Algebra.Monoid.SetLike.Basic
import Math.Algebra.DirectSum.Defs

namespace DirectSum

variable [DecidableEq γ] [AddMonoidOps M] [IsAddMonoid M]
  [IsAddCommMagma M] [∀m: M, Decidable (m  =0)]
variable [SetLike σ M] [IsAddSubmonoid σ] (A : γ → σ)

private instance (a: A i) : Decidable (a = 0) :=
  decidable_of_iff (a.val = 0) (by
    obtain ⟨a, ha⟩ := a
    simp
    rw [←Subtype.val_inj.eq_iff]
    rfl)

def get {A: γ -> σ} : (⊕i, A i) →+ M :=
  lift <| fun _ => {
    toFun := Subtype.val
    map_zero := rfl
    map_add := rfl
  }

def get_ι (a: A i) : get (A := A) (ι i a) = a.val := lift_ι _

protected class Decomposition where
  protected decompose' : M -> ⊕i, A i
  leftInv : Function.IsLeftInverse get decompose'
  rightInv : Function.IsRightInverse get decompose'

def _root_.decompose {A: γ -> σ} (d: DirectSum.Decomposition A) : M ≃+ ⊕i, A i := AddGroupEquiv.symm {
  get with
  invFun := d.decompose'
  leftInv := d.rightInv
  rightInv := d.leftInv
}

def Decomposition.apply_decompose (d: DirectSum.Decomposition A) : decompose d = d.decompose' := rfl
def Decomposition.symm_apply_decompose (d: DirectSum.Decomposition A) : ((decompose d).symm: _ -> _) = get (A := A) := rfl

instance : Subsingleton (DirectSum.Decomposition A) where
  allEq a b := by
    have : decompose a = decompose b := by
      apply DFunLike.ext; intro m
      apply (decompose a).symm.inj
      simp
      show _ = (decompose b).symm _
      simp
    have : (decompose a: _ -> _) = (decompose b) := by rw [this]
    rw [Decomposition.apply_decompose, Decomposition.apply_decompose] at this
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    congr

end DirectSum
