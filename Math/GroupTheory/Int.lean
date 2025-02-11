import Math.GroupTheory.Subgroup
import Math.Algebra.Impls.Int

namespace Group

def AddInt : AbelianGroup Int := AbelianGroup.ofAdd Int

-- the Cyclic group is the quotient of the AddInt group by some element a
def Cyclic (a: Int) := Subgroup.IsNormal.Quot (A := Subgroup.generated (g := (AddInt: Group ℤ)) {a})
  (Subgroup.IsNormal.ofAbelian _)

-- the cyclic group of order 0 is equal to the entire group, so it's not really a cyclic group
-- but it's convenient to just leave it in
def cyclic_zero_eq_trivial : AddInt ≃* Cyclic 0 where
  toFun x := Subgroup.mkQuot _ x
  invFun x := by
    apply x.lift id
    intro a b eq
    have : Subgroup.cosetLeft a _ = Subgroup.cosetLeft b _ := eq
    rw [show Subgroup.generated _ = ⊥ from ?_] at this
    · have mem := Subgroup.rep_mem_cosetLeft (A := ⊥) (x := a)
      rw [this] at mem
      obtain ⟨x, _, eq⟩ := mem; subst x
      dsimp at eq
      rw [mul_one] at eq
      assumption
    apply Subgroup.generate_one
  leftInv _ := rfl
  rightInv x := by
    induction x using Quot.ind with
    | mk x => rfl
  resp_one := rfl
  resp_mul := rfl

-- the cyclic group of order 1 is equal to the trivial group
def cyclic_one_eq_trivial : Trivial ≃* Cyclic 1 where
  toFun _ := 1
  invFun _ := 1
  leftInv _ := rfl
  rightInv x := by
    dsimp
    induction x using Quot.ind with
    | mk x =>
    apply Quotient.sound
    ext y
    rw [show Subgroup.generated _ = ⊤ from ?_]
    · apply Iff.intro
      intro ⟨z, hz, h⟩
      subst y
      dsimp
      rw [one_mul]
      refine ⟨x⁻¹ * z, ?_, ?_⟩
      trivial
      dsimp
      rw [←mul_assoc, mul_inv_cancel, one_mul]
      intro ⟨z, hz, h⟩
      subst y
      refine ⟨x * z, ?_, ?_⟩
      trivial
      dsimp
      rw [one_mul]
    · ext x
      apply Iff.intro
      intro; trivial
      intro h; clear h
      unfold Elem at x
      let one: Int := 1
      let one': AddInt := one
      have : x = one' ^ (x: Int) := by
        show x = x * 1
        rw [Int.mul_one]
      rw [this]
      apply Subgroup.zpow_mem _ ⟨_, _⟩
      apply Subgroup.Generate.of
      rfl
  resp_one := rfl
  resp_mul := rfl


end Group
