import Math.GroupTheory.Subgroup
import Math.Algebra.Impls.Int

namespace Group

variable (G: Group α)

instance : One (G ≃* G) where
  one := .refl
instance : Inv (G ≃* G) where
  inv := .symm
instance : Mul (G ≃* G) where
  mul := .trans

-- the automorphism group is the set of all bijective group homomorphisms
def Aut : Group (G ≃* G) := by
  apply Group.ofAxiomsLeft
  case mul_assoc =>
    intros
    rfl
  case one_mul =>
    intros
    rfl
  case inv_mul =>
    intro x
    apply GroupEquiv.symm_trans

end Group
