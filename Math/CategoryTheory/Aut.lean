import Math.CategoryTheory.Functor.Basic
import Math.Algebra.Group.Theory.Basic
import Math.Algebra.Group.Units.Defs

namespace Category

variable [Category α] [Category β] {x: α}

local instance : One (x ⟶ x) where
  one := 𝟙 _
local instance : Mul (x ⟶ x) where
  mul := (· ≫ ·)

instance : MonoidOps (x ⟶ x) where
  npow := flip npowRec
instance : IsMonoid (x ⟶ x) where
  mul_assoc _ _ _ := (comp_assoc _ _ _).symm
  one_mul _ := id_comp _
  mul_one _ := comp_id _

def Aut (x: α) := Units (x ⟶ x)

instance : GroupOps (Aut x) := inferInstanceAs (GroupOps (Units _))
instance : IsGroup (Aut x) := inferInstanceAs (IsGroup (Units _))

-- every functor from α to β induces a group homomorphism from
-- between their automorphism groups
def groupHom_of_functor (f: α ⥤ β) (x: α) : Aut x →* Aut (f.obj x) where
  toFun x := {
    val := f.map x.val
    inv := f.map x.inv
    val_mul_inv := by
      show _ ≫ _ = _
      rw [←f.map_comp]
      show f.map (x.val * _) = _
      rw [x.val_mul_inv]
      show f.map (𝟙 _) = _
      rw [f.map_id]
      rfl
    inv_mul_val := by
      show _ ≫ _ = _
      rw [←f.map_comp]
      show f.map (x.inv * _) = _
      rw [x.inv_mul_val]
      show f.map (𝟙 _) = _
      rw [f.map_id]
      rfl
  }
  resp_one' := by
    apply Units.val.inj
    apply f.map_id
  resp_mul' := by
    intro a b
    apply Units.val.inj
    apply f.map_comp

end Category
