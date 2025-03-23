import Math.Order.Preorder

-- do not use this in bounds directly, this is only meant to be used to create a PreOrder
-- for example, via `GaloisConnection`
class PartialOrder (α: Type*) extends LT α, LE α, IsPartialOrder α

variable {α: Type*} {a b c d: α}
variable [LT α] [LE α] [IsPartialOrder α]

namespace Pi

variable {β: α -> Sort _}

instance [∀x, LE (β x)] [∀x, LT (β x)] [∀x, IsPartialOrder (β x)] : IsPartialOrder (∀x, β x) where
  le_antisymm := by
    intro a b ab ba
    ext x
    apply le_antisymm
    apply ab
    apply ba

end Pi

variable {β γ: Type*} {x y z: β} {f: α -> β} {g: β -> γ }
variable [LT β] [LE β] [IsPartialOrder β]
variable [LT γ] [LE γ] [IsPartialOrder γ]

namespace Monotone

def ofStrict (mf: StrictMonotone f) : Monotone f := by
  intro x y h
  rcases lt_or_eq_of_le h with h | h
  apply le_of_lt
  apply mf
  assumption
  rw [h]

end Monotone

namespace MonotoneOn

def ofStrict (mf: StrictMonotoneOn f s) : MonotoneOn f s := by
  intro x y hx hy h
  rcases lt_or_eq_of_le h with h | h
  apply le_of_lt
  apply mf
  assumption
  assumption
  assumption
  rw [h]

end MonotoneOn

namespace StrictMonotoneOn

def ofMonoInj [IsPreOrder α] (m: MonotoneOn f s) (h: Function.InjectiveOn f s) : StrictMonotoneOn f s := by
  intro x y hx hy hxy
  apply lt_of_le_of_ne
  apply m
  assumption
  assumption
  apply le_of_lt
  assumption
  intro g
  rw [h hx hy g] at hxy
  exact lt_irrefl hxy

end StrictMonotoneOn

namespace StrictMonotone

def ofMonoInj [IsPreOrder α] (m: Monotone f) (h: Function.Injective f) : StrictMonotone f := by
  rw [←StrictMonotone.iffOnUniv]
  rw [←Monotone.iffOnUniv] at m
  rw [←Function.InjectiveOn_univ_iff_Injective] at h
  apply StrictMonotoneOn.ofMonoInj
  assumption
  assumption

end StrictMonotone
