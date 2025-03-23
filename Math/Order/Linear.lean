import Math.Order.Partial

-- do not use this in bounds directly, this is only meant to be used to create a PreOrder
-- for example, via `GaloisConnection`
class LinearOrder (α: Type*) extends LT α, LE α, IsLinearOrder α

-- do not use this in bounds directly, this is only meant to be used to create a PreOrder
-- for example, via `GaloisConnection`
class LinearMinMaxOrder (α: Type*) extends LT α, LE α, Min α, Max α, IsLinearMinMaxOrder α

variable {α: Type*} {a b c d: α}
variable [LT α] [LE α] [Min α] [Max α]
variable [IsLinearOrder α]

-- do not use this in bounds directly, this is only meant to be used to create a PreOrder
-- for example, via `GaloisConnection`
class DecidableLinearOrder (α: Type*) extends LT α, LE α, Min α, Max α, IsDecidableLinearOrder α

variable {β γ: Type*} {x y z: β} {f: α -> β} {g: β -> γ}
variable [LT β] [LE β]
variable [LT γ] [LE γ]

namespace StrictMonotoneOn

def InjectiveOn [IsPreOrder β] (m: StrictMonotoneOn f s) : Function.InjectiveOn f s := by
  intro x y hx hy hxy
  rcases lt_trichotomy x y with h | h | h
  have := m hx hy h
  rw [hxy] at this
  have := lt_irrefl this
  contradiction
  assumption
  have := m hy hx h
  rw [hxy] at this
  have := lt_irrefl this
  contradiction

end StrictMonotoneOn

namespace StrictMonotone

def Injective [IsPreOrder β] (m: StrictMonotone f) : Function.Injective f := by
  rw [←StrictMonotone.iffOnUniv] at m
  rw [←Function.InjectiveOn_univ_iff_Injective]
  apply StrictMonotoneOn.InjectiveOn
  assumption

end StrictMonotone
