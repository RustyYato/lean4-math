import Math.Algebra.Monoid.Hom
import Math.Logic.IsEmpty
import Math.Logic.Equiv.Defs

def FreeMonoid (α: Type*) : Type _ := List α

namespace FreeMonoid

def toList : FreeMonoid α -> List α := id
def ofList : List α -> FreeMonoid α := id

instance : One (FreeMonoid α) where
  one := .ofList []

instance : Inhabited (FreeMonoid α) where
  default := 1

instance : Mul (FreeMonoid α) where
  mul a b := .ofList (a.toList ++ b.toList)

instance : Pow (FreeMonoid α) ℕ := instNPowrec

instance : IsMonoid (FreeMonoid α) where
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

instance : IsMulCancel (FreeMonoid α) where
  mul_left_cancel := List.append_cancel_left
  mul_right_cancel := List.append_cancel_right

instance [IsEmpty α] : Subsingleton (FreeMonoid α) where
  allEq a b := by
    cases a
    cases b
    rfl
    rename_i a _
    exact elim_empty a
    rename_i a _
    exact elim_empty a

def of : α ↪ FreeMonoid α where
  toFun a := .ofList [a]
  inj' := by
    intro x y h
    exact (List.cons.inj h).left

def reverse (a: FreeMonoid α) : FreeMonoid α := .ofList a.toList.reverse

def reverseEquiv : FreeMonoid α ≃* (FreeMonoid α)ᵐᵒᵖ where
  toFun a := .mk (reverse a)
  invFun a := reverse a.get
  leftInv := by apply List.reverse_reverse
  rightInv := by apply List.reverse_reverse
  map_one := rfl
  map_mul := by
    intro x y
    apply List.reverse_append

def reverse_of : reverse (of a) = of a := rfl
def reverseEquiv_of : reverseEquiv (of a) = of a := rfl

def reverse_mul {a b : FreeMonoid α} : reverse (a * b) = reverse b * reverse a := by
  apply List.reverse_append

end FreeMonoid
