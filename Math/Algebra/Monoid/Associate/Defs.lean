import Math.Algebra.Monoid.Units.Defs
import Math.Algebra.Hom.Defs
import Math.Algebra.Monoid.Con

def IsAssociates [One α] [Mul α] (a b: α) := ∃u: Units α, a * u = b

instance [MonoidOps α] [IsMonoid α] : Relation.IsEquiv (IsAssociates (α := α)) where
  refl a := ⟨1, by rw [Units.val_one, mul_one]⟩
  symm {a b} | ⟨u, h⟩ => ⟨u⁻¹, by
    rw [←h, mul_assoc, Units.val_inv, Units.val_mul_inv, mul_one]⟩
  trans {a b c} | ⟨u, h⟩, ⟨v, g⟩ => ⟨u * v, by
    rw [Units.val_mul, ←mul_assoc, h, g]⟩

def Associates.Con (α: Type*) [MonoidOps α] [IsCommMagma α] [IsMonoid α] : MulCon α where
  r := IsAssociates
  iseqv := Relation.equiv _
  resp_mul := by
    intro a b c d ac bd
    obtain ⟨u, rfl⟩ := ac
    obtain ⟨v, rfl⟩ := bd
    rw [mul_assoc, mul_left_comm _ b, ←mul_assoc]
    exists u * v

def Associates (α: Type*) [MonoidOps α] [IsCommMagma α] [IsMonoid α] := AlgQuotient (Associates.Con α)

namespace Associates

variable [MonoidOps α] [IsMonoid α] [IsCommMagma α]

instance : MonoidOps (Associates α) := inferInstanceAs (MonoidOps (AlgQuotient _))
instance : IsMonoid (Associates α) := inferInstanceAs (IsMonoid (AlgQuotient _))
instance : IsCommMagma (Associates α) := inferInstanceAs (IsCommMagma (AlgQuotient _))

instance [Zero α] : Zero (Associates α) := inferInstanceAs (Zero (AlgQuotient _))

def mk : α ↠* Associates α := MulCon.mkQuot (Associates.Con α)

def mk_rel {a b: α} : IsAssociates a b -> mk a = mk b := Quotient.sound (s := Relation.setoid (IsAssociates (α := α)))
def rel_of_mk {a b: α} : mk a = mk b -> IsAssociates a b := Quotient.exact

instance [Zero α] [IsMulZeroClass α] [IsNontrivial α] : IsNontrivial (Associates α) := by
  apply IsNontrivial.iff_not_subsingleton.mpr
  intro h
  have : (mk 0: Associates α) = mk 1 := Subsingleton.allEq _ _
  replace ⟨u, this⟩ := rel_of_mk this
  rw [zero_mul] at this
  exact zero_ne_one _ this

end Associates
