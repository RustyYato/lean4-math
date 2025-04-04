import Math.Data.CauchySeq.Basic


section

variable (α: Type*) {γ: Type*}
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearLattice γ] [IsStrictOrderedSemiring γ]
  [FieldOps α] [IsField α] [Norm α γ]
  [SMul γ α] [IsModule γ α] [IsLawfulNorm α]

def Cauchy := Quotient (CauchySeq.setoid (α := α))

end

namespace Cauchy

open Norm.ofAbs

variable {α γ: Type*}
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearLattice γ] [IsStrictOrderedSemiring γ]
  [FieldOps α] [IsField α] [Norm α γ]
  [SMul γ α] [IsModule γ α] [IsLawfulNorm α]

def ofSeq : CauchySeq α -> Cauchy α := Quotient.mk _
def of (a: α) : Cauchy α := .ofSeq (.const a)
def add : Cauchy α -> Cauchy α -> Cauchy α := by
  apply Quotient.lift₂ (fun a b => ofSeq (a + b))
  intro a b c d ac bd
  apply Quotient.sound
  apply CauchySeq.add.spec
  assumption
  assumption
def neg : Cauchy α -> Cauchy α := by
  apply Quotient.lift (fun a => ofSeq (-a))
  intro a b ab
  apply Quotient.sound
  apply CauchySeq.neg.spec
  assumption
def sub : Cauchy α -> Cauchy α -> Cauchy α := by
  apply Quotient.lift₂ (fun a b => ofSeq (a - b))
  intro a b c d ac bd
  apply Quotient.sound
  apply CauchySeq.sub.spec
  assumption
  assumption
def norm : Cauchy α -> Cauchy γ := by
  apply Quotient.lift (fun a => ofSeq (‖a‖))
  intro a b ab
  apply Quotient.sound
  apply CauchySeq.norm.spec
  assumption

def nsmul (n: ℕ) : Cauchy α -> Cauchy α := by
  apply Quotient.lift (fun a => ofSeq (n • a))
  intro a b ab
  apply Quotient.sound
  apply CauchySeq.nsmul.spec
  assumption
def zsmul (n: ℤ) : Cauchy α -> Cauchy α := by
  apply Quotient.lift (fun a => ofSeq (n • a))
  intro a b ab
  apply Quotient.sound
  apply CauchySeq.zsmul.spec
  assumption

instance : Add (Cauchy α) where
  add := add
instance : Sub (Cauchy α) where
  sub := sub
instance : Neg (Cauchy α) where
  neg := neg
instance : Norm (Cauchy α) (Cauchy γ) where
  norm := norm
instance : SMul ℕ (Cauchy α) where
  smul := nsmul
instance : SMul ℤ (Cauchy α) where
  smul := zsmul

instance : NatCast (Cauchy α) := ⟨fun n => .of n⟩
instance : IntCast (Cauchy α) := ⟨fun n => .of n⟩
instance : Zero (Cauchy α) := ⟨(0: ℕ)⟩
instance : One (Cauchy α) := ⟨(1: ℕ)⟩

end Cauchy

namespace Cauchy

open Norm.ofAbs

variable {α γ: Type*}
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearLattice γ] [IsStrictOrderedSemiring γ]
  [FieldOps α] [IsField α] [Norm α γ]
  [SMul γ α] [AlgebraMap γ α] [IsAlgebra γ α] [IsAlgebraNorm α]

def mul : Cauchy α -> Cauchy α -> Cauchy α := by
  apply Quotient.lift₂ (fun a b => ofSeq (a * b))
  intro a b c d ac bd
  apply Quotient.sound
  apply CauchySeq.mul.spec
  assumption
  assumption
def npow (n: ℕ) : Cauchy α -> Cauchy α := by
  apply Quotient.lift (fun a => ofSeq (a ^ n))
  intro a b ab
  apply Quotient.sound
  apply CauchySeq.npow.spec
  assumption

instance : Mul (Cauchy α) where
  mul := mul
instance : Pow (Cauchy α) ℕ where
  pow := flip npow

end Cauchy
