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
instance : Zero (Cauchy α) := ⟨.of 0⟩
instance : One (Cauchy α) := ⟨.of 1⟩

@[induction_eliminator]
def ind : ∀{motive: Cauchy α -> Prop}, (ofSeq: ∀a, motive (ofSeq a)) -> ∀a, motive a := Quotient.ind
@[induction_eliminator]
def ind₂ : ∀{motive: Cauchy α -> Cauchy α -> Prop}, (ofSeq: ∀a b, motive (ofSeq a) (ofSeq b)) -> ∀a b, motive a b := Quotient.ind₂
@[induction_eliminator]
def ind₃ : ∀{motive: Cauchy α -> Cauchy α -> Cauchy α -> Prop}, (ofSeq: ∀a b c, motive (ofSeq a) (ofSeq b) (ofSeq c)) -> ∀a b c, motive a b c := by
  intro _ h a b c
  induction a, b
  induction c
  apply h

instance : IsAddGroupWithOne (Cauchy α) where
  add_assoc a b c := by
    induction a, b, c
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply add_assoc
  zero_add a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply zero_add
  add_zero a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply add_zero
  sub_eq_add_neg a b := by
    induction a, b
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply sub_eq_add_neg
  zero_nsmul a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply zero_nsmul
  succ_nsmul _ a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply succ_nsmul
  zsmul_ofNat _ a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply zsmul_ofNat
  zsmul_negSucc _ a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply zsmul_negSucc
  neg_add_cancel a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply neg_add_cancel
  natCast_zero := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply natCast_zero
  natCast_succ _ := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply natCast_succ
  intCast_ofNat _ := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply intCast_ofNat
  intCast_negSucc _ := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply intCast_negSucc

instance : IsAddCommMagma (Cauchy α) where
  add_comm a b := by
    induction a, b
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply add_comm

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

instance : IsCommMagma (Cauchy α) where
  mul_comm a b := by
    induction a, b
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply mul_comm

instance : IsLeftDistrib (Cauchy α) where
  left_distrib k a b := by
    induction k, a, b
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply mul_add

instance : IsMonoid (Cauchy α) where
  mul_assoc a b c := by
    induction a, b, c
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply mul_assoc
  mul_one a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply mul_one
  one_mul a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply one_mul
  npow_zero a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply npow_zero
  npow_succ _ a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply npow_succ

instance : IsMulZeroClass (Cauchy α) where
  mul_zero a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply mul_zero
  zero_mul a := by
    induction a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i; apply zero_mul

instance : IsSemiring (Cauchy α) := IsSemiring.inst
instance : IsRing (Cauchy α) := IsRing.inst

end Cauchy
