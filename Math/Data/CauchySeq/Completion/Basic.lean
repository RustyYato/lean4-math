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
def inv [DecidableEq α] : ∀a: Cauchy α, a ≠ 0 -> Cauchy α := by
  intro a
  refine Quotient.hrecOn a ?_ ?_
  all_goals clear a
  intro a ha
  have : ¬a ≈ 0 := by intro h; apply ha; apply Quotient.sound h
  exact ofSeq (a.inv this)
  intro a b h
  simp
  apply Function.hfunext
  rw [Quotient.sound h]
  intro h₀ h₁ heq
  simp
  apply Quotient.sound
  apply CauchySeq.inv.spec
  assumption
  intro h; apply h₀; apply Quotient.sound h

instance : Mul (Cauchy α) where
  mul := mul
instance : Pow (Cauchy α) ℕ where
  pow := flip npow

instance [DecidableEq α] : CheckedInv? (Cauchy α) where
  checked_invert := inv
instance [DecidableEq α] : CheckedDiv? (Cauchy α) where
  checked_div a b h := a * b⁻¹?
instance [DecidableEq α] : CheckedIntPow? (Cauchy α) :=
  instCheckedIntPow

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

instance : SMul α (Cauchy α) where
  smul a b := .of a * b
instance : AlgebraMap α (Cauchy α) where
  toFun := of
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

instance : IsAlgebra α (Cauchy α) where
  commutes _ _ := mul_comm _ _
  smul_def _ _ := rfl

instance : IsNontrivial (Cauchy α) where
  exists_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    have ⟨i, h⟩ := Quotient.exact h.symm 1 zero_lt_one
    have : ‖(1 - 0: α)‖ < 1 := h i i (le_refl _) (le_refl _)
    simp [norm_one] at this
    exact lt_irrefl this

instance (priority := 2000) [DecidableEq α] : FieldOps (Cauchy α) := inferInstance

instance [DecidableEq α] : IsField (Cauchy α) where
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl
  mul_inv?_cancel a h := by
    induction a with | ofSeq a =>
    apply Quotient.sound
    apply CauchySeq.eventually_pointwise
    have ⟨B, Bpos, i, hi⟩ := CauchySeq.norm_pos_of_not_zero a (by
      intro g; apply h; apply Quotient.sound g)
    exists i
    intro n hn
    show a n * a.safe_inv n = 1
    unfold CauchySeq.safe_inv; rw [dif_neg]
    rw [mul_inv?_cancel]
    intro h
    have : B ≤ ‖a n‖ - 0 := hi n hn
    simp [h, norm_zero, not_le_of_lt Bpos] at this

end Cauchy
