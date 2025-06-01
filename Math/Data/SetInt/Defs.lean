import Math.Algebra.Hom.Defs
import Math.Algebra.Ring.Hom
import Math.Function.Basic
import Math.Data.Int.Basic

def SetInt.Pre := ℕ × ℕ

def SetInt.setoid : Setoid SetInt.Pre where
  r a b := a.1 + b.2 = b.1 + a.2
  iseqv := {
    refl _ := rfl
    symm h := h.symm
    trans := by
      intro x y z h g
      apply add_left_cancel (k := y.snd)
      rw [show y.snd + (x.fst + z.snd) = (x.fst + y.snd + z.snd) by ac_rfl, h]
      rw [add_comm_right, g]; ac_rfl
  }

def SetInt := Quotient SetInt.setoid

namespace SetInt

def mk : ℕ -> ℕ -> SetInt := fun a b => Quotient.mk _ (a, b)

def ind {motive: SetInt -> Prop} (mk: ∀a b, motive (mk a b)) (s: SetInt) : motive s := by
  induction s using Quotient.ind with | _ s =>
  apply mk s.1 s.2

def lift (f: ℕ -> ℕ -> α) (resp: ∀a b c d, a + d = c + b -> f a b = f c d) : SetInt -> α := by
  refine Quotient.lift (fun x => f x.1 x.2) ?_
  intro a b h
  exact resp _ _ _ _ h

def lift₂ (f: ℕ -> ℕ -> ℕ -> ℕ -> α) (resp: ∀a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁, a₀ + b₁ = a₁ + b₀ -> c₀ + d₁ = c₁ + d₀ -> f a₀ b₀ c₀ d₀ = f a₁ b₁ c₁ d₁) : SetInt -> SetInt -> α := by
  refine Quotient.lift₂ (fun x y => f x.1 x.2 y.1 y.2) ?_
  intro a b c d h g
  exact resp _ _ _ _ _ _ _ _ h g

@[simp] def lift_mk : lift f resp (mk a b) = f a b := rfl

def sound (a b c d: ℕ) : a + d = c + b -> mk a b = mk c d := by
  intro h
  apply Quotient.sound
  assumption

def add : SetInt -> SetInt -> SetInt := by
  refine lift₂ ?_ ?_
  intro a b c d
  exact mk (a + c) (b + d)
  intro a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ h g
  apply sound
  rw [show a₀ + c₀ + (b₁ + d₁) = a₀ + b₁ + (c₀ + d₁) by ac_rfl]
  rw [h, g]
  ac_rfl

def mul : SetInt -> SetInt -> SetInt := by
  refine lift₂ ?_ ?_
  intro a b c d
  exact mk (a * c + b * d) (a * d + b * c)
  intro a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ h g
  apply sound
  apply add_left_cancel (k := b₁ * c₀)
  repeat rw [←add_assoc (b₁ * c₀)]
  rw [←add_mul, add_comm b₁]
  rw [←add_comm_right (b₁ * c₀), ←mul_add]
  rw [h, g]
  rw [add_mul, mul_add]
  ac_nf
  rw [add_left_comm _ (b₀ * c₀)]; congr 1
  repeat rw [←add_assoc]
  congr 1
  rw [mul_comm c₀, add_assoc, ←mul_add, g, mul_add, add_left_comm, ←add_mul, add_comm b₀, ←h, add_mul]
  ac_nf

def neg : SetInt -> SetInt := by
  refine lift ?_ ?_
  intro a b; exact mk b a
  intro a b c d h
  apply sound
  rw [add_comm b, add_comm d, h]

instance : Add SetInt where
  add := add
instance : Mul SetInt where
  mul := mul
instance : Neg SetInt where
  neg := neg
instance : Sub SetInt where
  sub a b := a + -b

instance : NatCast SetInt where
  natCast n := mk n 0
instance : IntCast SetInt := ⟨intCastRec⟩
instance : OfNat SetInt n := ⟨n⟩

instance : SMul ℕ SetInt where
  smul n x := n * x
instance : SMul ℤ SetInt where
  smul n x := n * x
instance : Pow SetInt ℕ where
  pow := flip npowRec

instance : IsAddSemigroup SetInt where
  add_assoc a b c := by
    induction a using ind with | mk a₀ a₁ =>
    induction b using ind with | mk b₀ b₁ =>
    induction c using ind with | mk c₀ c₁ =>
    apply sound
    dsimp
    ac_nf
instance : IsAddCommMagma SetInt where
  add_comm a b := by
    induction a using ind with | mk a₀ a₁ =>
    induction b using ind with | mk b₀ b₁ =>
    apply sound
    dsimp
    ac_nf

instance : IsCommMagma SetInt where
  mul_comm a b := by
    induction a using ind with | mk a₀ a₁ =>
    induction b using ind with | mk b₀ b₁ =>
    apply sound
    dsimp
    ac_nf
instance : IsSemigroup SetInt where
  mul_assoc a b c := by
    induction a using ind with | mk a₀ a₁ =>
    induction b using ind with | mk b₀ b₁ =>
    induction c using ind with | mk c₀ c₁ =>
    apply sound
    simp [add_mul, mul_add]
    ac_nf

instance : IsMulZeroClass SetInt where
  zero_mul a := by
    induction a using ind
    apply sound
    simp
  mul_zero a := by
    induction a using ind
    apply sound
    simp

instance : IsLeftDistrib SetInt where
  mul_add k a b := by
    induction a using ind with | mk a₀ a₁ =>
    induction b using ind with | mk b₀ b₁ =>
    induction k using ind with | mk k₀ k₁ =>
    apply sound
    simp [add_mul, mul_add]
    ac_nf

instance : IsMonoid SetInt where
  mul_one a := by
    induction a using ind
    apply sound
    simp
  one_mul a := by
    induction a using ind
    apply sound
    simp

instance : IsAddGroupWithOne SetInt where
  zero_add a := by
    induction a using ind
    apply sound
    simp
  add_zero a := by
    induction a using ind
    apply sound
    simp
  sub_eq_add_neg _ _ := rfl
  neg_add_cancel a := by
    induction a using ind
    apply sound
    simp
    rw [add_comm]
  zsmul_ofNat n a := by
    induction a using ind
    apply sound
    simp
  zsmul_negSucc n a := by
    induction a using ind
    apply sound
    simp
  zero_nsmul a := by
    induction a using ind
    apply sound
    simp
  succ_nsmul n a := by
    induction a using ind
    apply sound
    simp [add_mul]
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

instance : IsRing SetInt where

-- prove that SetInt (the quotient of pairs of nats)
-- is equivalent to the normal integers in the obvious way
def equiv_int : SetInt ≃+* ℤ := RingEquiv.symm {
  RingHom.intCast with
  invFun := by
    refine lift ?_ ?_
    intro a b
    exact a - b
    intro a b c  d h
    apply eq_of_sub_eq_zero
    rw [sub_sub, sub_eq_add_neg (a: ℤ), add_comm_right, sub_eq_add_neg,
      add_assoc, ←neg_add_rev, ←natCast_add, ←natCast_add, h, add_neg_cancel]
  leftInv x := by
    simp; cases x <;> rfl
  rightInv x := by
    induction x using ind
    simp
    rw [←intCast_sub, intCast_ofNat, intCast_ofNat, sub_eq_add_neg]
    show mk (_ + 0) (0 + _) = _
    simp
}

end SetInt
