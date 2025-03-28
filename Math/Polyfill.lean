def Decidable.not_and_iff_not_or_not {P Q: Prop} [Decidable P] [Decidable Q] : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
    apply Iff.intro
    intro h
    apply Decidable.or_iff_not_imp_left.mpr
    intro nnp q
    apply h
    apply And.intro _ q
    apply Decidable.byContradiction
    assumption
    intro h ⟨p, q⟩
    cases h <;> contradiction

def Classical.not_and_iff_not_or_not {P Q: Prop} : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
  Decidable.not_and_iff_not_or_not


protected def Int.zero_le_ofNat (a: Nat) : 0 ≤ (a: Int) := by simp

protected theorem Int.le_iff_lt_add_one {a b : Int} : a ≤ b ↔ a < b + 1 := by
  rw [Int.lt_iff_add_one_le]
  exact (Int.add_le_add_iff_right 1).symm

@[simp]
protected def Int.neg_lt_neg_iff {a b: Int} : -a < -b ↔ b < a := by omega
@[simp]
protected def Int.neg_le_neg_iff {a b: Int} : -a ≤ -b ↔ b ≤ a := by omega

protected def Int.sign_trichotomy (a : Int) : sign a = 1 ∨ sign a = 0 ∨ sign a = -1 := by
  match a with
  | 0 => simp
  | .ofNat (_ + 1) => simp
  | .negSucc _ => simp

@[simp] protected theorem Int.neg_le_zero_iff {a : Int} : -a ≤ 0 ↔ 0 ≤ a := by
  rw [← Int.neg_zero, Int.neg_le_neg_iff, Int.neg_zero]
