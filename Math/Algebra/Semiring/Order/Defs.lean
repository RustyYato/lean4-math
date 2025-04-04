import Math.Algebra.Monoid.Order.Defs
import Math.Algebra.Semiring.Defs

class IsOrderedNonUnitalNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] [LT α] [LE α] extends IsNonUnitalNonAssocSemiring α, IsOrderedAddCommMonoid α where
  mul_nonneg: ∀a b: α, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b
  mul_le_mul_of_nonneg_left: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b
  mul_le_mul_of_nonneg_right: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> a * c ≤ b * c

class IsOrderedSemiring (α: Type*) [SemiringOps α] [LT α] [LE α] extends IsSemiring α, IsOrderedNonUnitalNonAssocSemiring α, IsZeroLeOne α where

instance [SemiringOps α] [LT α] [LE α]
  [hs: IsSemiring α] [ho: IsOrderedNonUnitalNonAssocSemiring α] [IsZeroLeOne α]
  : IsOrderedSemiring α := { hs, ho with }

class IsStrictOrderedNonUnitalNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] [LT α] [LE α] extends IsOrderedNonUnitalNonAssocSemiring α where
  mul_pos: ∀a b: α, 0 < a -> 0 < b -> 0 < a * b

class IsStrictOrderedSemiring (α: Type*) [SemiringOps α] [LT α] [LE α] extends
  IsOrderedSemiring α, IsStrictOrderedNonUnitalNonAssocSemiring α where

instance [SemiringOps α] [LT α] [LE α]
  [hs: IsOrderedSemiring α] [ho: IsStrictOrderedNonUnitalNonAssocSemiring α]
  : IsStrictOrderedSemiring α := { hs, ho with }

instance : IsStrictOrderedSemiring Nat where
  zero_le_one := Nat.zero_le 1
  add_le_add_left _ _ := Nat.add_le_add_left
  mul_pos := by apply Nat.mul_pos
  mul_nonneg := by exact fun a b a_1 a_2 => Nat.zero_le _
  mul_le_mul_of_nonneg_left := fun a b a_1 c a_2 => Nat.mul_le_mul_left c a_1
  mul_le_mul_of_nonneg_right := fun a b a_1 c a_2 => Nat.mul_le_mul_right c a_1

instance : IsStrictOrderedSemiring Int where
  zero_le_one := by exact Int.zero_le_ofNat 1
  add_le_add_left _ _ := Int.add_le_add_left
  mul_pos := by apply Int.mul_pos
  mul_nonneg := by exact fun a b a_1 a_2 => Int.mul_nonneg a_1 a_2
  mul_le_mul_of_nonneg_left := fun a b a_1 c a_2 => Int.mul_le_mul_of_nonneg_left a_1 a_2
  mul_le_mul_of_nonneg_right := fun a b a_1 c a_2 => by exact Int.mul_le_mul_of_nonneg_right a_1 a_2

section

variable [AddMonoidOps α] [Mul α] [LT α] [LE α] [IsOrderedNonUnitalNonAssocSemiring α]

def mul_nonneg: ∀a b: α, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b := IsOrderedNonUnitalNonAssocSemiring.mul_nonneg
def mul_le_mul_of_nonneg_left: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b := IsOrderedNonUnitalNonAssocSemiring.mul_le_mul_of_nonneg_left
def mul_le_mul_of_nonneg_right: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> a * c ≤ b * c := IsOrderedNonUnitalNonAssocSemiring.mul_le_mul_of_nonneg_right

end

section

variable [AddMonoidOps α] [Mul α] [LT α] [LE α] [IsStrictOrderedNonUnitalNonAssocSemiring α]

def mul_pos: ∀a b: α, 0 < a -> 0 < b -> 0 < a * b := IsStrictOrderedNonUnitalNonAssocSemiring.mul_pos

end

section

variable [SemiringOps α] [LE α] [LT α] [IsOrderedSemiring α]
  [IsNontrivial α]

def natCast_nonneg (n: ℕ) : 0 ≤ (n: α) := by
  induction n with
  | zero => rw [natCast_zero]
  | succ n ih =>
    rw [natCast_succ, ←add_zero 0]
    apply add_le_add
    assumption
    apply zero_le_one

def natCast_monotone : Monotone (Nat.cast (R := α)) := by
  intro a b h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [natCast_add]
  rw (occs := [1]) [←add_zero (a: α)]
  apply add_le_add_left
  apply natCast_nonneg

def natCast_pos (n: ℕ) (h: 0 < n) : 0 < (n: α) := by
  cases n; contradiction; clear h
  rename_i n
  apply lt_of_lt_of_le
  apply zero_lt_one
  rw [←natCast_one]
  apply natCast_monotone
  exact Nat.le_add_left 1 n

instance (n: ℕ) [NeZero n] : NeZero (n: α) where
  out := by
    intro h
    have := natCast_pos (α := α) n
    rw [h] at this
    simp [lt_irrefl] at this
    have := NeZero.ne n
    contradiction

instance instNeZeroOfOrderedSemiring (n: ℕ) [Nat.AtLeastTwo n] : NeZero (OfNat.ofNat n: α) := by
  rw [ofNat_eq_natCast]
  have := two_le n
  match n with | n + 2 => infer_instance

instance : NeZero (2: α) := instNeZeroOfOrderedSemiring 2
instance : NeZero (3: α) := instNeZeroOfOrderedSemiring 3
instance : NeZero (4: α) := instNeZeroOfOrderedSemiring 4

def two_pos : 0 < (2: α) := by
  apply natCast_pos
  apply Nat.zero_lt_succ

def natCast_strictmonotone [IsAddCancel α] : StrictMonotone (Nat.cast (R := α)) := by
  intro a b h
  replace h := (Nat.succ_le_of_lt h)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [natCast_add]
  apply flip lt_of_lt_of_le
  apply add_le_add
  rfl
  apply natCast_nonneg
  rw [add_zero]
  clear h k
  rw [←add_zero (a: α), natCast_succ]
  apply add_lt_add_left
  apply zero_lt_one

end

instance [SemiringOps α] [LT α] [LE α] [IsOrderedSemiring α]
  : IsOrderedAddCommMonoid α := inferInstance
