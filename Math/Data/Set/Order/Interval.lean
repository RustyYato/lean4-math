import Math.Data.Set.Like
import Math.Order.Preorder
import Math.Data.Set.Basic
import Math.Order.Lattice.Basic

namespace Set

section

variable [LE α] [LT α] [IsPreOrder α]

def Iii := Set.univ
def Iio (upper_bound: α) := mk fun x => x < upper_bound
def Iic (upper_bound: α) := mk fun x => x ≤ upper_bound
def Ioi (lower_bound: α) := mk fun x => lower_bound < x
def Ioo (lower_bound upper_bound: α) := Ioi lower_bound ∩ Iio upper_bound
def Ioc (lower_bound upper_bound: α) := Ioi lower_bound ∩ Iic upper_bound
def Ici (lower_bound: α) := mk fun x => lower_bound ≤ x
def Ico (lower_bound upper_bound: α) := Ici lower_bound ∩ Iio upper_bound
def Icc (lower_bound upper_bound: α) := Ici lower_bound ∩ Iic upper_bound

end

variable {x a b c d: α}

@[simp]
def mem_Iii : x ∈ Iii α := mem_univ _

@[simp]
def mem_Iio [LT α] : x ∈ Iio b ↔ x < b := Iff.rfl

@[simp]
def mem_Iic [LE α]: x ∈ Iic b ↔ x ≤ b := Iff.rfl

@[simp]
def mem_Ioi [LT α] : x ∈ Ioi a ↔ a < x := Iff.rfl

@[simp]
def mem_Ioo [LT α] : x ∈ Ioo a b ↔ a < x ∧ x < b := Iff.rfl

@[simp]
def mem_Ioc [LT α] [LE α] : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := Iff.rfl

@[simp]
def mem_Ici [LE α] : x ∈ Ici a ↔ a ≤ x := Iff.rfl

@[simp]
def mem_Ico [LT α] [LE α] : x ∈ Ico a b ↔ a ≤ x ∧ x < b := Iff.rfl

@[simp]
def mem_Icc [LE α] : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := Iff.rfl

instance decidableMemIii : Decidable (x ∈ Iii α) := inferInstanceAs (Decidable True)
instance decidableMemIio [LT α] [Decidable (x < b)] : Decidable (x ∈ Iio b) := by assumption
instance decidableMemIic [LE α] [Decidable (x ≤ b)] : Decidable (x ∈ Iic b) := by assumption

instance decidableMemIoi [LT α] [Decidable (a < x)] : Decidable (x ∈ Ioi a) := by assumption
instance decidableMemIoo [LT α] [Decidable (a < x ∧ x < b)] : Decidable (x ∈ Ioo a b) := by assumption
instance decidableMemIoc [LT α] [LE α] [Decidable (a < x ∧ x ≤ b)] : Decidable (x ∈ Ioc a b) := by assumption

instance decidableMemIci [LE α] [Decidable (a ≤ x)] : Decidable (x ∈ Ici a) := by assumption
instance decidableMemIco [LT α] [LE α] [Decidable (a ≤ x ∧ x < b)] : Decidable (x ∈ Ico a b) := by assumption
instance decidableMemIcc [LE α] [Decidable (a ≤ x ∧ x ≤ b)] : Decidable (x ∈ Icc a b) := by assumption

variable [LT α] [LE α] [IsPreOrder α]

def not_left_mem_Ioo : ¬a ∈ Ioo a b := by simp [lt_irrefl]
def not_right_mem_Ioo : ¬b ∈ Ioo a b := by simp [lt_irrefl]
def not_left_mem_Ioc : ¬a ∈ Ioc a b := by simp [lt_irrefl]
def not_right_mem_Ico : ¬b ∈ Ico a b := by simp [lt_irrefl]
def not_left_mem_Ioi : ¬a ∈ Ioi a := by simp [lt_irrefl]
def not_right_mem_Iio : ¬b ∈ Iio b := by simp [lt_irrefl]

def left_mem_Ici : a ∈ Ici a := le_refl _
def left_mem_Iic : a ∈ Iic a := le_refl _
def left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp
def right_mem_Ioc : b ∈ Ioc a b ↔ a < b := by simp
def left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp
def right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := by simp

def nonempty_Iii : (Iii α).Nonempty ↔ _root_.Nonempty α := by
  apply Iff.intro
  intro ⟨x, _⟩
  exact ⟨x⟩
  intro ⟨x⟩
  exact ⟨x, mem_univ _⟩
def nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty := by
  obtain ⟨x, _⟩ := exists_lt a
  exists x
def nonempty_Iic : (Iic a).Nonempty := by
  exists a
  simp
def nonempty_Ioi [NoMaxOrder α] : (Ioi a).Nonempty := by
  obtain ⟨x, _⟩ := exists_gt a
  exists x
def nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b := by
  apply Iff.intro
  intro ⟨x, _, _⟩
  apply lt_trans <;> assumption
  intro h
  have ⟨x, _, _⟩  := dense a b h
  exists x
def nonempty_Ioc [DenselyOrdered α] : (Ioc a b).Nonempty ↔ a < b := by
  apply Iff.intro
  intro ⟨x, _, _⟩
  apply lt_of_lt_of_le <;> assumption
  intro h
  have ⟨x, _, right⟩  := dense a b h
  exists x
  simpa [le_of_lt right]
def nonempty_Ici : (Ici a).Nonempty := by
  exists a
  simp
def nonempty_Ico [DenselyOrdered α] : (Ico a b).Nonempty ↔ a < b := by
  apply Iff.intro
  intro ⟨x, _, _⟩
  apply lt_of_le_of_lt <;> assumption
  intro h
  have ⟨x, left, _⟩  := dense a b h
  exists x
  simpa [le_of_lt left]
def nonempty_Icc : (Icc a b).Nonempty ↔ a ≤ b := by
  apply Iff.intro
  intro ⟨x, _, _⟩
  apply le_trans <;> assumption
  intro h
  exists a
  apply And.intro
  apply le_refl
  assumption

instance [NoMinOrder α] : NoMinOrder (Iio a) where
  exists_lt := by
    intro ⟨x, prf⟩
    have ⟨y, y_lt_x⟩ := exists_lt x
    refine ⟨⟨y, ?_⟩, ?_⟩
    exact lt_trans y_lt_x prf
    exact y_lt_x

instance [NoMinOrder α] : NoMinOrder (Iic a) where
  exists_lt := by
    intro ⟨x, prf⟩
    have ⟨y, y_lt_x⟩ := exists_lt x
    refine ⟨⟨y, ?_⟩, ?_⟩
    exact le_trans (le_of_lt y_lt_x) prf
    exact y_lt_x

instance [NoMaxOrder α] : NoMaxOrder (Ioi a) :=
  inferInstanceAs (NoMaxOrder (α := Opposite (Iio (Opposite.mk a))))

instance [NoMaxOrder α] : NoMaxOrder (Ici a) :=
  inferInstanceAs (NoMaxOrder (α := Opposite (Iic (Opposite.mk a))))


class _root_.IsInterval (I: Set α): Prop where
  isInterval: ∀⦃x y⦄, x ∈ I -> y ∈ I -> ∀z, x ≤ z -> z ≤ y -> z ∈ I

def isInterval (I: Set α) : Prop :=
  ∀⦃x y⦄, x ∈ I -> y ∈ I -> ∀z, x ≤ z -> z ≤ y -> z ∈ I

def mem_interval (I: Set α) [IsInterval I] : isInterval I :=
  IsInterval.isInterval

namespace isInterval

-- the intersection of two intervals is always an interval
instance (A B: Set α) [IsInterval A] [IsInterval B] : IsInterval (A ∩ B) where
  isInterval := by
    intro x y hx hy z x₀ y₀
    apply And.intro
    apply mem_interval
    apply hx.left
    apply hy.left
    assumption
    assumption
    apply mem_interval
    apply hx.right
    apply hy.right
    assumption
    assumption

-- the entire set is always an interval
instance : @IsInterval α _ ⊤ where
  isInterval := by
    intro x y hx hy z x₀ y₀
    trivial
-- the empty set is always an interval
instance : @IsInterval α _ ⊥ where
  isInterval := by
    intro x y hx hy z x₀ y₀
    trivial

variable {a b: α}

-- the above defined intervals are also intervals

instance : IsInterval (Set.Ici a) where
  isInterval := by
    intro x y hx hy z x₀ y₀
    show a ≤ _
    apply le_trans hx
    assumption
instance : IsInterval (Set.Ioi a) where
  isInterval := by
    intro x y hx hy z x₀ y₀
    show a < _
    apply lt_of_lt_of_le hx
    assumption
instance : IsInterval (Set.Iic a) where
  isInterval := by
    intro x y hx hy z x₀ y₀
    show _ ≤ a
    apply le_trans _ hy
    assumption
instance : IsInterval (Set.Iio a) where
  isInterval := by
    intro x y hx hy z x₀ y₀
    show _ < a
    apply lt_of_le_of_lt _ hy
    assumption

instance : IsInterval (Set.Icc a b) := inferInstanceAs (IsInterval (_ ∩ _))
instance : IsInterval (Set.Ico a b) := inferInstanceAs (IsInterval (_ ∩ _))
instance : IsInterval (Set.Ioc a b) := inferInstanceAs (IsInterval (_ ∩ _))
instance : IsInterval (Set.Ioo a b) := inferInstanceAs (IsInterval (_ ∩ _))

end isInterval

end Set
