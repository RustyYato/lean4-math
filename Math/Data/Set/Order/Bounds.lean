import Math.Order.Preorder
import Math.Data.Set.Order.Interval

namespace Set

variable [LE α] [LT α] [IsPreOrder α]

def lowerBounds (s: Set α) : Set α := mk fun b => ∀a ∈ s, b ≤ a
def upperBounds (s: Set α) : Set α := mk fun b => ∀a ∈ s, a ≤ b

def BoundedAbove (s: Set α): Prop := (upperBounds s).Nonempty
def BoundedBelow (s: Set α): Prop := (lowerBounds s).Nonempty

def IsLeast (s: Set α) (x: α) := x ∈ s ∧ x ∈ lowerBounds s
def IsGreatest (s: Set α) (x: α) := x ∈ s ∧ x ∈ upperBounds s

def IsLUB (s: Set α) (x: α) := IsLeast (upperBounds s) x
def IsGLB (s: Set α) (x: α) := IsGreatest (lowerBounds s) x

def mem_lowerBounds {s: Set α} : ∀{x}, x ∈ lowerBounds s ↔ ∀a ∈ s, x ≤ a := Iff.rfl
def mem_upperBounds {s: Set α} : ∀{x}, x ∈ upperBounds s ↔ ∀a ∈ s, a ≤ x := Iff.rfl

variable {a b x: α} {s: Set α}

def BoundedAbove.dual (h: BoundedAbove s) : BoundedBelow (s.preimage Opposite.get) := h
def BoundedBelow.dual (h: BoundedBelow s) : BoundedAbove (s.preimage Opposite.get) := h
def IsLeast.dual (h: IsLeast s x) : IsGreatest (s.preimage Opposite.get) (Opposite.mk x) := h
def IsGreatest.dual (h: IsGreatest s x) : IsLeast (s.preimage Opposite.get) (Opposite.mk x) := h
def IsLUB.dual (h: IsLUB s x) : IsGLB (s.preimage Opposite.get) (Opposite.mk x) := h
def IsGLB.dual (h: IsGLB s x) : IsLUB (s.preimage Opposite.get) (Opposite.mk x) := h

def upperBounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : a ∈ upperBounds s → b ∈ upperBounds s :=
  fun ha _ h => le_trans (ha _ h) hab

def lowerBounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : b ∈ lowerBounds s → a ∈ lowerBounds s :=
  fun hb _ h => le_trans hab (hb _ h)

def IsLeast.isGLB (h: IsLeast s x) : IsGLB s x := by
  apply And.intro
  rw [mem_lowerBounds]
  intro y g
  exact h.right y g
  intro y mem
  apply mem
  exact h.left

def IsGreatest.isLUB (h: IsGreatest s x) : IsLUB s x :=
  h.dual.isGLB

def IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds s = Ici a := by
  obtain ⟨h, h'⟩ := h
  ext x
  simp [mem_upperBounds]
  apply Iff.intro
  intro g
  apply h'
  assumption
  intro g y y_in_s
  apply le_trans _ g
  apply h
  assumption

def IsGLB.lowerBounds_eq (h : IsGLB s a) : lowerBounds s = Iic a :=
  h.dual.upperBounds_eq

def IsLeast.lowerBounds_eq (h : IsLeast s a) : lowerBounds s = Iic a :=
  h.isGLB.lowerBounds_eq

def IsGreatest.upperBounds_eq (h : IsGreatest s a) : upperBounds s = Ici a :=
  h.isLUB.upperBounds_eq

def isLeast_Ici (a: α) : IsLeast (Ici a) a := by
  apply And.intro <;> simp [mem_lowerBounds]

def isLeast_Icc (h: a ≤ b) : IsLeast (Icc a b) a := by
  apply And.intro <;> simp [mem_lowerBounds, h]
  intros; assumption

def isLeast_Ico (h: a < b) : IsLeast (Ico a b) a := by
  apply And.intro <;> simp [mem_lowerBounds, h]
  intros; assumption

def isGreatest_Iic (a: α) : IsGreatest (Iic a) a :=
  IsLeast.dual (isLeast_Ici (Opposite.mk a))

def isGreatest_Icc (h: a ≤ b) : IsGreatest (Icc a b) b := by
  apply And.intro <;> simp [mem_upperBounds, h]

def isGreatest_Ioc (h: a < b) : IsGreatest (Ioc a b) b := by
  apply And.intro <;> simp [mem_upperBounds, h]

def isGLB_Ici (a: α) : IsGLB (Ici a) a := (isLeast_Ici a).isGLB
def isGLB_Ico (h: a < b) : IsGLB (Ico a b) a := (isLeast_Ico h).isGLB
def isGLB_Icc (h: a ≤ b) : IsGLB (Icc a b) a := (isLeast_Icc h).isGLB

def isLUB_Iic (a: α) : IsLUB (Iic a) a := (isGreatest_Iic a).isLUB
def isLUB_Ioc (h: a < b) : IsLUB (Ioc a b) b := (isGreatest_Ioc h).isLUB
def isLUB_Icc (h: a ≤ b) : IsLUB (Icc a b) b := (isGreatest_Icc h).isLUB

def isLUB_le_iff (h : IsLUB s a) : a ≤ b ↔ b ∈ upperBounds s := by
  rw [h.upperBounds_eq]
  rfl

def le_isGLB_iff (h : IsGLB s a) : b ≤ a ↔ b ∈ lowerBounds s :=
  isLUB_le_iff (α := Opposite α) h

def BoundedAbove.empty : BoundedAbove (∅: Set α) := by
  exists a
  intro x mem
  contradiction

def BoundedAbove.singleton (a: α) : BoundedAbove {a} := by
  exists a
  intro x mem
  cases mem
  rfl

def BoundedBelow.empty : BoundedBelow (∅: Set α) := by
  exists a
  intro x mem
  contradiction

def BoundedBelow.singleton (a: α) : BoundedBelow {a} := by
  exists a
  intro x mem
  cases mem
  rfl

def allBoundedAbove [LE α] [Top α] [IsLawfulTop α] (s: Set α) : Set.BoundedAbove s := by
  exists ⊤
  intro x mem
  apply le_top

def allBoundedBelow [LE α] [Bot α] [IsLawfulBot α] (s: Set α) : Set.BoundedBelow s := by
  exists ⊥
  intro x mem
  apply bot_le

section

variable [IsPartialOrder α] {a b: α}

def IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b :=
  le_antisymm (Ha.right _ Hb.left) (Hb.right _ Ha.left)

def IsLeast.isLeast_iff_eq (Ha : IsLeast s a) : IsLeast s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha

def IsGreatest.unique (Ha : IsGreatest s a) (Hb : IsGreatest s b) : a = b :=
  IsLeast.unique (α := Opposite α) Ha Hb

def IsGreatest.isGreatest_iff_eq (Ha : IsGreatest s a) : IsGreatest s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha

def IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b :=
  IsLeast.unique Ha Hb

def IsGLB.unique (Ha : IsGLB s a) (Hb : IsGLB s b) : a = b :=
  IsGreatest.unique Ha Hb

def IsLeast.nonempty (h: IsLeast s a) : s.Nonempty := ⟨a, h.left⟩
def IsGreatest.nonempty (h: IsGreatest s a) : s.Nonempty := ⟨a, h.left⟩

end

end Set
