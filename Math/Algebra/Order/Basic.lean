import Math.Order.Covariant.Defs
import Math.Order.Defs

section Abbreviations

variable (α : Type*) [Mul α] [Zero α] [LT α] [LE α]

private abbrev nonneg := { x : α // 0 ≤ x }
private abbrev pos := { x : α // 0 < x }

instance [h: IsLawfulLT α] : Coe (pos α) (nonneg α) where
  coe x := ⟨x, (h.lt_iff_le_and_not_le.mp x.property).left⟩

abbrev PosMulLE : Prop :=
  @CovariantClass (nonneg α) α (fun x y => x * y) (· ≤ ·)
abbrev MulPosLE : Prop :=
  @CovariantClass (nonneg α) α (fun x y => y * x) (· ≤ ·)

abbrev PosMulLT : Prop :=
  @CovariantClass (pos α) α (fun x y => x * y) (· < ·)
abbrev MulPosLT : Prop :=
  @CovariantClass (pos α) α (fun x y => y * x) (· < ·)

abbrev PosMulReflectLT : Prop :=
  @ContravariantClass (nonneg α) α (fun x y => x * y) (· < ·)
abbrev MulPosReflectLT : Prop :=
  @ContravariantClass (nonneg α) α (fun x y => y * x) (· < ·)

abbrev PosMulReflectLE : Prop :=
  @ContravariantClass (pos α) α (fun x y => x * y) (· ≤ ·)
abbrev MulPosReflectLE : Prop :=
  @ContravariantClass (pos α) α (fun x y => y * x) (· ≤ ·)

variable [IsLawfulLT α]

instance [h: PosMulLE α] : @CovariantClass (pos α) α (fun x y => x * y) (· ≤ ·) where
  elim g _ _ x := h.elim g x
instance [h: MulPosLE α] : @CovariantClass (pos α) α (fun x y => y * x) (· ≤ ·) where
  elim g _ _ x := h.elim g x

instance inst₃ [h: PosMulReflectLT α] : @ContravariantClass (pos α) α (fun x y => x * y) (· < ·) where
  elim g _ _ x := h.elim g x
instance [h: MulPosReflectLT α] : @ContravariantClass (pos α) α (fun x y => y * x) (· < ·) where
  elim g _ _ x := h.elim g x

end Abbreviations

variable {α : Type*} [Mul α] [Zero α] [LT α] [LE α]

section Preorder

variable {a b c: α}

def mul_le_mul_of_nonneg_left [g: PosMulLE α] (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c :=
  g.elim ⟨_, a0⟩ h
def mul_le_mul_of_nonneg_right [g: MulPosLE α] (h : b ≤ c) (a0 : 0 ≤ a) : b * a ≤ c * a :=
  g.elim ⟨_, a0⟩ h

def mul_lt_mul_of_pos_left [g: PosMulLT α] (h : b < c) (a0 : 0 < a) : a * b < a * c :=
  g.elim ⟨_, a0⟩ h
def mul_lt_mul_of_pos_right [g: MulPosLT α] (h : b < c) (a0 : 0 < a) : b * a < c * a :=
  g.elim ⟨_, a0⟩ h

def le_of_mul_le_mul_left [g: PosMulReflectLE α] (h : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
  g.elim ⟨_, a0⟩ h
def le_of_mul_le_mul_right [g: MulPosReflectLE α] (h : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
  g.elim ⟨_, a0⟩ h

def lt_of_mul_lt_mul_left [g: PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 ≤ a) : b < c :=
  g.elim ⟨_, a0⟩ h
def lt_of_mul_lt_mul_right [g: MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 ≤ a) : b < c :=
  g.elim ⟨_, a0⟩ h

section

variable [IsLawfulLT α]

def mul_lt_mul_left [PosMulLT α] [PosMulReflectLT α] (a0 : 0 < a) :
  a * b < a * c ↔ b < c :=
  @rel_iff_cov (pos α) α (fun x y => x * y) (· < ·) _ _ ⟨_, a0⟩ _ _

def mul_lt_mul_right [MulPosLT α] [MulPosReflectLT α] (a0 : 0 < a) :
  b * a < c * a ↔ b < c :=
  @rel_iff_cov (pos α) α (fun x y => y * x) (· < ·) _ _ ⟨_, a0⟩ _ _

def mul_le_mul_left [PosMulLE α] [PosMulReflectLE α] (a0 : 0 < a) :
  a * b ≤ a * c ↔ b ≤ c :=
  @rel_iff_cov (pos α) α (fun x y => x * y) (· ≤ ·) _ _ ⟨_, a0⟩ _ _

def mul_le_mul_right [MulPosLE α] [MulPosReflectLE α] (a0 : 0 < a) :
  b * a ≤ c * a ↔ b ≤ c :=
  @rel_iff_cov (pos α) α (fun x y => y * x) (· ≤ ·) _ _ ⟨_, a0⟩ _ _


end

variable [IsPreOrder α]

def mul_le_mul_of_nonneg [PosMulLE α] [MulPosLE α]
    (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 ≤ d) : a * c ≤ b * d :=
  trans (mul_le_mul_of_nonneg_left h₂ a0) (mul_le_mul_of_nonneg_right h₁ d0)

def mul_le_mul_of_nonneg' [PosMulLE α] [MulPosLE α]
    (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d :=
  trans (mul_le_mul_of_nonneg_right h₁ c0) (mul_le_mul_of_nonneg_left h₂ b0)

def mul_lt_mul_of_le_of_lt_of_pos_of_nonneg [PosMulLT α] [MulPosLE α]
    (h₁ : a ≤ b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 ≤ d) : a * c < b * d :=
  trans (mul_lt_mul_of_pos_left h₂ a0) (mul_le_mul_of_nonneg_right h₁ d0)

def mul_lt_mul_of_le_of_lt_of_nonneg_of_pos [PosMulLT α] [MulPosLE α]
    (h₁ : a ≤ b) (h₂ : c < d) (c0 : 0 ≤ c) (b0 : 0 < b) : a * c < b * d :=
  trans (mul_le_mul_of_nonneg_right h₁ c0) (mul_lt_mul_of_pos_left h₂ b0)

def mul_lt_mul_of_lt_of_le_of_nonneg_of_pos [PosMulLE α] [MulPosLT α]
    (h₁ : a < b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 < d) : a * c < b * d :=
  trans (mul_le_mul_of_nonneg_left h₂ a0) (mul_lt_mul_of_pos_right h₁ d0)

def mul_lt_mul_of_lt_of_le_of_pos_of_nonneg [PosMulLE α] [MulPosLT α]
    (h₁ : a < b) (h₂ : c ≤ d) (c0 : 0 < c) (b0 : 0 ≤ b) : a * c < b * d :=
  trans (mul_lt_mul_of_pos_right h₁ c0) (mul_le_mul_of_nonneg_left h₂ b0)

def mul_lt_mul_of_pos [PosMulLT α] [MulPosLT α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
  trans (mul_lt_mul_of_pos_left h₂ a0) (mul_lt_mul_of_pos_right h₁ d0)

def mul_lt_mul_of_pos' [PosMulLT α] [MulPosLT α]
    (h₁ : a < b) (h₂ : c < d) (c0 : 0 < c) (b0 : 0 < b) : a * c < b * d :=
  trans (mul_lt_mul_of_pos_right h₁ c0) (mul_lt_mul_of_pos_left h₂ b0)

end Preorder
