import Math.Data.Real.Div

@[ext]
structure Complex where
  real: ℝ
  img: ℝ

notation "ℂ" => Complex

namespace Complex

def conj (c: ℂ) : ℂ where
  real := c.real
  img := -c.img

def mag_sq (c: ℂ) : ℝ :=
  c.real * c.real + c.img * c.img

instance : Coe ℝ ℂ where
  coe := (Complex.mk · 0)

instance : OfNat ℂ n where
  ofNat := (OfNat.ofNat n: ℝ)

instance : NatCast ℂ where
  natCast n := (n: ℝ)

instance : IntCast ℂ where
  intCast n := (n: ℝ)

instance : Nonempty ℂ := ⟨0⟩
instance : Inhabited ℂ := ⟨0⟩

@[simp]
def ofNat_real (n: ℕ) : (OfNat.ofNat (α := ℂ) n).real = OfNat.ofNat n := rfl
@[simp]
def ofNat_img (n: ℕ) : (OfNat.ofNat (α := ℂ) n).img = 0 := rfl

@[simp]
def zero_real : (Zero.toOfNat0 (α := ℂ).ofNat).real = 0 := rfl
@[simp]
def zero_img : (Zero.toOfNat0 (α := ℂ).ofNat).img = 0 := rfl

@[simp]
def one_real : (One.ofNat.ofNat: ℂ).real = 1 := rfl
@[simp]
def one_img : (One.ofNat.ofNat: ℂ).img = 0 := rfl

@[simp]
def natCast_real (n: ℕ) : (n: ℂ).real = n := rfl
@[simp]
def natCast_img (n: ℕ) : (n: ℂ).img = 0 := rfl

@[simp]
def intCast_real (n: ℤ) : (n: ℂ).real = n := rfl
@[simp]
def intCast_img (n: ℤ) : (n: ℂ).img = 0 := rfl

@[simp]
def natCast_coe (n: ℕ) : ((n: ℝ): ℂ).real = n := rfl

def mag_sq_nonzero (c: ℂ) (h: c ≠ 0) : c.mag_sq ≠ 0 := by
  intro g
  apply h; clear h
  unfold mag_sq at g
  replace g := neg_eq_of_add_left g
  ext
  have := Real.square_nonneg c.img
  rw [←g, ←Real.neg_le_neg_iff, neg_neg, neg_zero] at this
  exact Real.eq_zero_of_square_eq_zero _ <| le_antisymm this (Real.square_nonneg c.real)
  have := Real.square_nonneg c.real
  rw [←Real.neg_le_neg_iff, g, neg_zero] at this
  exact Real.eq_zero_of_square_eq_zero _ <| le_antisymm this (Real.square_nonneg c.img)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply mag_sq_nonzero; invert_tactic)

instance : Add ℂ where
  add a b := ⟨a.real + b.real, a.img + b.img⟩

@[simp]
def add_real (a b: ℂ) : (a + b).real = a.real + b.real := rfl
@[simp]
def add_img (a b: ℂ) : (a + b).img = a.img + b.img := rfl

instance : Neg ℂ where
  neg a := ⟨-a.real, -a.img⟩

@[simp]
def neg_real (a: ℂ) : (-a).real = -a.real := rfl
@[simp]
def neg_img (a: ℂ) : (-a).img = -a.img := rfl

instance : Sub ℂ where
  sub a b := ⟨a.real - b.real, a.img - b.img⟩

@[simp]
def sub_real (a b: ℂ) : (a - b).real = a.real - b.real := rfl
@[simp]
def sub_img (a b: ℂ) : (a - b).img = a.img - b.img := rfl

instance : Mul ℂ where
  mul a b := ⟨a.real * b.real - a.img * b.img, a.real * b.img + a.img * b.real⟩

@[simp]
def mul_real (a b: ℂ) : (a * b).real = a.real * b.real - a.img * b.img := rfl
@[simp]
def mul_img (a b: ℂ) : (a * b).img = a.real * b.img + a.img * b.real := rfl

instance : CheckedInv? ℂ where
  checked_invert a h := {
    real := a.real /? a.mag_sq
    img := -a.img /? a.mag_sq
  }

@[simp]
def inv_real (a: ℂ) (h: a ≠ 0) : (a⁻¹?).real = a.real /? a.mag_sq := rfl
@[simp]
def inv_img (a: ℂ) (h: a ≠ 0) : (a⁻¹?).img = -a.img /? a.mag_sq := rfl

def i : ℂ := ⟨0, 1⟩

@[simp]
def real_i : real i = 0 := rfl
@[simp]
def img_i : img i = 1 := rfl

instance : CheckedDiv? ℂ where
  checked_div a b h := a * b⁻¹?

instance : SMul ℕ ℂ where
  smul n a := n * a

def nsmul_def (n: ℕ) (a: ℂ) : n • a = n * a := rfl

instance : SMul ℤ ℂ where
  smul a b := a * b

def zsmul_def (n: ℤ) (a: ℂ) : n • a = n * a := rfl

instance : Pow ℂ ℕ where
  pow := flip npowRec

instance : CheckedIntPow? ℂ where
  checked_pow := zpow?Rec (α := ℂ)

end Complex
