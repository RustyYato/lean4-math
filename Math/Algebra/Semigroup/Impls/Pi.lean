import Math.Algebra.Semigroup.Defs

section Pi.Operators

-- just define all operators pointwise here, we can't implement IsGroupWithZero
-- so we don't need any of the checked operators

variable {ι: Type*} {α: ι -> Type*}

instance [∀i, Zero (α i)] : Zero (∀i, α i) where
  zero _ := 0
instance [∀i, One (α i)] : One (∀i, α i) where
  one _ := 1
instance [∀i, NatCast (α i)] : NatCast (∀i, α i) where
  natCast n _ := n
instance [∀i, IntCast (α i)] : IntCast (∀i, α i) where
  intCast n _ := n

instance [∀i, Add (α i)] : Add (∀i, α i) where
  add f g i := f i + g i

instance [∀i, Sub (α i)] : Sub (∀i, α i) where
  sub f g i := f i - g i

instance [∀i, Mul (α i)] : Mul (∀i, α i) where
  mul f g i := f i * g i

instance [∀i, Div (α i)] : Div (∀i, α i) where
  div f g i := f i / g i

instance [∀i, SMul R (α i)] : SMul R (∀i, α i) where
  smul n f i := n • f i

instance [∀i, Pow (α i) ℕ] : Pow (∀i, α i) ℕ where
  pow f n i := f i ^ n

instance [∀i, Pow (α i) ℤ] : Pow (∀i, α i) ℤ where
  pow f n i := f i ^ n

instance [∀i, Neg (α i)] : Neg (∀i, α i) where
  neg f i := -f i

instance [∀i, Inv (α i)] : Inv (∀i, α i) where
  inv f i := (f i)⁻¹

def Pi.zero_eq [∀i, Zero (α i)] : (0: ∀i, α i) = fun _ => 0 := rfl
def Pi.one_eq [∀i, One (α i)] : (1: ∀i, α i) = fun _ => 1 := rfl
def Pi.natCast_eq [∀i, NatCast (α i)] (n: ℕ): (n: ∀i, α i) = fun _ => (n: α _) := rfl
def Pi.intCast_eq [∀i, IntCast (α i)] (n: ℤ): (n: ∀i, α i) = fun _ => (n: α _) := rfl
def Pi.add_eq [∀i, Add (α i)] (f g: ∀i, α i): f + g = fun x => f x + g x := rfl
def Pi.mul_eq [∀i, Mul (α i)] (f g: ∀i, α i): f * g = fun x => f x * g x := rfl
def Pi.sub_eq [∀i, Sub (α i)] (f g: ∀i, α i): f - g = fun x => f x - g x := rfl
def Pi.div_eq [∀i, Div (α i)] (f g: ∀i, α i): f / g = fun x => f x / g x := rfl
def Pi.smul_eq [∀i, SMul R (α i)] (r: R) (f: ∀i, α i): r • f = fun x => r • f x := rfl
def Pi.npow_eq [∀i, Pow (α i) ℕ] (f: ∀i, α i) (n: ℕ): f ^ n = fun x => f x ^ n := rfl
def Pi.zpow_eq [∀i, Pow (α i) ℤ] (f: ∀i, α i) (n: ℤ): f ^ n = fun x => f x ^ n := rfl
def Pi.neg_eq [∀i, Neg (α i)] (f: ∀i, α i): -f = fun x => -f x := rfl
def Pi.inv_eq [∀i, Inv (α i)] (f: ∀i, α i): f⁻¹ = fun x => (f x)⁻¹ := rfl

@[simp] def Pi.apply_zero [∀i, Zero (α i)] (i: ι) : (0: ∀i, α i) i = 0 := rfl
@[simp] def Pi.apply_one [∀i, One (α i)] (i: ι) : (1: ∀i, α i) i = 1 := rfl
@[simp] def Pi.apply_natCast [∀i, NatCast (α i)] (n: ℕ) (i: ι): (n: ∀i, α i) i = (n: α _) := rfl
@[simp] def Pi.apply_intCast [∀i, IntCast (α i)] (n: ℤ) (i: ι): (n: ∀i, α i) i = (n: α _) := rfl
@[simp] def Pi.apply_add [∀i, Add (α i)] (f g: ∀i, α i) (i: ι): (f + g) i = f i + g i := rfl
@[simp] def Pi.apply_mul [∀i, Mul (α i)] (f g: ∀i, α i) (i: ι): (f * g) i = f i * g i := rfl
@[simp] def Pi.apply_sub [∀i, Sub (α i)] (f g: ∀i, α i) (i: ι): (f - g) i = f i - g i := rfl
@[simp] def Pi.apply_div [∀i, Div (α i)] (f g: ∀i, α i) (i: ι): (f / g) i = f i / g i := rfl
@[simp] def Pi.apply_smul [∀i, SMul R (α i)] (r: R) (f: ∀i, α i): (r • f) i = r • f i := rfl
@[simp] def Pi.apply_npow [∀i, Pow (α i) ℕ] (f: ∀i, α i) (n: ℕ): (f ^ n) i = f i ^ n := rfl
@[simp] def Pi.apply_zpow [∀i, Pow (α i) ℤ] (f: ∀i, α i) (n: ℤ): (f ^ n) i = f i ^ n := rfl
@[simp] def Pi.apply_neg [∀i, Neg (α i)] (f: ∀i, α i): (-f) i = -f i := rfl
@[simp] def Pi.apply_inv [∀i, Inv (α i)] (f: ∀i, α i): (f⁻¹) i = (f i)⁻¹ := rfl

end Pi.Operators

section Function.Operators

-- just define all operators pointwise here, we can't implement IsGroupWithZero
-- so we don't need any of the checked operators

variable {ι α: Type*}

instance [Zero α] : Zero (ι -> α) :=
  inferInstance
instance [One α] : One (ι -> α) :=
  inferInstance
instance [NatCast α] : NatCast (ι -> α) :=
  inferInstance
instance [IntCast α] : IntCast (ι -> α) :=
  inferInstance
instance [Add α] : Add (ι -> α) :=
  inferInstance
instance [Sub α] : Sub (ι -> α) :=
  inferInstance
instance [Mul α] : Mul (ι -> α) :=
  inferInstance
instance [Div α] : Div (ι -> α) :=
  inferInstance
instance [SMul ℕ α] : SMul ℕ (ι -> α) :=
  inferInstance
instance [SMul ℤ α] : SMul ℤ (ι -> α) :=
  inferInstance
instance [Pow α ℕ] : Pow (ι -> α) ℕ :=
  inferInstance
instance [Pow α ℤ] : Pow (ι -> α) ℤ :=
  inferInstance
instance [Neg α] : Neg (ι -> α) :=
  inferInstance
instance [Inv α] : Inv (ι -> α) :=
  inferInstance

def Function.zero_eq [Zero α] : (0: ι -> α) = fun _ => 0 := rfl
def Function.one_eq [One α] : (1: ι -> α) = fun _ => 1 := rfl
def Function.natCast_eq [NatCast α] (n: ℕ): (n: ι -> α) = fun _ => (n: α) := rfl
def Function.intCast_eq [IntCast α] (n: ℤ): (n: ι -> α) = fun _ => (n: α) := rfl
def Function.add_eq [Add α] (f g: ι -> α): f + g = fun x => f x + g x := rfl
def Function.mul_eq [Mul α] (f g: ι -> α): f * g = fun x => f x * g x := rfl
def Function.sub_eq [Sub α] (f g: ι -> α): f - g = fun x => f x - g x := rfl
def Function.div_eq [Div α] (f g: ι -> α): f / g = fun x => f x / g x := rfl
def Function.smul_eq [SMul R α] (r: R) (f: ι -> α): r • f = fun x => r • f x := rfl
def Function.npow_eq [Pow α ℕ] (f: ι -> α) (n: ℕ): f ^ n = fun x => f x ^ n := rfl
def Function.zpow_eq [Pow α ℤ] (f: ι -> α) (n: ℤ): f ^ n = fun x => f x ^ n := rfl
def Function.neg_eq [Neg α] (f: ι -> α): -f = fun x => -f x := rfl
def Function.inv_eq [Inv α] (f: ι -> α): f⁻¹ = fun x => (f x)⁻¹ := rfl

@[simp] def Function.apply_zero [Zero α] (i: ι) : (0: ι -> α) i = 0 := rfl
@[simp] def Function.apply_one [One α] (i: ι) : (1: ι -> α) i = 1 := rfl
@[simp] def Function.apply_natCast [NatCast α] (n: ℕ) (i: ι): (n: ι -> α) i = (n: α) := rfl
@[simp] def Function.apply_intCast [IntCast α] (n: ℤ) (i: ι): (n: ι -> α) i = (n: α) := rfl
@[simp] def Function.apply_add [Add α] (f g: ι -> α) (i: ι): (f + g) i = f i + g i := rfl
@[simp] def Function.apply_mul [Mul α] (f g: ι -> α) (i: ι): (f * g) i = f i * g i := rfl
@[simp] def Function.apply_sub [Sub α] (f g: ι -> α) (i: ι): (f - g) i = f i - g i := rfl
@[simp] def Function.apply_div [Div α] (f g: ι -> α) (i: ι): (f / g) i = f i / g i := rfl
@[simp] def Function.apply_smul [SMul R α] (r: R) (f: ι -> α): (r • f) i = r • f i := rfl
@[simp] def Function.apply_npow [Pow α ℕ] (f: ι -> α) (n: ℕ): (f ^ n) i = f i ^ n := rfl
@[simp] def Function.apply_zpow [Pow α ℤ] (f: ι -> α) (n: ℤ): (f ^ n) i = f i ^ n := rfl
@[simp] def Function.apply_neg [Neg α] (f: ι -> α): (-f) i = -f i := rfl
@[simp] def Function.apply_inv [Inv α] (f: ι -> α): (f⁻¹) i = (f i)⁻¹ := rfl

end Function.Operators

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)] : IsAddZeroClass (∀i, α i) where
  zero_add := by
    intro f; ext i
    apply zero_add
  add_zero := by
    intro f; ext i
    apply add_zero

instance [∀i, One (α i)] [∀i, Mul (α i)] [∀i, IsMulOneClass (α i)] : IsMulOneClass (∀i, α i)
  := inferInstanceAs (IsMulOneClass (MulOfAdd (∀i, AddOfMul (α i))))

instance [∀i, Zero (α i)] [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] : IsMulZeroClass (∀i, α i) where
  zero_mul := by
    intro f; ext i
    apply zero_mul
  mul_zero := by
    intro f; ext i
    apply mul_zero

instance [∀i, Add (α i)] [∀i, IsAddSemigroup (α i)] : IsAddSemigroup (∀i, α i) where
  add_assoc := by
    intro a b c; ext i
    apply add_assoc

instance [∀i, Mul (α i)] [∀i, IsSemigroup (α i)] : IsSemigroup (∀i, α i) :=
  inferInstanceAs (IsSemigroup (MulOfAdd (∀i, AddOfMul (α i))))

instance [∀i, Add (α i)] [∀i, IsAddCommMagma (α i)] : IsAddCommMagma (∀i, α i) where
  add_comm := by
    intro a b; ext i
    apply add_comm

instance [∀i, Mul (α i)] [∀i, IsCommMagma (α i)] : IsCommMagma (∀i, α i) :=
  inferInstanceAs (IsCommMagma (MulOfAdd (∀i, AddOfMul (α i))))

end Pi

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)] : IsAddZeroClass (∀i, α i) where
  zero_add := by
    intro f; ext i
    apply zero_add
  add_zero := by
    intro f; ext i
    apply add_zero

instance [∀i, One (α i)] [∀i, Mul (α i)] [∀i, IsMulOneClass (α i)] : IsMulOneClass (∀i, α i)
  := inferInstanceAs (IsMulOneClass (MulOfAdd (∀i, AddOfMul (α i))))

instance [∀i, Zero (α i)] [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] : IsMulZeroClass (∀i, α i) where
  zero_mul := by
    intro f; ext i
    apply zero_mul
  mul_zero := by
    intro f; ext i
    apply mul_zero

instance [∀i, Add (α i)] [∀i, IsAddSemigroup (α i)] : IsAddSemigroup (∀i, α i) where
  add_assoc := by
    intro a b c; ext i
    apply add_assoc

instance [∀i, Mul (α i)] [∀i, IsSemigroup (α i)] : IsSemigroup (∀i, α i) :=
  inferInstanceAs (IsSemigroup (MulOfAdd (∀i, AddOfMul (α i))))

instance [∀i, Add (α i)] [∀i, IsAddCommMagma (α i)] : IsAddCommMagma (∀i, α i) where
  add_comm := by
    intro a b; ext i
    apply add_comm

instance [∀i, Mul (α i)] [∀i, IsCommMagma (α i)] : IsCommMagma (∀i, α i) :=
  inferInstanceAs (IsCommMagma (MulOfAdd (∀i, AddOfMul (α i))))

end Pi

section Function

instance [Zero α] [Add α] [IsAddZeroClass α] : IsAddZeroClass (ι -> α) :=
  inferInstance
instance [One α] [Mul α] [IsMulOneClass α] : IsMulOneClass (ι -> α) :=
  inferInstance
instance [Zero α] [Mul α] [IsMulZeroClass α] : IsMulZeroClass (ι -> α) :=
  inferInstance
instance [Add α] [IsAddSemigroup α] : IsAddSemigroup (ι -> α) :=
  inferInstance
instance [Mul α] [IsSemigroup α] : IsSemigroup (ι -> α) :=
  inferInstance
instance [Add α] [IsAddCommMagma α] : IsAddCommMagma (ι -> α) :=
  inferInstance
instance [Mul α] [IsCommMagma α] : IsCommMagma (ι -> α) :=
  inferInstance

end Function
