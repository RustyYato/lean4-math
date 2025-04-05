import Math.Algebra.Semiring.Defs
import Math.Function.Basic

@[ext]
structure Rsqrtd (d: α) where
  a: α
  b: α


namespace Rsqrtd

scoped notation R "√" d => @Rsqrtd R d

variable {R: Type*} [SemiringOps R] [IsSemiring R] [IsCommMagma R] {d: R}

@[coe]
def of : R -> R√d := fun a => ⟨a, 0⟩

instance : Coe R (R√d) where
  coe := of

instance : Zero (R√d) where
  zero := (0: R)
instance : One (R√d) where
  one := (1: R)
instance : NatCast (R√d) where
  natCast n := (n: R)
instance : Add (R√d) where
  add x y := ⟨x.a + y.a, x.b + y.b⟩
instance : SMul ℕ (R√d) where
  smul n x := ⟨n • x.a, n • x.b⟩

instance : Mul (R√d) where
  mul x y := {
    a := x.a * y.a + d * x.b * y.b
    b := x.a * y.b + x.b * y.a
  }

instance : Pow (R√d) ℕ := instNPowrec

instance : SMul R (R√d) where
  smul r x := {
    a := r * x.a
    b := r * x.b
  }

@[simp] def a_zero : a (0: R√d) = 0 := rfl
@[simp] def b_zero : b (0: R√d) = 0 := rfl
@[simp] def a_one : a (1: R√d) = 1 := rfl
@[simp] def b_one : b (1: R√d) = 0 := rfl
@[simp] def a_natCast (n: ℕ) : a (n: R√d) = n := rfl
@[simp] def b_natCast (n: ℕ) : b (n: R√d) = 0 := rfl
@[simp] def a_add (x y: R√d) : a (x + y) = a x + a y := rfl
@[simp] def b_add (x y: R√d) : b (x + y) = b x + b y := rfl
@[simp] def a_nsmul (n: ℕ) (x: R√d) : a (n • x) = n • a x := rfl
@[simp] def b_nsmul (n: ℕ) (x: R√d) : b (n • x) = n • b x := rfl
@[simp] def a_mul (x y: R√d) : a (x * y) = x.a * y.a + d * x.b * y.b := rfl
@[simp] def b_mul (x y: R√d) : b (x * y) = x.a * y.b + x.b * y.a := rfl

@[simp] def a_coe (x: R) : a (x: R√d) = x := rfl
@[simp] def b_coe (x: R) : b (x: R√d) = 0 := rfl

@[norm_cast, simp] def coe_zero : ((0: R): R√d) = 0 := rfl
@[norm_cast, simp] def coe_one : ((1: R): R√d) = 1 := rfl
@[norm_cast, simp] def coe_natCast (n: ℕ) : ((n: R): R√d) = n := rfl
@[norm_cast, simp] def coe_add (a b: R) : ((a + b: R): R√d) = a + b := by ext <;> simp
@[norm_cast, simp] def coe_mul (a b: R) : ((a * b: R): R√d) = a * b := by ext <;> simp
@[norm_cast, simp] def coe_nsmul (n: ℕ) (a: R) : ((n • a: R): R√d) = n • (a: R√d) := by ext <;> simp

@[simp] def a_smul (r: R) (x: R√d) : a (r • x) = r • a x := rfl
@[simp] def b_smul (r: R) (x: R√d) : b (r • x) = r • b x := rfl

def smul_eq_coe_mul (r: R) (x: R√d) : r • x = r * x := by ext <;> (simp; rfl)

def coe_inj : Function.Injective (of (d := d)) := by
  intro x y h
  cases h
  rfl

instance : IsCommMagma (R√d) where
  mul_comm a b := by ext <;> (simp [add_mul, mul_add]; ac_rfl)

instance : IsSemiring (R√d) where
  add_comm _ _ := by ext <;> apply add_comm
  add_assoc a b c := by ext <;> apply add_assoc
  zero_add a := by ext <;> apply zero_add
  add_zero a := by ext <;> apply add_zero
  natCast_zero := by ext <;> simp; norm_cast
  natCast_succ n := by ext <;> simp; norm_cast
  zero_nsmul a := by ext <;> apply zero_nsmul
  succ_nsmul n a := by ext <;> apply succ_nsmul
  mul_assoc a b c := by ext <;> (simp [add_mul, mul_add]; ac_rfl)
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b k := by ext <;> (simp [add_mul, mul_add]; ac_rfl)
  right_distrib a b k := by ext <;> (simp [add_mul, mul_add]; ac_rfl)

end Rsqrtd
