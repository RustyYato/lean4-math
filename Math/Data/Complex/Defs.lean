import Math.Data.Real.Order
import Math.Data.Rsqrtd.Order
import Math.Data.Rsqrtd.Algebra

open Rsqrtd

def Complex := ℝ[i]
notation "ℂ" => Complex

namespace Complex

def real : ℂ -> ℝ := Rsqrtd.a
def img : ℂ -> ℝ := Rsqrtd.b

def toRsqrtd : ℂ -> ℝ[i] := id

def mag_sq (c: ℂ) : ℝ := Rsqrtd.norm c.toRsqrtd
def conj (c: ℂ) : ℂ := c.toRsqrtd.conj

instance : FieldOps ℂ := inferInstanceAs (FieldOps (ℝ[i]))
open Classical in
instance : IsField ℂ := inferInstanceAs (IsField (ℝ[i]))
instance : Inhabited ℂ := ⟨0⟩

instance : SMul ℝ ℂ := inferInstanceAs (SMul ℝ (ℝ[i]))
instance : AlgebraMap ℝ ℂ := inferInstanceAs (AlgebraMap ℝ (ℝ[i]))
instance : IsAlgebra ℝ ℂ := inferInstanceAs (IsAlgebra ℝ (ℝ[i]))

def ofRealHom : ℝ ↪+* ℂ := {
  algebraMap with
  inj' := field_hom_inj algebraMap
}

@[coe]
protected def ofReal : ℝ -> ℂ := ofRealHom

instance : Coe ℝ ℂ := ⟨.ofReal⟩

instance : HasChar ℂ 0 := HasChar.of_ring_emb ofRealHom

def mag_sq_nonzero : x ≠ 0 -> mag_sq x ≠ 0 := Rsqrtd.norm_ne_zero _

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply mag_sq_nonzero; invert_tactic)

def i : ℂ := ⟨0, 1⟩

@[simp] def real_zero : real (0: ℂ) = 0 := rfl
@[simp] def img_zero : img (0: ℂ) = 0 := rfl
@[simp] def real_one : real (1: ℂ) = 1 := rfl
@[simp] def img_one : img (1: ℂ) = 0 := rfl
@[simp] def real_natCast (n: ℕ) : real (n: ℂ) = n := rfl
@[simp] def img_natCast (n: ℕ) : img (n: ℂ) = 0 := rfl
@[simp] def real_add (x y: ℂ) : real (x + y) = real x + real y := rfl
@[simp] def img_add (x y: ℂ) : img (x + y) = img x + img y := rfl
@[simp] def real_nsmul (n: ℕ) (x: ℂ) : real (n • x) = n • real x := rfl
@[simp] def img_nsmul (n: ℕ) (x: ℂ) : img (n • x) = n • img x := rfl
@[simp] def real_mul (x y: ℂ) : real (x * y) = x.real * y.real - x.img * y.img := by
  rw [sub_eq_add_neg]
  apply Eq.trans
  apply Rsqrtd.a_mul
  rw [neg_one_mul, neg_mul]
  rfl
@[simp] def img_mul (x y: ℂ) : img (x * y) = x.real * y.img + x.img * y.real := rfl

@[simp] def real_neg (x: ℂ) : real (-x) = -real x := rfl
@[simp] def img_neg (x: ℂ) : img (-x) = -img x := rfl
@[simp] def real_sub (x y: ℂ) : real (x - y) = real x - real y := rfl
@[simp] def img_sub (x y: ℂ) : img (x - y) = img x - img y := rfl
@[simp] def real_zsmul (n: ℤ) (x: ℂ) : real (n • x) = n • real x := rfl
@[simp] def img_zsmul (n: ℤ) (x: ℂ) : img (n • x) = n • img x := rfl
@[simp] def real_intCast (n: ℤ) : real (n: ℂ) = n := rfl
@[simp] def img_intCast (n: ℤ) : img (n: ℂ) = 0 := rfl

@[simp] def real_inv (x: ℂ) (h: x ≠ 0) : real (x⁻¹?) = (real x) /? x.mag_sq := rfl
@[simp] def img_inv (x: ℂ) (h: x ≠ 0) : img (x⁻¹?) = (-img x) /? x.mag_sq := rfl

@[simp] def real_algebraMap (x: ℝ) : real (algebraMap x) = x := rfl
@[simp] def img_algebraMap (x: ℝ) : img (algebraMap x) = 0 := rfl

@[simp] def real_i : real i = 0 := rfl
@[simp] def img_i : img i = 1 := rfl

@[simp] def real_coe (r: ℝ) : real r = r := rfl
@[simp] def img_coe (r: ℝ) : img r = 0 := rfl

@[ext]
def ext (a b: ℂ) : a.real = b.real -> a.img = b.img -> a = b := Rsqrtd.ext

def mk (a b: ℝ) : ℂ := ⟨a, b⟩
@[simp] def mk_real (a b: ℝ) : (mk a b).real = a := rfl
@[simp] def mk_img (a b: ℝ) : (mk a b).img = b := rfl

end Complex
