import Math.Data.Rsqrtd.Defs
import Math.Algebra.Ring.Defs
import Math.Algebra.Hom.Defs
import Math.Ops.Abs

namespace Rsqrtd

variable {R: Type*} [RingOps R] [IsRing R] [IsCommMagma R] {d: R}

scoped notation R:100 "[i]" => @Rsqrtd R (-1)

prefix:100 "ℤ√" => @Rsqrtd ℤ

instance : Neg (R√d) where
  neg x := ⟨-x.a, -x.b⟩
instance : Sub (R√d) where
  sub x y := ⟨x.a - y.a, x.b - y.b⟩
instance : SMul ℤ (R√d) where
  smul n x := ⟨n • x.a, n • x.b⟩
instance : IntCast (R√d) where
  intCast n := ⟨n, 0⟩

@[simp] def a_neg (x: R√d) : a (-x) = -a x := rfl
@[simp] def b_neg (x: R√d) : b (-x) = -b x := rfl
@[simp] def a_sub (x y: R√d) : a (x - y) = a x - a y := rfl
@[simp] def b_sub (x y: R√d) : b (x - y) = b x - b y := rfl
@[simp] def a_zsmul (n: ℤ) (x: R√d) : a (n • x) = n • a x := rfl
@[simp] def b_zsmul (n: ℤ) (x: R√d) : b (n • x) = n • b x := rfl
@[simp] def a_intCast (n: ℤ) : a (n: R√d) = n := rfl
@[simp] def b_intCast (n: ℤ) : b (n: R√d) = 0 := rfl

instance : IsRing (R√d) where
  sub_eq_add_neg _ _ := by ext <;> apply sub_eq_add_neg
  neg_add_cancel _ := by ext <;> apply neg_add_cancel
  zsmul_ofNat _ _ := by ext <;> apply zsmul_ofNat
  zsmul_negSucc _ _ := by ext <;> apply zsmul_negSucc
  intCast_ofNat _ := by ext <;> simp [intCast_ofNat]
  intCast_negSucc _ := by ext <;> simp [intCast_negSucc]

private def norm (x: R√d) := x.a * x.a - d * x.b * x.b
def conj (x: R√d) : R√d := {
  a := x.a
  b := -x.b
}

instance : Norm (R√d) R where
  norm := norm

def norm_def (x: R√d) : ‖x‖ = x.a * x.a - d * x.b * x.b := rfl

def conjHom : (R√d) →+* (R√d) where
  toFun := conj
  map_zero := by simp [conj]; rfl
  map_one := by simp [conj]; rfl
  map_add {x y} := by
    ext <;> simp [conj]
    rw [neg_add_rev, add_comm]
  map_mul {x y} := by
    ext <;> simp [conj]
    rw [←neg_mul_right, ←neg_mul_right, ←neg_mul_left, neg_neg]
    rw [←neg_mul_left, ←neg_mul_right, neg_add_rev, add_comm]

@[simp] def conj_zero : conj (d := d) 0 = 0 := map_zero conjHom
@[simp] def conj_one : conj (d := d) 1 = 1 := map_one conjHom
def conj_add (x y: R√d) : conj (x + y) = conj x + conj y := map_add conjHom
def conj_mul (x y: R√d) : conj (x * y) = conj x * conj y := map_mul conjHom

def norm_eq_mul_conj (x: R√d) : ‖x‖ = x * x.conj := by
  ext <;> simp [Norm.norm, norm, conj]
  rw [←neg_mul_right, sub_eq_add_neg]
  rw [←neg_mul_right, mul_comm, neg_add_cancel]

def normHom : (R√d) →* R where
  toFun := norm
  map_one := by simp [norm]
  map_mul {x y} := by
    simp
    apply coe_inj
    simp
    repeat erw [norm_eq_mul_conj]
    rw [conj_mul]
    ac_rfl

@[simp] def norm_one : ‖(1: R√d)‖ = 1 := map_one normHom
def norm_mul (x y: R√d) : ‖x * y‖ = ‖x‖ * ‖y‖ := map_mul normHom

instance [IsNontrivial R] : IsNontrivial (R√d) where
  exists_ne := ⟨1, ⟨0, 1⟩, by
    intro h
    have : a (1: R√d) = 0 := by rw [h]
    exact zero_ne_one _ this.symm⟩

end Rsqrtd
