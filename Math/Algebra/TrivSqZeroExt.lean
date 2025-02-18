import Math.Algebra.Ring
import Math.Function.Basic
import Math.Algebra.Impls.Prod

def TrivSqZeroExt (R : Type u) (M : Type v) := R × M

namespace TrivSqZeroExt

def inl [Zero M] (r: R) : TrivSqZeroExt R M := (r, 0)
def inr [Zero R] (m: M) : TrivSqZeroExt R M := (0, m)

def fst (x: TrivSqZeroExt R M) : R := Prod.fst x
def snd (x: TrivSqZeroExt R M) : M := Prod.snd x

@[ext]
def ext (a b: TrivSqZeroExt R M) : a.fst = b.fst -> a.snd = b.snd -> a = b := Prod.ext

@[simp]
def fst_inl [Zero M] (r: R) : fst (inl (M := M) r) = r := rfl
@[simp]
def snd_inl [Zero M] (r: R) : snd (inl (M := M) r) = 0 := rfl
@[simp]
def fst_inr [Zero R] (m: M) : fst (inr (R := R) m) = 0 := rfl
@[simp]
def snd_inr [Zero R] (m: M) : snd (inr (R := R) m) = m := rfl

@[simp]
def fst_mk (r: R) (m: M) : fst (r, m) = r := rfl
@[simp]
def snd_mk (r: R) (m: M) : snd (r, m) = m := rfl

def inl_inj [Zero M] : Function.Injective (inl : R -> TrivSqZeroExt R M) :=
  Function.IsLeftInverse.Injective fst_inl
def inr_inj [Zero R] : Function.Injective (inr : M -> TrivSqZeroExt R M) :=
  Function.IsLeftInverse.Injective snd_inr

section Add

variable {T S R M: Type*}

instance [Zero R] [Zero M] : Zero (TrivSqZeroExt R M) := inferInstanceAs (Zero (R × M))
instance [Add R] [Add M] : Add (TrivSqZeroExt R M) := inferInstanceAs (Add (R × M))
instance [SMul S R] [SMul S M] : SMul S (TrivSqZeroExt R M) := inferInstanceAs (SMul S (R × M))
instance [Sub R] [Sub M] : Sub (TrivSqZeroExt R M) := inferInstanceAs (Sub (R × M))
instance [Neg R] [Neg M] : Neg (TrivSqZeroExt R M) := inferInstanceAs (Neg (R × M))
instance [Add R] [Add M] [IsAddSemigroup R] [IsAddSemigroup M] : IsAddSemigroup (TrivSqZeroExt R M) := inferInstanceAs (IsAddSemigroup (R × M))
instance [Add R] [Add M] [IsAddCommMagma R] [IsAddCommMagma M] : IsAddCommMagma (TrivSqZeroExt R M) := inferInstanceAs (IsAddCommMagma (R × M))
instance [Add R] [Add M] [Zero R] [Zero M] [IsAddZeroClass R] [IsAddZeroClass M] : IsAddZeroClass (TrivSqZeroExt R M) := inferInstanceAs (IsAddZeroClass (R × M))
instance [AddMonoidOps R] [AddMonoidOps M] [IsAddMonoid R] [IsAddMonoid M] : IsAddMonoid (TrivSqZeroExt R M) := inferInstanceAs (IsAddMonoid (R × M))
instance [AddGroupOps R] [AddGroupOps M] [IsAddGroup R] [IsAddGroup M] : IsAddGroup (TrivSqZeroExt R M) := inferInstanceAs (IsAddGroup (R × M))

instance [MonoidOps S] [SMul S R] [SMul S M] [IsMonoid S] [IsMulAction S R] [IsMulAction S M] : IsMulAction S (TrivSqZeroExt R M) :=
  inferInstanceAs (IsMulAction S (R × M))

instance [MonoidOps R] [SMul R α] [SMul R β] [IsMonoid R]
  [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β]
  [IsDistribMulAction R α] [IsDistribMulAction R β] : IsDistribMulAction R (α × β) where
  smul_zero := by
    intro a; ext <;> apply smul_zero
  smul_add := by
    intro r a b; ext <;> apply smul_add

instance [SemiringOps R] [SMul R α] [SMul R β] [IsSemiring R]
  [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β]
  [IsAddCommMagma α] [IsAddCommMagma β]
  [IsModule R α] [IsModule R β] : IsModule R (α × β) where
  add_smul := by
    intro r s a
    ext <;> apply add_smul
  zero_smul := by
    intro r
    ext <;> apply zero_smul

@[simp] def fst_zero [Zero R] [Zero M] : fst (R := R) (M := M) 0 = 0 := rfl
@[simp] def snd_zero [Zero R] [Zero M] : snd (R := R) (M := M) 0 = 0 := rfl

@[simp] def fst_add [Add R] [Add M] (a b: TrivSqZeroExt R M) : fst (a + b) = fst a + fst b := rfl
@[simp] def snd_add [Add R] [Add M] (a b: TrivSqZeroExt R M) : snd (a + b) = snd a + snd b := rfl

@[simp] def fst_sub [Sub R] [Sub M] (a b: TrivSqZeroExt R M) : fst (a - b) = fst a - fst b := rfl
@[simp] def snd_sub [Sub R] [Sub M] (a b: TrivSqZeroExt R M) : snd (a - b) = snd a - snd b := rfl

@[simp] def fst_neg [Neg R] [Neg M] (a: TrivSqZeroExt R M) : fst (-a) = -fst a := rfl
@[simp] def snd_neg [Neg R] [Neg M] (a: TrivSqZeroExt R M) : snd (-a) = -snd a := rfl

@[simp] def fst_smul [SMul S R] [SMul S M] (s: S) (a: TrivSqZeroExt R M) : fst (s • a) = s • fst a := rfl
@[simp] def snd_smul [SMul S R] [SMul S M] (s: S) (a: TrivSqZeroExt R M) : snd (s • a) = s • snd a := rfl

def inl_zero [Zero R] [Zero M] : inl (M := M) 0 = 0 := rfl
def inr_zero [Zero R] [Zero M] : inr (R := R) 0 = 0 := rfl
def inl_fst_add_inr_snd_eq [Zero R] [Zero M] [Add R] [Add M] [IsAddZeroClass R] [IsAddZeroClass M] (x: TrivSqZeroExt R M) :
  x = (inl x.fst + inr x.snd) := by
  ext <;> simp [add_zero, zero_add]

/-- To show a property hold on all `TrivSqZeroExt R M` it suffices to show it holds
on terms of the form `inl r + inr m`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def ind {R M} [Zero R] [Zero M] [Add R] [Add M] [IsAddZeroClass R] [IsAddZeroClass M] {P : TrivSqZeroExt R M → Prop}
    (inl_add_inr : ∀ r m, P (inl r + inr m)) (x) : P x := by
  rw [inl_fst_add_inr_snd_eq x]
  apply inl_add_inr

def linearMap_ext {N} [SemiringOps S] [IsSemiring S]
    [AddMonoidOps R] [IsAddMonoid R] [IsAddCommMagma R]
    [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
    [AddMonoidOps N] [IsAddMonoid N] [IsAddCommMagma N]
    [SMul S R] [SMul S M] [SMul S N]
    [IsModule S R] [IsModule S M] [IsModule S N] ⦃f g : TrivSqZeroExt R M →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ m, f (inr m) = g (inr m)) : f = g := by
    apply DFunLike.ext
    intro x
    induction x with | inl_add_inr r m =>
    rw [resp_add, resp_add, hl, hr]

def inrHom [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddCommMagma M] [IsAddMonoid M]
  [SMul R M] [IsModule R M] : M →ₗ[R] TrivSqZeroExt R M where
  toFun := inr
  resp_add {x y} := by ext <;> simp [add_zero]
  resp_smul {n x} := by ext <;> simp; apply (mul_zero _).symm

def sndHom [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddCommMagma M] [IsAddMonoid M]
  [SMul R M] [IsModule R M] : TrivSqZeroExt R M →ₗ[R] M where
  toFun := snd
  resp_add := rfl
  resp_smul := rfl

end Add

section Mul

-- for some reason lean is unable to infer this
instance [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M]
  [SMul Rᵐᵒᵖ M] [IsAddCommMagma M] [h: IsModule Rᵐᵒᵖ M] : IsDistribMulAction Rᵐᵒᵖ M := h.toIsDistribMulAction

instance [One R] [Zero M] : One (TrivSqZeroExt R M) := ⟨inl 1⟩

instance [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] : Mul (TrivSqZeroExt R M) where
  mul a b := (a.fst * b.fst, a.fst • b.snd + MulOpp.mk b.fst • a.snd)

@[simp] def fst_one [One R] [Zero M] : fst (R := R) (M := M) 1 = 1 := rfl
@[simp] def snd_one [One R] [Zero M] : snd (R := R) (M := M) 1 = 0 := rfl

@[simp] def fst_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (a b: TrivSqZeroExt R M) :
  fst (R := R) (M := M) (a * b) = a.fst * b.fst := rfl
@[simp] def snd_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (a b: TrivSqZeroExt R M) :
  snd (R := R) (M := M) (a * b) = a.fst • b.snd + MulOpp.mk b.fst • a.snd := rfl

@[simp] def inl_one [One R] [Zero M] : inl (M := M) 1 = 1 := rfl

@[simp]
def inl_mul_inl [MonoidOps R] [IsMonoid R] [AddMonoidOps M] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsDistribMulAction R M] [IsDistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : inl r₁ * inl r₂ = inl (M := M) (r₁ * r₂) := by
  ext
  simp
  simp
  rw [smul_zero, smul_zero, zero_add]

@[simp]
def inl_mul_inr [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsDistribMulAction R M] [IsDistribMulAction Rᵐᵒᵖ M]
    (r: R) (m: M) : inl r * inr m = inr (r • m) := by
  ext
  simp [mul_zero]
  simp
  simp [smul_zero, add_zero]

@[simp]
def inr_mul_inl [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsDistribMulAction R M] [IsDistribMulAction Rᵐᵒᵖ M]
    (r: R) (m: M) : inr m * inl r = inr (MulOpp.mk r • m) := by
  ext
  simp [zero_mul]
  simp
  simp [smul_zero, zero_add]

@[simp]
def inr_mul_inr [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsAddCommMagma M] [IsModule R M] [IsModule Rᵐᵒᵖ M]
    (m₀ m₁: M) : inr (R := R) m₀ * inr m₁ = 0 := by
  ext
  simp [zero_mul]
  simp [zero_smul, zero_add]

@[simp]
def inr_mul [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsAddCommMagma M] [IsModule R M] [IsModule Rᵐᵒᵖ M]
  (x: TrivSqZeroExt R M) (r: R) : x * inl r = MulOpp.mk r • x := by
  ext <;> simp
  rfl
  simp [smul_zero, zero_add]

@[simp]
def mul_inr [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsAddCommMagma M] [IsModule R M] [h: IsModule Rᵐᵒᵖ M]
  (x: TrivSqZeroExt R M) (r: R) : inl r  * x = r • x := by
  ext <;> simp
  simp [smul_zero, add_zero]

instance instMulOneClass [MonoidOps R] [IsMonoid R] [AddMonoidOps M] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsDistribMulAction R M] [IsDistribMulAction Rᵐᵒᵖ M] : IsMulOneClass (TrivSqZeroExt R M) where
  one_mul a := by ext <;> simp [one_mul, smul_zero, one_smul, add_zero]
  mul_one a := by ext <;> simp [mul_one, smul_zero, one_smul, zero_add]

instance [NatCast R] [Zero M] : NatCast (TrivSqZeroExt R M) where
  natCast n := inl n
instance [IntCast R] [Zero M] : IntCast (TrivSqZeroExt R M) where
  intCast n := inl n
instance [OfNat R (n + 2)] [Zero M] : OfNat (TrivSqZeroExt R M) (n + 2) where
  ofNat := inl (OfNat.ofNat (n + 2))

@[simp] def fst_natCast [NatCast R] [Zero M] (n: Nat) : (n: TrivSqZeroExt R M).fst = n := rfl
@[simp] def snd_natCast [NatCast R] [Zero M] (n: Nat) : (n: TrivSqZeroExt R M).snd = 0 := rfl

@[simp] def inl_natCast [NatCast R] [Zero M] (n: Nat) : (.inl n: TrivSqZeroExt R M) = n := rfl

@[simp] def fst_intCast [IntCast R] [Zero M] (n: Int) : (n: TrivSqZeroExt R M).fst = n := rfl
@[simp] def snd_intCast [IntCast R] [Zero M] (n: Int) : (n: TrivSqZeroExt R M).snd = 0 := rfl

@[simp] def inl_intCast [IntCast R] [Zero M] (n: Int) : (.inl n: TrivSqZeroExt R M) = n := rfl

@[simp] def fst_ofNat (n: Nat) [OfNat R (n + 2)] [Zero M] : (OfNat.ofNat (n + 2): TrivSqZeroExt R M).fst = OfNat.ofNat (n + 2) := rfl
@[simp] def snd_ofNat (n: Nat) [OfNat R (n + 2)] [Zero M] : (OfNat.ofNat (n + 2): TrivSqZeroExt R M).snd = 0 := rfl

instance instAddMonoidWithOne [AddMonoidWithOneOps R] [AddMonoidOps M] [IsAddMonoidWithOne R] [IsAddMonoid M] : IsAddMonoidWithOne (TrivSqZeroExt R M) where
  natCast_zero := by ext <;> simp [natCast_zero]
  natCast_succ n := by ext <;> simp [natCast_succ, add_zero]
  ofNat_eq_natCast n := by ext <;> simp [ofNat_eq_natCast]

instance instAddGroupWithOne [AddGroupWithOneOps R] [AddGroupOps M] [IsAddGroupWithOne R] [IsAddGroup M] : IsAddGroupWithOne (TrivSqZeroExt R M) where
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  ofNat_eq_natCast := ofNat_eq_natCast
  intCast_ofNat n := by ext <;> simp [intCast_ofNat]
  intCast_negSucc n := by ext <;> simp [intCast_negSucc, neg_zero]

section

variable [MonoidOps R] [IsMonoid R] [AddMonoidOps M] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsDistribMulAction R M]
  [IsDistribMulAction Rᵐᵒᵖ M] [IsSMulComm R Rᵐᵒᵖ M]

private noncomputable def npow' : ℕ -> TrivSqZeroExt R M -> TrivSqZeroExt R M :=
  have : IsDistribMulAction Rᵐᵒᵖ M := inferInstance
  npowRec

@[simp]
private def npow'_zero (x: TrivSqZeroExt R M) : npow' 0 x = 1 := rfl

@[simp]
private def npow'_succ (n: Nat) (x: TrivSqZeroExt R M) : npow' (n + 1) x = npow' n x * x := rfl

@[simp]
private def fst_npow' (x: TrivSqZeroExt R M) (n: ℕ) : fst (npow' n x) = x.fst ^ n := by
  induction n with
  | zero => simp [npow_zero]
  | succ n ih => simp [npow_succ, ih]

private def smul_list_sum (r: R) (as: List M) : r • as.sum = (as.map (fun a => r • a)).sum := by
  induction as with
  | nil => simp [List.sum_nil, smul_zero]
  | cons a as ih => simp [List.sum_cons, ih, smul_add]

@[simp]
private def snd_npow' (x: TrivSqZeroExt R M) (n: ℕ) : snd (npow' n x) = ((List.range n).map fun i => MulOpp.mk (x.fst ^ i) • (x.fst ^ (n.pred - i) • x.snd)).sum := by
  induction n with
  | zero => simp [npow_zero]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons]
    simp [npow_succ, ih, npow_zero, one_smul]
    congr
    dsimp [Function.comp_def]
    clear ih
    rw [smul_list_sum]
    simp
    congr
    ext i; simp
    simp [←mul_smul, ←MulOpp.mk_mul, ←npow_succ]
    congr 3
    rw [Nat.add_comm, Nat.sub_add_eq]

private def npowFast' (n: Nat) (x: TrivSqZeroExt R M): TrivSqZeroExt R M :=
  have : IsDistribMulAction Rᵐᵒᵖ M := inferInstance
  ⟨x.fst ^ n, ((List.range n).map fun i => MulOpp.mk (x.fst ^ i) • (x.fst ^ (n.pred - i) • x.snd)).sum⟩

-- override the simple implementation with npowFast
-- this allows it to use the optimzed impl from the underlying types
-- for code generation, while keeping the simple to reason about
-- version for theorem proving. And we have convert to the opt
-- impl using fst_npow and snd_npow while theorem proving
@[csimp]
def npow'_eq_npowFast' : @npow' = @npowFast' := by
  ext
  apply fst_npow'
  apply snd_npow'

instance : Pow (TrivSqZeroExt R M) ℕ := ⟨flip npow'⟩

instance monoid : IsMonoid (TrivSqZeroExt R M) where
    mul_assoc a b c := by
      ext <;> simp
      rw [mul_assoc]
      simp [mul_smul, smul_add, add_assoc]
      congr 1
      rw [smul_comm]

@[simp]
def fst_npow (x: TrivSqZeroExt R M) (n: ℕ) : fst (x ^ n) = x.fst ^ n := fst_npow' x n

@[simp]
def snd_npow (x: TrivSqZeroExt R M) (n: ℕ) : snd (npow' n x) = ((List.range n).map fun i => MulOpp.mk (x.fst ^ i) • (x.fst ^ (n.pred - i) • x.snd)).sum := snd_npow' x n

end

instance [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsModule R M] [h: IsModule Rᵐᵒᵖ M] : IsNonAssocSemiring (TrivSqZeroExt R M) :=
  {
    instMulOneClass, instAddMonoidWithOne with
    zero_mul a := by ext <;> simp [zero_mul, zero_smul, smul_zero, add_zero]
    mul_zero a := by ext <;> simp [mul_zero, zero_smul, smul_zero, add_zero]
    left_distrib k a b := by
      ext <;> simp [mul_add, smul_add, add_smul]
      ac_rfl
    right_distrib a b k := by
      ext <;> simp [add_mul, smul_add, add_smul]
      ac_rfl
  }

instance [RingOps R] [IsRing R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsModule R M] [h: IsModule Rᵐᵒᵖ M] : IsNonAssocRing (TrivSqZeroExt R M) := inferInstance

/-- The canonical inclusion of rings `R → TrivSqZeroExt R M`. -/
def inlHom [SemiringOps R] [IsSemiring R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [SMul R M] [SMul Rᵐᵒᵖ M] [IsModule R M] [IsModule Rᵐᵒᵖ M] : R →+* TrivSqZeroExt R M where
  toFun := inl
  resp_zero := by intros; rfl
  resp_one := by intros; rfl
  resp_add := by
    intro a b
    ext <;> simp [add_zero]
  resp_mul := by
    intro a b
    ext <;> simp [smul_zero]
    rfl

end Mul

-- a shortcut instance, since this is slow to infer
instance
  [SemiringOps R] [AddMonoidOps M]
  [IsSemiring R] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M]
  [IsDistribMulAction R M]
  [IsDistribMulAction Rᵐᵒᵖ M] : SemiringOps (TrivSqZeroExt R M) := inferInstance

instance
  [SemiringOps R] [AddMonoidOps M]
  [IsSemiring R] [IsAddMonoid M] [IsAddCommMagma M]
  [SMul R M] [SMul Rᵐᵒᵖ M]
  [IsModule R M]
  [IsModule Rᵐᵒᵖ M]
  [IsSMulComm Rᵐᵒᵖ R M] : IsSemiring (TrivSqZeroExt R M) where
  add_comm a b := by ext <;> simp [add_comm]
  mul_assoc a b c := by ext <;> simp [mul_assoc]
  zero_mul a := by ext <;> simp [zero_mul]
  mul_zero a := by ext <;> simp [mul_zero]
  left_distrib k a b := by ext <;> simp [mul_add]
  right_distrib a b k := by ext <;> simp [add_mul]

instance
  [SemiringOps R] [AddMonoidOps M]
  [IsSemiring R] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M]
  [IsDistribMulAction R M]
  [IsDistribMulAction Rᵐᵒᵖ M] : AlgebraMap R (TrivSqZeroExt R M) where
  toFun := inl
  resp_zero := rfl
  resp_one := rfl
  resp_add := by
    intro x y
    ext <;> simp [add_zero]
  resp_mul := by
    intro x y
    ext <;> simp [add_zero, smul_zero]

def algebraMap_eq_inl
  [SemiringOps R] [AddMonoidOps M]
  [IsSemiring R] [IsAddMonoid M]
  [SMul R M] [SMul Rᵐᵒᵖ M]
  [IsDistribMulAction R M]
  [IsDistribMulAction Rᵐᵒᵖ M] :
  (DFunLike.coe algebraMap) = inl (R := R) (M := M) := rfl


instance
  [SemiringOps R] [AddMonoidOps M]
  [IsSemiring R] [IsAddMonoid M]
  [IsCommMagma R] [IsAddCommMagma M]
  [SMul R M] [SMul Rᵐᵒᵖ M]
  [IsModule R M]
  [IsModule Rᵐᵒᵖ M]
  [IsCentralScalar R M]
  [IsSMulComm Rᵐᵒᵖ R M] : IsAlgebra R (TrivSqZeroExt R M) where
  commutes r x := by
    ext <;> simp [algebraMap_eq_inl]
    apply mul_comm r x.fst
    rw [op_smul_eq_smul]
  smul_def r x := by ext <;> simp [algebraMap_eq_inl]

end TrivSqZeroExt
