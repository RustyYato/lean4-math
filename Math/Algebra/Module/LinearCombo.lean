import Math.Data.FinSupp.Algebra
import Math.Algebra.Hom

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M]

def LinearCombination (R M: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M] [DecidableEq M]
  := Finsupp M R (Finset M)

namespace LinearCombination

instance : Zero (LinearCombination R M) :=
  inferInstanceAs (Zero (Finsupp _ _ _))
instance : Add (LinearCombination R M) :=
  inferInstanceAs (Add (Finsupp _ _ _))
instance : SMul ℕ (LinearCombination R M) :=
  inferInstanceAs (SMul ℕ (Finsupp _ _ _))
instance : SMul R (LinearCombination R M) :=
  inferInstanceAs (SMul R (Finsupp _ _ _))

instance : IsAddMonoid (LinearCombination R M) :=
  inferInstanceAs (IsAddMonoid (Finsupp _ _ _))
instance : IsAddCommMagma (LinearCombination R M) :=
  inferInstanceAs (IsAddCommMagma (Finsupp _ _ _))
instance : IsModule R (LinearCombination R M) :=
  inferInstanceAs (IsModule R (Finsupp _ _ _))

def val (f: LinearCombination R M) := f.sum (fun v r => r • v) (fun v h => by simp [h])

@[simp]
def zero_val : (0 : LinearCombination R M).val = 0 := rfl

@[simp]
def add_val (a b: LinearCombination R M) : (a + b).val = a.val + b.val := by
  unfold val
  rw [Finsupp.add_sum]
  intro v a b
  rw [add_smul]

@[simp]
def smul_val (r: R) (a: LinearCombination R M) : (r • a).val = r • a.val := by
  unfold val
  let g : M →+ M := {
    toFun x := r • x
    resp_zero := by simp
    resp_add {x y} := smul_add _ _ _
  }
  show _ = g (a.sum _ _)
  rw [Finsupp.resp_sum]
  apply Finsupp.sum_eq_pairwise
  intro i
  show _ =  r • _
  rw [←mul_smul]
  rfl

def valHom : LinearCombination R M →ₗ[R] M where
  toFun := val
  resp_add := add_val _ _
  resp_smul := smul_val _ _

def single (r: R) (m: M) : LinearCombination R M := Finsupp.single m r

@[simp]
def single_val (r: R) (m: M) : (single r m).val = r • m := by
  unfold val single
  rw [Finsupp.single_sum]

@[simp]
def single_valHom (r: R) (m: M) : valHom (single r m) = r • m :=
  single_val _ _

instance : CoeTC (LinearCombination R M) M := ⟨valHom⟩
instance : FunLike (LinearCombination R M) M R := inferInstanceAs (FunLike (Finsupp M R _) M R)

def apply_single {m: M} {r: R} (x: M) : single r m x = if x = m then r else 0 := rfl

def mem_support_single {r: R} {m x: M} : x ∈ Set.support (single r m) -> r ≠ 0 ∧ x = m := by
  rintro h
  rw [Set.mem_support, apply_single] at h
  split at h
  trivial
  contradiction

@[induction_eliminator]
def induction
  {motive: LinearCombination R M -> Prop}
  (zero: motive 0)
  (single: ∀r m, motive (single r m))
  (add: ∀a b,
    motive a ->
    motive b ->
    (∀x, a x + b x = 0 -> a x = 0 ∧ b x = 0) ->
    motive (a + b)):
    ∀l, motive l := by
    apply Finsupp.induction zero
    intros ; apply single
    assumption

end LinearCombination
