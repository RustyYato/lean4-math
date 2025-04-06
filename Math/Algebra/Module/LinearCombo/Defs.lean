import Math.Data.FinSupp.Algebra
import Math.Algebra.Algebra.Hom

def LinearCombination (R M: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M] [DecidableEq M]
  := Finsupp M R (Finset M)

namespace LinearCombination

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M]

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

def valHom : LinearCombination R M →ₗ[R] M where
  toFun f := f.sum (fun v r => r • v) (fun v h => by simp [h])
  map_add := by
    intro a b
    dsimp
    rw [Finsupp.add_sum]
    intro v a b
    rw [add_smul]
  map_smul := by
    intro r a
    dsimp
    let g : M →+ M := {
      toFun x := r • x
      map_zero := by simp
      map_add {x y} := smul_add _ _ _
    }
    show _ = g (a.sum _ _)
    rw [Finsupp.map_sum]
    apply Finsupp.sum_eq_pairwise
    intro i
    show _ =  r • _
    rw [←mul_smul]
    rfl

@[coe]
abbrev val (f: LinearCombination R M) := valHom f

@[simp]
def zero_val : (0 : LinearCombination R M).val = 0 := rfl

@[simp]
def add_val (a b: LinearCombination R M) : (a + b).val = a.val + b.val := map_add _

@[simp]
def smul_val (r: R) (a: LinearCombination R M) : (r • a).val = r • a.val := map_smul _

def single (r: R) (m: M) : LinearCombination R M := Finsupp.single m r

@[simp]
def single_valHom (r: R) (m: M) : valHom (single r m) = r • m := by
  simp [valHom, single, DFunLike.coe, Finsupp.single_sum]

@[simp]
def single_val (r: R) (m: M) : (single r m).val = r • m := single_valHom _ _

instance : CoeTC (LinearCombination R M) M := ⟨valHom⟩
instance : FunLike (LinearCombination R M) M R := inferInstanceAs (FunLike (Finsupp M R _) M R)

@[simp] def apply_add (a b: LinearCombination R M) (m: M) : (a + b) m = a m + b m := rfl
@[simp] def apply_nsmul (a: LinearCombination R M) (n: ℕ) (m: M) : (n • a) m = n • a m := rfl
@[simp] def apply_smul (a: LinearCombination R M) (n: R) (m: M) : (n • a) m = n • a m := rfl

def apply_single {m: M} {r: R} (x: M) : single r m x = if x = m then r else 0 := rfl

def mem_support_single {r: R} {m x: M} : x ∈ Set.support (single r m) -> r ≠ 0 ∧ x = m := by
  rintro h
  rw [Set.mem_support, apply_single] at h
  split at h
  trivial
  contradiction

def of_empty_support (a: LinearCombination R M) :
  Set.support a = ∅ -> a = 0 := by
  intro supp_eq
  apply Finsupp.ext
  intro m
  apply Classical.byContradiction
  intro hm
  suffices m ∈ Set.support a by
    rw [supp_eq] at this
    contradiction
  rwa [Set.mem_support]

@[ext]
def ext (a b: LinearCombination R M) : (∀m, a m = b m) -> a = b :=
  Finsupp.ext _ _

@[induction_eliminator]
def induction
  {motive: LinearCombination R M -> Prop}
  (zero: motive 0)
  (single: ∀r m, r ≠ 0 -> motive (single r m))
  (add: ∀a b,
    motive a ->
    motive b ->
    Set.support (a + b) = Set.support a ∪ Set.support b ->
    (a + b = 0 -> a = 0 ∧ b = 0) ->
    motive (a + b)):
    ∀l, motive l := by
    apply Finsupp.induction zero
    intros m r
    by_cases hr:r = 0
    show motive (LinearCombination.single _ _)
    rw [hr, show LinearCombination.single (0: R) m = 0 from ?_]
    apply zero
    ext; rw [apply_single]; split <;> rfl
    apply single
    assumption
    intro a b ha hb h
    apply add
    assumption
    assumption
    ext m
    simp [Set.mem_support, Set.mem_union]
    rw [Classical.not_iff_not, not_or, Classical.not_not, Classical.not_not, Classical.not_not]
    apply Iff.intro
    apply h
    intro ⟨h, g⟩
    show a m + b m = 0
    simp [h, g]
    intro g
    apply And.intro
    ext m
    exact (h m (by
      show (a + b) m = 0
      rw [g]; rfl)).left
    ext m
    exact (h m (by
      show (a + b) m = 0
      rw [g]; rfl)).right

def support_single (r: R) (m: M) : Set.support (single r m) = ∅ ∨ Set.support (single r m) = {m} := by
  by_cases h:r = 0
  subst r
  left;
  apply Set.ext_empty
  intro x hx
  rw [Set.mem_support, apply_single] at hx
  split at hx <;> contradiction
  right
  ext
  simp [Set.mem_support, apply_single]
  intro; assumption

end LinearCombination

namespace LinearCombination

variable {R M: Type*} [RingOps R] [IsRing R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M]

instance : Neg (LinearCombination R M) :=
  inferInstanceAs (Neg (Finsupp _ _ _))
instance : Sub (LinearCombination R M) :=
  inferInstanceAs (Sub (Finsupp _ _ _))
instance : SMul ℤ (LinearCombination R M) :=
  inferInstanceAs (SMul ℤ (Finsupp _ _ _))
instance : IsAddGroup (LinearCombination R M) :=
  inferInstanceAs (IsAddGroup (Finsupp _ _ _))

@[simp] def apply_sub (a b: LinearCombination R M) (m: M) : (a - b) m = a m - b m := rfl
@[simp] def apply_neg (a: LinearCombination R M) (m: M) : (-a) m = -a m := rfl
@[simp] def apply_zsmul (a: LinearCombination R M) (n: ℤ) (m: M) : (n • a) m = n • a m := rfl

end LinearCombination
