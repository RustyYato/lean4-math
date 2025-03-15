import Math.Algebra.Module.SetLike.Lattice
import Math.Algebra.Field.Defs
import Math.Data.List.Algebra
import Math.Algebra.Group.Action.Basic
import Math.Data.FinSupp.Algebra

namespace Submodule

section Defs

namespace LinearCombination

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M]

def _root_.Submodule.LinearCombination (R M: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M] [DecidableEq M]
  := Finsupp M R (Finset M)

instance : Zero (LinearCombination R M) :=
  inferInstanceAs (Zero (Finsupp _ _ _))
instance : Add (LinearCombination R M) :=
  inferInstanceAs (Add (Finsupp _ _ _))
instance : SMul R (LinearCombination R M) :=
  inferInstanceAs (SMul R (Finsupp _ _ _))

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

def single (r: R) (m: M) : LinearCombination R M := Finsupp.single m r

@[simp]
def single_val (r: R) (m: M) : (single r m).val = r • m := by
  unfold val single
  rw [Finsupp.single_sum]

def support [∀r: R, Decidable (r = 0)] (f: LinearCombination R M) : Finset M := Finsupp.support f

instance : CoeTC (LinearCombination R M) M := ⟨LinearCombination.val⟩
instance : FunLike (LinearCombination R M) M R := inferInstanceAs (FunLike (Finsupp M R _) M R)

def mem_support [∀r: R, Decidable (r = 0)] {f: LinearCombination R M} :
  ∀{x: M}, x ∈ f.support ↔ f x ≠ 0 := Finsupp.mem_support

def apply_single {m: M} {r: R} (x: M) : single r m x = if x = m then r else 0 := rfl

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

open Classical

variable {M: Type*} (R: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

-- the span of a set is the set of all vectors that are made from
-- linear combinations of members of the set
def span (U: Set M) : Submodule R M where
  carrier := Set.mk fun v => ∃f: LinearCombination R M, (∀x, x ∈ f.support -> x ∈ U) ∧ v = f
  mem_zero' := ⟨0, by
    intro v h
    rw [LinearCombination.mem_support] at h
    contradiction , rfl⟩
  mem_add' := by
    rintro a b ⟨fa, ha, rfl⟩ ⟨fb, hb, rfl⟩
    exists fa + fb
    apply And.intro
    · intro v h
      rw [LinearCombination.mem_support] at h
      replace h : fa v + fb v ≠ 0 := h
      by_cases g:fa v = 0
      rw [g] at h
      simp at h
      apply hb v
      rw [LinearCombination.mem_support]
      assumption
      apply ha v
      rw [LinearCombination.mem_support]
      assumption
    · simp
  mem_smul' := by
    rintro r _ ⟨f, hf, rfl⟩
    exists r • f
    apply And.intro
    · intro v h
      rw [LinearCombination.mem_support] at h
      replace h : r • f v ≠ 0 := h
      by_cases g:f v = 0
      rw [g] at h
      simp at h
      apply hf
      rw [LinearCombination.mem_support]
      assumption
    · simp

def mem_span_of (U: Set M) : ∀x ∈ U, x ∈ span R U := by
  intro x h
  exists LinearCombination.single 1 x
  apply And.intro
  intro y hy
  cases List.mem_singleton.mp (Finsupp.support_single _ hy)
  assumption
  simp

def span_eq_generate (U: Set M) : span R U = generate U := by
  ext x
  apply Iff.intro
  · rintro ⟨f, h, rfl⟩
    induction f with
    | zero =>
      apply mem_zero
    | add f₀ f₁ h₀ h₁ g =>
      rw [LinearCombination.add_val]
      apply mem_add
      · apply h₀
        intro x hx
        apply h
        rw [LinearCombination.mem_support] at *
        intro eq
        have := (g _ eq).left
        contradiction
      · apply h₁
        intro x hx
        apply h
        rw [LinearCombination.mem_support] at *
        intro eq
        have := (g _ eq).right
        contradiction
    | single r m =>
      show LinearCombination.val (LinearCombination.single _ _) ∈ _
      rw [LinearCombination.single_val]
      by_cases hb:r = 0
      subst hb
      rw [zero_smul]
      apply mem_zero
      apply mem_smul
      apply Generate.of
      apply h m
      rw [LinearCombination.mem_support, LinearCombination.apply_single, if_pos rfl]
      assumption
  · intro h
    apply of_mem_generate _ _ _ _ h
    intro v hv
    apply mem_span_of
    assumption

-- a set is linearly independent if every non-trivial linear combination is non-zero
def linindep (U: Set M) := ∀f: LinearCombination R M,
  Set.support f ⊆ U -> f.val = 0 -> f = 0

end Defs

end Submodule
