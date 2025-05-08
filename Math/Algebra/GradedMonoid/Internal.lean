import Math.Algebra.GradedMonoid.Defs
import Math.Data.Set.Like

namespace SetLike

variable {S: Type*} [SetLike S R] (A: ι -> S)

class GradedOne [One R] [Zero ι] : Prop where
  mem_one: 1 ∈ A 0

class GradedMul [Mul R] [Add ι] : Prop where
  mem_mul: ∀{i₀ i₁: ι} (a b: R),
    a ∈ A i₀ -> b ∈ A i₁ ->
    a * b ∈ A (i₀ + i₁)

def _root_.gmem_one [One R] [Zero ι] [GradedOne A] : (1: R) ∈ A 0 := GradedOne.mem_one
def _root_.gmem_mul [Mul R] [Add ι] [GradedMul A] : ∀{i₀ i₁: ι} (a b: R),
    a ∈ A i₀ -> b ∈ A i₁ ->
    a * b ∈ A (i₀ + i₁) := GradedMul.mem_mul

instance [Zero ι] [One R] [GradedOne A] : GOne (fun i => A i) where
  gOne := ⟨1, gmem_one A⟩

instance [Add ι] [Mul R] [GradedMul A] : GMul (fun i => A i) where
  gMul a b := ⟨a.val * b.val, gmem_mul A _ _ a.property b.property⟩

variable [AddMonoidOps ι] [IsAddMonoid ι] [MonoidOps R] [IsMonoid R] [GradedOne A] [GradedMul A]

def _root_.gmem_npow: ∀(n: ℕ) {i: ι} (a: R), a ∈ A i -> a ^ n ∈ A (n • i) := by
  intro n i a h
  induction n with
    | zero => rw [npow_zero, zero_nsmul]; apply gmem_one
    | succ n ih =>
      rw [npow_succ, succ_nsmul]
      apply gmem_mul
      assumption
      exact h

instance : GPow (fun i => A i) where
  gPow n i a := {
    val := a.val ^ n
    property := by
      apply gmem_npow
      exact a.property
  }

@[ext]
private def ext' (a b: GradedMonoid fun i => ↑(A i)) : a.fst = b.fst -> a.snd.val = b.snd.val -> a = b := by
  intro h g; ext
  assumption
  obtain ⟨_, a, _⟩ := a
  obtain ⟨_, b, _⟩ := b
  simp
  cases h; cases g
  rfl

instance instGMonoidOps : GMonoidOps (fun i => A i) := inferInstance

instance instIsGMonoid : IsGMonoid (fun i => A i) where
  mul_assoc a b c := by
    ext; apply add_assoc
    apply mul_assoc
  one_mul a := by
    ext; apply zero_add
    apply one_mul
  mul_one a := by
    ext; apply add_zero
    apply mul_one
  npow_zero a := by
    ext; apply zero_nsmul
    apply npow_zero
  npow_succ n a := by
    ext; apply succ_nsmul
    apply npow_succ

instance instIsGCommMagma [IsAddCommMagma ι] [IsCommMagma R] : IsGCommMagma (fun i => A i) where
  mul_comm a b := by
    ext; apply add_comm
    apply mul_comm



end SetLike
