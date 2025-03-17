import Math.Algebra.Module.LinearCombo.Defs
import Math.Data.Set.Like

structure LinearSpan (R M: Type*) (s: S) [SetLike S M] [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M] [DecidableEq M] where
  ofCombo ::
  toCombo : LinearCombination R M
  subS: Set.support toCombo ⊆ s

namespace LinearSpan

section

variable {R M: Type*} {s: S} [SetLike S M] [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M]

instance : FunLike (LinearSpan R M s) M R where
  coe a := a.toCombo
  coe_inj := by
    intro a b eq; cases a; cases b; congr
    apply DFunLike.coe_inj
    assumption

@[ext]
def ext (a b: LinearSpan R M s) : (∀m, a m = b m) -> a = b :=
  DFunLike.ext _ _

instance : Zero (LinearSpan R M s) where
  zero := {
    toCombo := 0
    subS := by intro _ _; contradiction
  }
instance : Add (LinearSpan R M s) where
  add a b := {
    toCombo := a.toCombo + b.toCombo
    subS := by
      suffices h:Set.support (a.toCombo + b.toCombo) ⊆ Set.support a.toCombo ∪ Set.support b.toCombo by
        suffices g:Set.support a.toCombo ∪ Set.support b.toCombo ⊆ s by
          intro m hm
          apply g
          apply h
          assumption
        intro x h; cases h
        apply a.subS
        assumption
        apply b.subS
        assumption
      intro x h
      simp [Set.mem_support, Set.mem_union] at *
      apply Classical.byContradiction
      intro g
      simp at g
      rw [g.left, g.right] at h
      simp at h
  }
instance : SMul ℕ (LinearSpan R M s) where
  smul n a := {
    toCombo := n • a.toCombo
    subS := by
      intro m h
      rw [Set.mem_support] at h
      simp at h
      apply a.subS m
      rw [Set.mem_support]
      intro g
      rw [g] at h
      simp at h
  }
instance : SMul R (LinearSpan R M s) where
  smul r a := {
    toCombo := r • a.toCombo
    subS := by
      intro m h
      rw [Set.mem_support] at h
      simp at h
      apply a.subS m
      rw [Set.mem_support]
      intro g
      rw [g] at h
      simp at h
  }

instance : IsAddMonoid (LinearSpan R M s) where
  add_assoc _ _ _ := by ext; apply add_assoc
  zero_add _ := by ext; apply zero_add
  add_zero _ := by ext; apply add_zero
  zero_nsmul _ := by ext; apply zero_nsmul
  succ_nsmul _ _ := by ext; apply succ_nsmul
instance : IsAddCommMagma (LinearSpan R M s) where
  add_comm _ _ :=  by ext; apply add_comm
instance : IsModule R (LinearSpan R M s) where
  add_smul _ _ _ := by ext; apply add_mul
  one_smul _ := by ext; apply one_mul
  mul_smul _ _ _ := by ext; apply mul_assoc
  smul_zero _ := by ext; apply mul_zero
  smul_add _ _ _ := by ext; apply mul_add
  zero_smul _ :=  by ext; apply zero_mul

@[simp] def apply_add (a b: LinearSpan R M s) (m: M) : (a + b) m = a m + b m := rfl
@[simp] def apply_nsmul (a: LinearSpan R M s) (n: ℕ) (m: M) : (n • a) m = n • a m := rfl
@[simp] def apply_smul (a: LinearSpan R M s) (n: R) (m: M) : (n • a) m = n • a m := rfl

def toLinearCombo : LinearSpan R M s ↪ₗ[R] LinearCombination R M where
  toFun := LinearSpan.toCombo
  inj' := by intro a b eq; cases a; congr
  resp_add := rfl
  resp_smul := rfl

def valHom : LinearSpan R M s →ₗ[R] M :=
  LinearCombination.valHom.comp toLinearCombo.toLinearMap

def single (r: R) (m: M) (h: m ∈ s) : LinearSpan R M s where
  toCombo := LinearCombination.single r m
  subS := by
    intro x h
    rcases LinearCombination.support_single r m with g | g
    rw [g] at h
    contradiction
    rw [g] at h
    subst x
    assumption

def apply_single {m: M} {r: R} {h: m ∈ s} (x: M) : single r m h x = if x = m then r else 0 := rfl

@[induction_eliminator]
def induction {motive: LinearSpan R M s -> Prop}
  (zero: motive 0)
  (single: ∀r m h, r ≠ 0 -> motive (single r m h))
  (add: ∀a b,
    motive a ->
    motive b ->
    Set.support (a + b) = Set.support a ∪ Set.support b ->
    (a + b = 0 -> a = 0 ∧ b = 0) ->
    motive (a + b)) : ∀a, motive a := by
  intro ⟨a, ha⟩
  induction a with
  | zero => apply zero
  | add a b ih₀ ih₁ h₀ h =>
    rw [h₀] at ha
    apply add ⟨_, _⟩ ⟨_, _⟩
    apply ih₀
    apply ih₁
    assumption
    intro x
    have := h (LinearSpan.ofCombo.inj x)
    apply And.intro
    congr; exact this.left
    congr; exact this.right
    apply Set.sub_trans _ ha
    apply Set.sub_union_left
    apply Set.sub_trans _ ha
    apply Set.sub_union_right
  | single r m =>
    apply single
    rcases LinearCombination.support_single r m with h | h
    rw [h] at ha
    have : m ∈ Set.support (LinearCombination.single r m) := by
      intro g
      simp [Set.mem_preimage, LinearCombination.apply_single] at g
      contradiction
    rw [h] at this
    contradiction
    apply ha
    rw [h]; rfl
    assumption

instance : CoeTC (LinearSpan R M s) M := ⟨valHom⟩

@[simp]
def single_valHom (r: R) (m: M) (hm: m ∈ s) : valHom (single r m hm) = r • m := LinearCombination.single_valHom _ _



end

section

variable {R M: Type*} {s: S} [SetLike S M] [RingOps R] [IsRing R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M]

instance : Neg (LinearSpan R M s) where
  neg a := {
    toCombo := -a.toCombo
    subS := by
      intro m h
      apply a.subS
      intro g; rw [Set.mem_preimage] at g
      simp [Set.mem_support] at h
      rw [g, neg_zero] at h
      contradiction
  }
instance : Sub (LinearSpan R M s) where
  sub a b := {
    toCombo := a.toCombo - b.toCombo
    subS := by
      rw [sub_eq_add_neg]
      exact (a + -b).subS
  }
instance : SMul ℤ (LinearSpan R M s) where
  smul n a := {
    toCombo := n • a.toCombo
    subS := by
      intro m h
      rw [Set.mem_support] at h
      simp at h
      apply a.subS m
      rw [Set.mem_support]
      intro g
      rw [g] at h
      simp at h
  }

instance : IsAddGroup (LinearSpan R M s) where
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  neg_add_cancel _ := by ext; apply neg_add_cancel
  zsmul_ofNat _ _ := by ext; apply zsmul_ofNat
  zsmul_negSucc _ _ := by ext; apply zsmul_negSucc

@[simp] def apply_sub (a b: LinearSpan R M s) (m: M) : (a - b) m = a m - b m := rfl
@[simp] def apply_neg (a: LinearSpan R M s) (m: M) : (-a) m = -a m := rfl
@[simp] def apply_zsmul (a: LinearSpan R M s) (n: ℤ) (m: M) : (n • a) m = n • a m := rfl

end

end LinearSpan
