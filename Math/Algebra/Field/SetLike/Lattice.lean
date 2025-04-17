import Math.Data.Set.Like.Lattice
import Math.Algebra.Field.SetLike.Defs
import Math.Algebra.GroupWithZero.SetLike.Basic
import Math.Algebra.AddGroupWithOne.SetLike.Basic
import Math.Algebra.Field.Basic

namespace Subfield

variable [FieldOps α] [IsField α]

private instance builder : SetLike.LatticeBuilder (Subfield α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_zero := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_zero s
    mem_one := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_one s
    mem_neg := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_neg s <;> assumption
    mem_inv?' := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_inv? s <;> assumption
    mem_add := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_add s <;> assumption
    mem_mul := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_mul s <;> assumption
  }
  gc := by
    intro s t
    apply flip Iff.intro
    intro h x hx
    apply h
    apply Generate.of
    assumption
    intro h x hx
    induction hx with
    | of => apply h; assumption
    | zero => apply mem_zero t
    | one => apply mem_one t
    | neg => apply mem_neg t <;> assumption
    | inv? => apply mem_inv? t <;> assumption
    | add => apply mem_add t <;> assumption
    | mul => apply mem_mul t <;> assumption

private local instance : SetLike.CompleteLatticeLE (Subfield α) := SetLike.toCompleteLattice

instance : LE (Subfield α) := inferInstance
instance : LT (Subfield α) := inferInstance
instance : Top (Subfield α) := inferInstance
instance : Bot (Subfield α) := inferInstance
instance : Max (Subfield α) := inferInstance
instance : Min (Subfield α) := inferInstance
instance : SupSet (Subfield α) := inferInstance
instance : InfSet (Subfield α) := inferInstance
instance : IsPartialOrder (Subfield α) := inferInstance
instance : IsCompleteLattice (Subfield α) := inferInstance

def mem_bot_iff (a: α) : a ∈ (⊥: Subfield α) ↔ ∃a': ℤ × ℕ, ∃h: (a'.2: α) ≠ 0, a = (a'.1: α) /? a'.2 := by
  apply Iff.intro
  intro h
  · suffices ∃a': ℤ × ℤ, ∃h: (a'.2: α) ≠ 0, a = (a'.1: α) /? a'.2 by
      obtain ⟨⟨x, y⟩, h, g⟩ := this
      simp at g
      simp at h
      refine ⟨(x * y.sign, y.natAbs), ?_, ?_⟩
      simp
      rcases Int.natAbs_eq y with h₀ | h₀
      rwa [←intCast_ofNat, ←h₀]
      rwa [←neg_inj, ←intCast_ofNat, intCast_neg,←h₀, neg_zero]
      simp
      rw [g]
      apply of_mul_right_nonzero
      assumption
      rw [div?_mul_cancel]
      conv => { rhs; rhs; rw [←y.sign_mul_natAbs] }
      rw [mul_comm y.sign, ←intCast_mul, ←intCast_mul]
      conv => { rhs; rhs; lhs; rw [intCast_ofNat] }
      rw [←mul_assoc, div?_mul_cancel,
        intCast_mul, intCast_mul, mul_assoc,
        ←Int.sign_mul, Int.sign_eq_one_iff_pos.mpr, mul_one]
      have : y ≠ 0 := by
        rintro rfl
        rw [intCast_zero] at h; contradiction
      refine Int.sign_eq_one_iff_pos.mp ?_
      rw [Int.sign_mul]
      rw [← Int.ediv_sign, Int.ediv_self]
      intro h
      rw [Int.sign_eq_zero_iff_zero] at h
      contradiction
    induction h with
    | of => contradiction
    | zero =>
      refine ⟨(0,1), ?_, ?_⟩
      simp; rw [intCast_one]
      exact (zero_ne_one _).symm
      simp [intCast_zero]
    | one =>
      refine ⟨(1,1), ?_, ?_⟩
      simp; rw [intCast_one]
      exact (zero_ne_one _).symm
      simp [intCast_one]
    | inv? _ _ ih =>
      obtain ⟨⟨a, b⟩, h, g⟩ := ih
      simp at g
      refine ⟨⟨b, a⟩, ?_, ?_⟩
      simp; intro ha
      simp at h
      rw [ha] at g
      simp at g
      contradiction
      rename_i a' ha' _
      subst a'
      simp
      rw [inv?_div?]
    | neg _ ih =>
      obtain ⟨⟨a, b⟩, h, g⟩ := ih
      refine ⟨⟨-a, b⟩, h, ?_⟩
      simp
      rw [g, div?_eq_mul_inv?, div?_eq_mul_inv?, ←neg_mul,
        intCast_neg]
    | mul _ _ ih₀ ih₁ =>
      obtain ⟨⟨a, b⟩, h₀, g₀⟩ := ih₀
      obtain ⟨⟨c, d⟩, h₁, g₁⟩ := ih₁
      subst g₀; subst g₁
      simp only
      refine ⟨⟨a * c, b * d⟩, ?_, ?_⟩
      simp; intro h
      rw [←intCast_mul] at h
      cases of_mul_eq_zero h
      contradiction
      contradiction
      rw [mul_div?_mul]
      simp
      congr
      rw [intCast_mul]
      rw [intCast_mul]
    | add _ _ ih₀ ih₁ =>
      obtain ⟨⟨a, b⟩, h₀, g₀⟩ := ih₀
      obtain ⟨⟨c, d⟩, h₁, g₁⟩ := ih₁
      subst g₀; subst g₁
      simp only
      refine ⟨⟨d * a + b * c, b * d⟩, ?_, ?_⟩
      simp; intro h
      rw [←intCast_mul] at h
      cases of_mul_eq_zero h
      contradiction
      contradiction
      rw [add_div?_add]
      simp
      congr
      norm_cast
      norm_cast
  · rintro ⟨⟨a, b⟩, h, rfl⟩
    simp
    apply mem_div?
    apply mem_intCast
    apply mem_natCast

end Subfield
