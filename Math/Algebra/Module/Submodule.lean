import Math.Algebra.Module.SetLike.Lattice
import Math.Algebra.Field.Defs
import Math.Algebra.Group.SetLike.Defs
import Math.Algebra.Group.Action.Basic
import Math.Algebra.Module.LinearCombo.Defs
import Math.Logic.Fact

namespace Submodule

section Defs

-- open Classical

variable {M: Type*} (R: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
  [DecidableEq M]

-- the span of a set is the set of all vectors that are made from
-- linear combinations of members of the set
def span (U: Set M) : Submodule R M where
  carrier := Set.mk fun v => ∃f: LinearCombo R U, v = f
  mem_zero := ⟨0, (map_zero _).symm⟩
  mem_add := by
    rintro a b ⟨fa, ha, rfl⟩ ⟨fb, hb, rfl⟩
    exists fa + fb
    rw [map_add]
  mem_smul' := by
    rintro r _ ⟨f, hf, rfl⟩
    exists r • f
    rw [map_smul]

def mem_span_of (U: Set M) : ∀x ∈ U, x ∈ span R U := by
  intro x h
  exists LinearCombo.single 1 x h
  simp

def mem_span_of_linear_combo_sub {U s: Set M} (h: s ⊆ U) : ∀x: LinearCombo R s, (x: M) ∈ span R U := by
  intro x
  induction x with
  | zero =>
    rw [map_zero]
    apply mem_zero
  | ι =>
    rw [LinearCombo.valHom_ι]
    apply mem_span_of
    apply h
    assumption
  | smul r x hx ih =>
    rw [map_smul]
    apply mem_smul
    assumption
  | add =>
    rw [map_add]
    apply mem_add
    assumption
    assumption

def mem_span_of_linear_combo (U: Set M) : ∀x: LinearCombo R U, (x: M) ∈ span R U := by
  apply mem_span_of_linear_combo_sub
  rfl

def span_eq_generate (U: Set M) : span R U = generate U := by
  ext x
  apply Iff.intro
  · rintro ⟨f, h, rfl⟩
    induction f with
    | zero =>
      rw [map_zero]
      apply mem_zero
    | add f₀ f₁ h₀ h₁ =>
      rw [map_add]
      apply mem_add
      assumption
      assumption
    | ι m hm =>
      apply Generate.of
      rw [LinearCombo.valHom_ι]
      assumption
    | smul r x hr ih =>
      rw [map_smul]
      apply mem_smul
      assumption
  · intro h
    apply of_mem_generate _ _ _ _ h
    intro v hv
    apply mem_span_of
    assumption

-- a set is linearly independent if every non-trivial linear combination is non-zero
def IsLinindep (U: Set M) := Function.Injective (fun l: LinearCombo R U => (l: M))

end Defs

section

variable (R M: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
  [DecidableEq M]

class IsBasis (S: Type*) [SetLike S M] : Prop where
  indep (U: S): IsLinindep R (U: Set M)
  complete (U: S): ∀m, m ∈ span R (U: Set M)

instance [SetLike S M] [b: IsBasis R M S] (U: S) : Fact (IsLinindep R (U: Set M)) where
  proof := b.indep _

structure Basis where
  carrier: Set M
  indep: IsLinindep R (carrier: Set M)
  complete: ∀m, m ∈ span R (carrier: Set M)

instance : SetLike (Basis R M) M where
  coe b := b.carrier
  coe_inj := by intro a b eq; cases a; congr

@[ext]
def Basis.ext (a b: Basis R M) : (∀{x}, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

instance : IsBasis R M (Basis R M) where
  indep b := b.indep
  complete b := b.complete

end

section

variable {M: Type*} (R: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
  [DecidableEq M]

def is_linear_indep (U: Set M) [Fact (IsLinindep R U)] : IsLinindep R U := of_fact _
def is_complete [SetLike S M] [b: IsBasis R M S] (U: S) : ∀m, m ∈ span R (U: Set M) := b.complete _

end

section

variable {R M: Type*} [RingOps R] [IsRing R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
  [DecidableEq M]

instance : IsNegMem (Submodule R M) where
  mem_neg s {a} h := by
    rw [←one_smul (R := R) a, ←neg_smul]
    apply mem_smul
    assumption

def is_linindep_iff_kernel_zero (U: Set M) : IsLinindep R U ↔ ∀f: LinearCombo R U, (f: M) = 0 -> f = 0 := by
  apply Iff.intro
  · intro h f g
    apply h
    simp
    assumption
  · intro h x y g
    apply eq_of_sub_eq_zero
    apply h
    rw [map_sub]
    simp at g
    rw [g, sub_self]

end

section

variable {R M: Type*} [FieldOps R] [IsField R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
  [DecidableEq M]

def insertLinindep (S: Set M) (hS: Submodule.IsLinindep R S) (m: M) (hm: m ∉ Submodule.span R S) : Submodule.IsLinindep R (insert m S) := by
  classical
  rw [is_linindep_iff_kernel_zero] at *
  intro C eq
  let C' := (C.erase m).cast (by
      rw [Set.insert_sdiff]
      intro h; apply hm
      rw [span_eq_generate]
      apply Generate.of
      assumption)
  by_cases hc:C ⟨m, by simp⟩ = 0
  · rw [←LinearCombo.erase_val (m := m), hc] at eq
    simp at eq
    have := hS C' (by rwa [LinearCombo.cast_val])
    ext ⟨v, hv⟩
    simp at hv
    by_cases v_eq_m:v = m
    subst v
    assumption
    have : C' ⟨v, by
      apply hv.resolve_left
      assumption⟩ = 0 := by rw [this]; rfl
    show _ = 0
    unfold C' at this
    rwa [LinearCombo.apply_cast_mem (hx := ?_), LinearCombo.apply_erase_mem] at this
    simp [Set.mem_insert, Set.mem_sdiff]
    apply And.intro
    right
    apply hv.resolve_left
    assumption
    assumption
  · exfalso
    have : m = (C ⟨m, by simp⟩)⁻¹? • -C' := by
      unfold C'
      rw [map_smul, map_neg, LinearCombo.cast_val]
      have := LinearCombo.erase_val C (m := m) (by simp)
      rw [add_eq_iff_eq_sub] at this
      rw [this, neg_sub, smul_sub, ←mul_smul, inv?_mul_cancel,
        one_smul, eq, smul_zero, sub_zero]
    rw [map_smul, map_neg] at this
    apply hm
    rw [this]; clear this
    apply mem_smul
    apply mem_neg
    apply mem_span_of_linear_combo

end

end Submodule

namespace LinearCombo

variable {R M: Type*} {s: S} [SetLike S M] [RingOps R] [IsRing R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M]

def valEmb {s: Set M} [Fact (Submodule.IsLinindep R s)] : LinearCombo R s ↪ₗ[R] M := {
  LinearCombo.valHom with
  inj' := of_fact (Submodule.IsLinindep R s)
}

end LinearCombo
