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

section BasisDef

variable (R M: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
  [DecidableEq M]

class IsBasis (S: Type*) [SetLike S M] : Prop where
  indep (U: S): IsLinindep R (U: Set M)
  complete (U: S): ∀m, m ∈ span R (U: Set M)

instance [SetLike S M] [b: IsBasis R M S] (U: S) : Fact (IsLinindep R (U: Set M)) where
  proof := b.indep _

structure Basis where
  -- the set of basis vectors
  carrier: Set M
  -- require that a set of basis vectors
  -- must be able to fully and faithfully represent any vector in the module
  protected decode: M -> LinearCombo R carrier
  -- by enforcing that decode is the left and right inverse of the canonical
  -- mapping of formal linear combinations of vectors to vectors
  -- we can show that the decoding is unique, and that it represents
  -- an equivalence between formal linear combinations and vectors
  coe_decode: Function.IsLeftInverse decode (fun m => m)
  decode_coe: Function.IsRightInverse decode (fun m => m)

instance : SetLike (Basis R M) M where
  coe b := b.carrier
  coe_inj := by
    intro a b
    simp
    intro h
    suffices HEq a.decode b.decode by
      cases a; cases b;
      congr
      simp at this
      apply proof_irrel_heq
      apply proof_irrel_heq
    obtain ⟨a, deca, a₀, a₁⟩ := a
    obtain ⟨b, decb, b₀, b₁⟩ := b
    cases h
    simp
    apply Function.eq_of_inverses <;> assumption

end BasisDef

namespace Basis

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
  [DecidableEq M]

@[ext]
def ext (a b: Basis R M) : (∀{x}, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

def toEquiv (b: Basis R M) : M ≃ₗ[R] LinearCombo R (b: Set M) :=
  LinearEquiv.symm {
    LinearCombo.valHom with
    invFun := b.decode
    leftInv := b.coe_decode
    rightInv := b.decode_coe
  }

def coords (b: Basis R M) : M →ₗ[R] LinearCombo R (b: Set M) :=
  b.toEquiv.toLinearMap

def apply_toEquiv {b: Basis R M} : b.toEquiv.toLinearMap = b.coords := rfl
def symm_apply_toEquiv {b: Basis R M} : b.toEquiv.symm.toLinearMap = LinearCombo.valHom := rfl

def apply_coords_valHom (b: Basis R M) (x: LinearCombo R (b: Set M)) : b.coords x = x := by
  apply b.coe_decode

def apply_valHom_coords (b: Basis R M) (x: M) : LinearCombo.valHom (b.coords x) = x := by
  apply b.decode_coe

def coords_comp_valHom (b: Basis R M) : b.coords.comp LinearCombo.valHom = .id _ := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.apply_comp]
  apply b.apply_coords_valHom

def valHom_comp_coords (b: Basis R M) : LinearCombo.valHom.comp b.coords = .id _ := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.apply_comp]
  apply b.apply_valHom_coords

noncomputable def ofSet (s: Set M) (h: IsLinindep R s) (g: ∀m: M, m ∈ span R s) : Basis R M where
  carrier := s
  decode m := Classical.choose (g m)
  coe_decode x := by apply h; symm; exact Classical.choose_spec (g x)
  decode_coe x := by symm; exact Classical.choose_spec (g x)

instance : IsBasis R M (Basis R M) where
  indep b := by
    intro x y h
    simp at h
    apply b.toEquiv.symm.inj
    assumption
  complete b v := by
    rw [←b.decode_coe v]
    simp
    apply mem_span_of_linear_combo

end Basis

section IsBasis

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
  [DecidableEq M]


def is_linear_indep (U: Set M) [Fact (IsLinindep R U)] : IsLinindep R U := of_fact _
def is_complete [SetLike S M] [b: IsBasis R M S] (U: S) : ∀m, m ∈ span R (U: Set M) := b.complete _

end IsBasis

section LinindepRing

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

end LinindepRing

section LinindepField

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

end LinindepField

end Submodule

namespace LinearCombo

variable {R M: Type*} {s: S} [SetLike S M] [RingOps R] [IsRing R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M]

def valEmb {s: Set M} [Fact (Submodule.IsLinindep R s)] : LinearCombo R s ↪ₗ[R] M := {
  LinearCombo.valHom with
  inj' := of_fact (Submodule.IsLinindep R s)
}

end LinearCombo
