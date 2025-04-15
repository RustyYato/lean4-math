import Math.Algebra.CliffordAlgebra.Defs
import Math.Algebra.Monoid.Units.Defs
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Quotient

namespace CliffordAlgebra

variable [RingOps R] [IsRing R] [IsCommMagma R] [AddGroupOps V]
  [IsAddGroup V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

def ideal : Ideal (TensorAlgebra R V) := Ideal.generate (Set.mk <| fun x => ∃v: V, x = .ι R v * .ι R v - algebraMap (Q v))

def ideal_eq_kernel : ideal Q = Ideal.kernel (ofTensorAlgebra Q).toRingHom := by
  ext x
  apply Iff.intro
  · intro h
    apply Ideal.of_mem_generate _ _ _ _ h
    clear h x; rintro _ ⟨v, rfl, hv⟩
    show ofTensorAlgebra Q (.ι R v * .ι R v - algebraMap (Q v)) = 0
    symm; rw [map_sub, ←add_eq_iff_eq_sub, zero_add]; symm
    apply RingQuot.mk_rel
    apply CliffordAlgebra.Rel.intro
  · intro h
    obtain h : ofTensorAlgebra Q x = 0 := h
    rw [←map_zero (ofTensorAlgebra Q)] at h
    replace h := RingQuot.of_mk_rel h
    apply (Ideal.equivCon_mem_iff _).mpr
    apply RingCon.ofGenerate _ _ _ _ _ h
    clear h x
    intro x y h
    apply (Ideal.equivCon_rel_iff _).mpr
    rw [Equiv.coe_symm]
    cases h with | intro v =>
    apply Ideal.Generate.of
    exists v

end CliffordAlgebra

namespace CliffordAlgebra

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

inductive IsVersor : CliffordAlgebra Q -> Prop where
| scalar (x: R) : IsUnit x -> IsVersor (algebraMap x)
| mul_vec (x: CliffordAlgebra Q) (v: V) : IsVersor x -> IsUnit (ι Q v) -> IsVersor (x * ι Q v)

-- every versor is invertible
def IsVersor.toIsUnit (x: CliffordAlgebra Q) (h: x.IsVersor) : IsUnit x := by
  induction h with
  | scalar x hx =>
    obtain ⟨⟨x, inv, xinv, invx⟩ , rfl⟩ := hx
    refine ⟨⟨_, algebraMap inv, ?_, ?_⟩, rfl⟩
    rw [←map_mul, xinv, map_one]
    rw [←map_mul, invx, map_one]
  | mul_vec x v _ hv hx =>
    obtain ⟨⟨x, x', xinv, invx⟩ , rfl⟩ := hx
    obtain ⟨⟨v, v', vinv, invv⟩ , rfl⟩ := hv
    refine ⟨⟨_, v' * x', ?_, ?_⟩, rfl⟩
    simp
    rw [mul_assoc, ←mul_assoc _ v', vinv, one_mul, xinv]
    rw [mul_assoc, ←mul_assoc x', invx, one_mul, invv]

end CliffordAlgebra
