import Math.Data.Set.Like.Lattice
import Math.Algebra.Ring.Theory.Ideal.Defs
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Algebra
import Math.Algebra.Ring.Defs
import Math.Order.Atom.Basic

namespace Ideal

variable (R: Type*) [RingOps R] [IsRing R]

private instance builder : SetLike.LatticeBuilder (Ideal R) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_add := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_add s <;> assumption
    mem_neg := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_neg s <;> assumption
    mem_zero := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_zero s
    mem_mul_left := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_mul_left s <;> assumption
    mem_mul_right := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_mul_right s <;> assumption
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
    | neg => apply mem_neg t <;> assumption
    | add => apply mem_add t <;> assumption
    | mul_left => apply mem_mul_left t <;> assumption
    | mul_right => apply mem_mul_right t <;> assumption
  bot := ⟨Ideal.zero _, by rintro _ _ rfl; apply Generate.zero⟩

instance : LE (Ideal R) := (SetLike.toCompleteLattice (S := Ideal R)).toLE
instance : LT (Ideal R) := (SetLike.toCompleteLattice (S := Ideal R)).toLT
instance : IsPartialOrder (Ideal R) := (SetLike.toCompleteLattice (S := Ideal R)).toIsPartialOrder

private local instance : SetLike.CompleteLatticeLE (Ideal R) := {
  SetLike.toCompleteLattice with
  max a b := a + b
  le_sup_left := by
    intro a b x hx
    refine ⟨(x, 0), ?_, ?_, ?_⟩
    assumption
    apply mem_zero
    apply add_zero
  le_sup_right := by
    intro a b x hx
    refine ⟨(0, x), ?_, ?_, ?_⟩
    apply mem_zero
    assumption
    apply zero_add
  sup_le := by
    rintro a b k ak bk _ ⟨⟨x, y⟩, _, _, rfl⟩
    apply mem_add k
    apply ak; assumption
    apply bk; assumption
}

instance : Top (Ideal R) := inferInstance
instance : Bot (Ideal R) := inferInstance
instance : Max (Ideal R) := inferInstance
instance : Min (Ideal R) := inferInstance
instance : SupSet (Ideal R) := inferInstance
instance : InfSet (Ideal R) := inferInstance
instance : IsCompleteLattice (Ideal R) := inferInstance

def isMaximal (i: Ideal R): Prop := IsCoatom i

def generate_spec (U: Set R) : generate U = sInf (Set.mk fun i: Ideal R => U ⊆ i) := by
  refine Eq.symm (Set.IsLeast.csInf_eq ?_)
  refine ⟨?_, ?_⟩
  apply Generate.of
  rintro i h _ hx
  simp
  apply of_mem_generate _ _ _ _ hx
  apply h

end Ideal
