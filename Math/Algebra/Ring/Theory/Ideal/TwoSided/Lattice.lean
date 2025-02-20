import Math.Algebra.Ring.Theory.Ideal.Defs
import Math.Algebra.Ring.SetLike.Defs
import Math.Data.Set.Lattice
import Math.Algebra.Ring.SetLike.Basic
import Math.Order.GaloisConnection
import Math.Algebra.Ring.Defs

namespace Ideal

variable (R: Type*) [RingOps R] [IsRing R]

instance : LE (Ideal R) where
  le a b := a.carrier ⊆ b.carrier

instance : LT (Ideal R) where
  lt a b := a ≤ b ∧ ¬b ≤ a

inductive Generate (U: Set R) : R -> Prop where
| of (x: R) : x ∈ U -> Generate U x
| zero : Generate U 0
| add (a b: R) : Generate U a -> Generate U b -> Generate U (a + b)
| neg (a: R) : Generate U a -> Generate U (-a)
| mul_left (r: R) (x: R) : Generate U x -> Generate U (r * x)
| mul_right (r: R) (x: R) : Generate U x -> Generate U (x * r)

def toIdeal (U: Set R) : Ideal R where
  carrier := Set.mk (Ideal.Generate R U)
  mem_zero' := Ideal.Generate.zero
  mem_add' := Ideal.Generate.add _ _
  mem_neg' := Ideal.Generate.neg _
  mem_mul_left' _ _ := Ideal.Generate.mul_left _ _
  mem_mul_right' _ _ := Ideal.Generate.mul_right _ _

def oemb : Ideal R ↪o Set R where
  toFun a := a.carrier
  resp_rel := Iff.rfl
  inj := SetLike.coe_inj

instance : IsLawfulLT (Ideal R) := ⟨Iff.rfl⟩

instance : IsPartialOrder (Ideal R) :=
  (Ideal.oemb R).inducedIsPartialOrder'

def giGenerate : @GaloisInsertion (Set R) (Ideal R) _ _ (toIdeal R) (fun x => x.carrier) where
  choice S hS := {
    carrier := S
    mem_add' := by
      intro a b ha hb
      apply hS
      apply Generate.add
      apply Generate.of
      assumption
      apply Generate.of
      assumption
    mem_neg' := by
      intro a ha
      apply hS
      apply Generate.neg
      apply Generate.of
      assumption
    mem_zero' := by
      apply hS
      apply Generate.zero
    mem_mul_left' := by
      intro _ _ ha
      apply hS
      apply Generate.mul_left
      apply Generate.of
      assumption
    mem_mul_right' := by
      intro _ _ ha
      apply hS
      apply Generate.mul_right
      apply Generate.of
      assumption
  }
  choice_eq := by
    intro S h
    simp
    apply le_antisymm
    apply Generate.of
    apply h
  gc := by
    intro a b
    dsimp
    apply Iff.intro
    · intro h x x_in_a
      exact h x (Ideal.Generate.of _ x_in_a)
    · intro h x hx
      show x ∈ b
      induction hx with
      | of =>
        apply h
        assumption
      | zero => apply mem_zero
      | add => apply mem_add <;> assumption
      | neg => apply mem_neg <;> assumption
      | mul_left => apply mem_mul_left <;> assumption
      | mul_right => apply mem_mul_right <;> assumption
  le_l_u := by
    intro x r hx
    apply Ideal.Generate.of
    assumption

instance : CompleteLattice (Ideal R) := {
  (Ideal.giGenerate R).liftCompleteLattice with
  bot := Ideal.zero R
  bot_le := by
    rintro x h rfl
    apply mem_zero x
}

end Ideal
