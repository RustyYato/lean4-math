import Math.Algebra.Group.Theory.NormalSubgroup.Basic
import Math.Algebra.Group.SetLike.Defs
import Math.Data.Set.Lattice
import Math.Algebra.Semigroup.SetLike.Defs
import Math.Order.GaloisConnection
import Math.Algebra.Group.Defs

namespace NormalSubgroup

variable [GroupOps α] [IsGroup α]

instance : LE (NormalSubgroup α) where
  le := (· ⊆ ·)
instance : LT (NormalSubgroup α) := IsLawfulLT.instLT _
instance : IsLawfulLT (NormalSubgroup α) := IsLawfulLT.inst _

def oemb : NormalSubgroup α ↪o Set α where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (NormalSubgroup α) := oemb.inducedIsPartialOrder'

def giGenerate : @GaloisInsertion (Set α) (NormalSubgroup α) _ _ generate (fun a => a.carrier) where
  choice S hS := {
    carrier := S
    mem_mul' := by
      intro a b ha hb
      apply hS
      apply Generate.mul
      apply Generate.of
      assumption
      apply Generate.of
      assumption
    mem_inv' := by
      intro a ha
      apply hS
      apply Generate.inv
      apply Generate.of
      assumption
    mem_one' := by
      apply hS
      apply Generate.one
    mem_conj' := by
      intro x a ha
      apply hS
      apply Generate.conj
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
    apply Iff.intro
    intro h x hx
    apply h
    apply Generate.of
    assumption
    intro h x hx
    induction hx with
    | of => apply h; assumption
    | one => apply mem_one
    | inv => apply mem_inv <;> assumption
    | mul => apply mem_mul <;> assumption
    | conj => apply mem_conj <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance : CompleteLattice (NormalSubgroup α) := {
  giGenerate.liftCompleteLattice with
  bot := {
    carrier := {1}
    mem_conj' := by
      rintro x a rfl
      dsimp at *
      rw [resp_one]; rfl
    mem_mul' := by
      rintro _ _ rfl rfl
      rw [mul_one]; rfl
    mem_inv' := by
      rintro _ rfl
      rw [inv_one]; rfl
    mem_one' := rfl
  }
  bot_le _ := by
    rintro x rfl
    apply mem_one
}

end NormalSubgroup
