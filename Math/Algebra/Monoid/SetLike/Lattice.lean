import Math.Algebra.Monoid.SetLike.Defs
import Math.Data.Set.Lattice
import Math.Algebra.Semigroup.SetLike.Defs
import Math.Order.GaloisConnection
import Math.Algebra.Monoid.Defs

namespace Submonoid

variable [Mul α] [One α]

instance : LE (Submonoid α) where
  le := (· ⊆ ·)
instance : LT (Submonoid α) := IsLawfulLT.instLT _
instance : IsLawfulLT (Submonoid α) := IsLawfulLT.inst _

def oemb : Submonoid α ↪o Set α where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (Submonoid α) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| one : Generate U 1

def generate (U: Set α) : Submonoid α where
  carrier := Set.mk (Generate U)
  mem_mul' := Generate.mul
  mem_one' := Generate.one

def giGenerate : @GaloisInsertion (Set α) (Submonoid α) _ _ generate (fun a => a.carrier) where
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
    mem_one' := by
      apply hS
      apply Generate.one
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
    | mul => apply mem_mul <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance [IsMulOneClass α] : CompleteLattice (Submonoid α) := {
  giGenerate.liftCompleteLattice with
  bot := {
    carrier := {1}
    mem_mul' := by
      rintro _ _ rfl rfl
      rw [mul_one]; rfl
    mem_one' := rfl
  }
  bot_le _ := by
    rintro x rfl
    apply mem_one
}

end Submonoid

namespace AddSubmonoid

variable [Add α] [Zero α]

instance : LE (AddSubmonoid α) where
  le := (· ⊆ ·)
instance : LT (AddSubmonoid α) := IsLawfulLT.instLT _
instance : IsLawfulLT (AddSubmonoid α) := IsLawfulLT.inst _

def oemb : AddSubmonoid α ↪o Set α where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (AddSubmonoid α) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| zero : Generate U 0

def generate (U: Set α) : AddSubmonoid α where
  carrier := Set.mk (Generate U)
  mem_add' := Generate.add
  mem_zero' := Generate.zero

def giGenerate : @GaloisInsertion (Set α) (AddSubmonoid α) _ _ generate (fun a => a.carrier) where
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
    mem_zero' := by
      apply hS
      apply Generate.zero
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
    | zero => apply mem_zero
    | add => apply mem_add <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance [IsAddZeroClass α] : CompleteLattice (AddSubmonoid α) := {
  giGenerate.liftCompleteLattice with
  bot := {
    carrier := {0}
    mem_add' := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
    mem_zero' := rfl
  }
  bot_le _ := by
    rintro x rfl
    apply mem_zero
}

end AddSubmonoid
