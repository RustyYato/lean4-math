import Math.Algebra.Monoid.SetLike.Defs
import Math.Data.Set.Lattice
import Math.Algebra.Semigroup.SetLike.Defs
import Math.Order.GaloisConnection
import Math.Algebra.Monoid.Defs

namespace SubMonoid

variable [Mul α] [One α]

instance : LE (SubMonoid α) where
  le := (· ⊆ ·)
instance : LT (SubMonoid α) := IsLawfulLT.instLT _
instance : IsLawfulLT (SubMonoid α) := IsLawfulLT.inst _

def oemb : SubMonoid α ↪o Set α where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (SubMonoid α) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| one : Generate U 1

def generate (U: Set α) : SubMonoid α where
  carrier := Set.mk (Generate U)
  mem_mul' := Generate.mul
  mem_one' := Generate.one

def giGenerate : @GaloisInsertion (Set α) (SubMonoid α) _ _ generate (fun a => a.carrier) where
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

instance [IsMulOneClass α] : CompleteLattice (SubMonoid α) := {
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

end SubMonoid

namespace SubAddMonoid

variable [Add α] [Zero α]

instance : LE (SubAddMonoid α) where
  le := (· ⊆ ·)
instance : LT (SubAddMonoid α) := IsLawfulLT.instLT _
instance : IsLawfulLT (SubAddMonoid α) := IsLawfulLT.inst _

def oemb : SubAddMonoid α ↪o Set α where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (SubAddMonoid α) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| zero : Generate U 0

def generate (U: Set α) : SubAddMonoid α where
  carrier := Set.mk (Generate U)
  mem_add' := Generate.add
  mem_zero' := Generate.zero

def giGenerate : @GaloisInsertion (Set α) (SubAddMonoid α) _ _ generate (fun a => a.carrier) where
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

instance [IsAddZeroClass α] : CompleteLattice (SubAddMonoid α) := {
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

end SubAddMonoid
