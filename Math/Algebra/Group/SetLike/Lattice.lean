import Math.Algebra.Group.SetLike.Defs
import Math.Data.Set.Lattice
import Math.Algebra.Semigroup.SetLike.Defs
import Math.Order.GaloisConnection
import Math.Algebra.Group.Defs

namespace SubGroup

variable [Mul α] [One α] [Inv α]

instance : LE (SubGroup α) where
  le := (· ⊆ ·)
instance : LT (SubGroup α) := IsLawfulLT.instLT _
instance : IsLawfulLT (SubGroup α) := IsLawfulLT.inst _

def oemb : SubGroup α ↪o Set α where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (SubGroup α) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| inv {a: α} : Generate U a -> Generate U (a⁻¹)
| one : Generate U 1

def generate (U: Set α) : SubGroup α where
  carrier := Set.mk (Generate U)
  mem_mul' := Generate.mul
  mem_one' := Generate.one
  mem_inv' := Generate.inv

def giGenerate : @GaloisInsertion (Set α) (SubGroup α) _ _ generate (fun a => a.carrier) where
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
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance [IsMulOneClass α] [IsInvOneClass α] : CompleteLattice (SubGroup α) := {
  giGenerate.liftCompleteLattice with
  bot := {
    carrier := {1}
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

end SubGroup

namespace SubAddGroup

variable [Add α] [Zero α] [Neg α]

instance : LE (SubAddGroup α) where
  le := (· ⊆ ·)
instance : LT (SubAddGroup α) := IsLawfulLT.instLT _
instance : IsLawfulLT (SubAddGroup α) := IsLawfulLT.inst _

def oemb : SubAddGroup α ↪o Set α where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (SubAddGroup α) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| neg {a: α} : Generate U a -> Generate U (-a)
| zero : Generate U 0

def generate (U: Set α) : SubAddGroup α where
  carrier := Set.mk (Generate U)
  mem_add' := Generate.add
  mem_zero' := Generate.zero
  mem_neg' := Generate.neg

def giGenerate : @GaloisInsertion (Set α) (SubAddGroup α) _ _ generate (fun a => a.carrier) where
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
    | neg => apply mem_neg <;> assumption
    | add => apply mem_add <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance [IsAddZeroClass α] [IsNegZeroClass α] : CompleteLattice (SubAddGroup α) := {
  giGenerate.liftCompleteLattice with
  bot := {
    carrier := {0}
    mem_add' := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
    mem_neg' := by
      rintro _ rfl
      rw [neg_zero]; rfl
    mem_zero' := rfl
  }
  bot_le _ := by
    rintro x rfl
    apply mem_zero
}

end SubAddGroup
