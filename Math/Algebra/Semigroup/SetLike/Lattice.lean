import Math.Data.Set.Lattice
import Math.Algebra.Semigroup.SetLike.Defs
import Math.Order.GaloisConnection

namespace SubSemigroup

instance [Mul α] : LE (SubSemigroup α) where
  le := (· ⊆ ·)
instance [Mul α] : LT (SubSemigroup α) := IsLawfulLT.instLT _
instance [Mul α] : IsLawfulLT (SubSemigroup α) := IsLawfulLT.inst _

def oemb [Mul α] : SubSemigroup α ↪o Set α where
  toFun a := a
  inj := SetLike.coe_inj
  resp_rel := Iff.rfl

instance [Mul α] : IsPartialOrder (SubSemigroup α) := oemb.inducedIsPartialOrder'

inductive Generate [Mul α] (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)

def generate [Mul α] (U: Set α) : SubSemigroup α where
  carrier := Set.mk (Generate U)
  mem_mul' := Generate.mul

def giGenerate [Mul α] : @GaloisInsertion (Set α) (SubSemigroup α) _ _ generate SubSemigroup.carrier where
  choice S hS := {
    carrier := S
    mem_mul' := by
      intro a b ha hb
      apply hS
      show a * b ∈ generate S
      apply mem_mul
      apply Generate.of
      assumption
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
    | mul => apply mem_mul <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance [Mul α] : CompleteLattice (SubSemigroup α) := {
  giGenerate.liftCompleteLattice with
  bot := {
    carrier := ∅
    mem_mul' h := h.elim
  }
  bot_le _ := Set.empty_sub _
}

end SubSemigroup

namespace SubAddSemigroup

instance [Add α] : LE (SubAddSemigroup α) where
  le := (· ⊆ ·)
instance [Add α] : LT (SubAddSemigroup α) := IsLawfulLT.instLT _
instance [Add α] : IsLawfulLT (SubAddSemigroup α) := IsLawfulLT.inst _

def oemb [Add α] : SubAddSemigroup α ↪o Set α where
  toFun a := a
  inj := SetLike.coe_inj
  resp_rel := Iff.rfl

instance [Add α] : IsPartialOrder (SubAddSemigroup α) := oemb.inducedIsPartialOrder'

inductive Generate [Add α] (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)

def generate [Add α] (U: Set α) : SubAddSemigroup α where
  carrier := Set.mk (Generate U)
  mem_add' := Generate.add

def giGenerate [Add α] : @GaloisInsertion (Set α) (SubAddSemigroup α) _ _ generate SubAddSemigroup.carrier where
  choice S hS := {
    carrier := S
    mem_add' := by
      intro a b ha hb
      apply hS
      show a + b ∈ generate S
      apply mem_add
      apply Generate.of
      assumption
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
    | add => apply mem_add <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance [Add α] : CompleteLattice (SubAddSemigroup α) := {
  giGenerate.liftCompleteLattice with
  bot := {
    carrier := ∅
    mem_add' h := h.elim
  }
  bot_le _ := Set.empty_sub _
}

end SubAddSemigroup
