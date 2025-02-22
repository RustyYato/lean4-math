import Math.Algebra.AddMonoidWithOne.SetLike.Basic
import Math.Data.Set.Lattice
import Math.Algebra.Semigroup.SetLike.Defs
import Math.Order.GaloisConnection

namespace SubAddMonoidWithOne

variable [Add α] [Zero α] [One α]

instance : LE (SubAddMonoidWithOne α) where
  le := (· ⊆ ·)
instance : LT (SubAddMonoidWithOne α) := IsLawfulLT.instLT _
instance : IsLawfulLT (SubAddMonoidWithOne α) := IsLawfulLT.inst _

def oemb : SubAddMonoidWithOne α ↪o Set α where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (SubAddMonoidWithOne α) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| zero : Generate U 0
| one : Generate U 1

def generate (U: Set α) : SubAddMonoidWithOne α where
  carrier := Set.mk (Generate U)
  mem_add' := Generate.add
  mem_zero' := Generate.zero
  mem_one' := Generate.one

def giGenerate : @GaloisInsertion (Set α) (SubAddMonoidWithOne α) _ _ generate (fun a => a.carrier) where
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
    | zero => apply mem_zero
    | one => apply mem_one
    | add => apply mem_add <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance: CompleteLattice (SubAddMonoidWithOne α) :=
  giGenerate.liftCompleteLattice

end SubAddMonoidWithOne

namespace SubAddMonoidWithOne

variable [AddMonoidWithOneOps α] [IsAddMonoidWithOne α]

def range_natCast : SubAddMonoidWithOne α where
  carrier := Set.range (fun n: ℕ => (n: α))
  mem_zero' := by exists 0; symm; apply natCast_zero
  mem_one' := by exists 1; symm; apply natCast_one
  mem_add' := by
    rintro _ _ ⟨a, _, rfl⟩ ⟨b, _, rfl⟩
    simp
    rw [←natCast_add]
    apply Set.mem_range'

def bot_eq_range_natCast: ⊥ = range_natCast (α := α) := by
  apply le_antisymm
  apply bot_le
  rintro _ ⟨n, rfl⟩
  apply mem_natCast

end SubAddMonoidWithOne
