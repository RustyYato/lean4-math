import Math.Algebra.AddGroupWithOne.SetLike.Basic
import Math.Algebra.AddMonoidWithOne.SetLike.Lattice

namespace SubAddGroupWithOne

variable [Add α] [Neg α] [Zero α] [One α]

instance : LE (SubAddGroupWithOne α) where
  le := (· ⊆ ·)
instance : LT (SubAddGroupWithOne α) := IsLawfulLT.instLT _
instance : IsLawfulLT (SubAddGroupWithOne α) := IsLawfulLT.inst _

def oemb : SubAddGroupWithOne α ↪o Set α where
  toFun a := a
  inj := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (SubAddGroupWithOne α) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| neg {a: α} : Generate U a -> Generate U (-a)
| zero : Generate U 0
| one : Generate U 1

def generate (U: Set α) : SubAddGroupWithOne α where
  carrier := Set.mk (Generate U)
  mem_add' := Generate.add
  mem_neg' := Generate.neg
  mem_zero' := Generate.zero
  mem_one' := Generate.one

def giGenerate : @GaloisInsertion (Set α) (SubAddGroupWithOne α) _ _ generate (fun a => a.carrier) where
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
    | neg => apply mem_neg <;> assumption
    | add => apply mem_add <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance: CompleteLattice (SubAddGroupWithOne α) :=
  giGenerate.liftCompleteLattice

end SubAddGroupWithOne

namespace SubAddGroupWithOne

variable [AddGroupWithOneOps α] [IsAddGroupWithOne α]

def range_intCast : SubAddGroupWithOne α where
  carrier := Set.range (fun n: ℤ => (n: α))
  mem_zero' := by exists 0; symm; apply intCast_zero
  mem_one' := by exists 1; symm; apply intCast_one
  mem_neg' := by
    rintro _ ⟨a, _, rfl⟩
    simp
    rw [←intCast_neg]
    apply Set.mem_range'
  mem_add' := by
    rintro _ _ ⟨a, _, rfl⟩ ⟨b, _, rfl⟩
    simp
    rw [←intCast_add]
    apply Set.mem_range'

def bot_eq_range_intCast: ⊥ = range_intCast (α := α) := by
  apply le_antisymm
  apply bot_le
  rintro _ ⟨n, rfl⟩
  apply mem_intCast

end SubAddGroupWithOne
