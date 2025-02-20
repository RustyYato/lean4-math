import Math.Algebra.Ring.SetLike.Defs
import Math.Algebra.AddGroupWithOne.SetLike.Basic
import Math.Data.Set.Lattice
import Math.Algebra.Semigroup.SetLike.Defs
import Math.Order.GaloisConnection
import Math.Algebra.Ring.Defs

namespace SubRing

variable [Add α] [Mul α] [Neg α] [Zero α] [One α]

instance : LE (SubRing α) where
  le := (· ⊆ ·)
instance : LT (SubRing α) := IsLawfulLT.instLT _
instance : IsLawfulLT (SubRing α) := IsLawfulLT.inst _

def oemb : SubRing α ↪o Set α where
  toFun a := a
  inj := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (SubRing α) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| neg {a: α} : Generate U a -> Generate U (-a)
| zero : Generate U 0
| one : Generate U 1

def generate (U: Set α) : SubRing α where
  carrier := Set.mk (Generate U)
  mem_add' := Generate.add
  mem_mul' := Generate.mul
  mem_neg' := Generate.neg
  mem_zero' := Generate.zero
  mem_one' := Generate.one

def giGenerate : @GaloisInsertion (Set α) (SubRing α) _ _ generate (fun a => a.carrier) where
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
    mem_mul' := by
      intro a b ha hb
      apply hS
      apply Generate.mul
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
    | one => apply mem_one
    | zero => apply mem_zero
    | neg => apply mem_neg <;> assumption
    | mul => apply mem_mul <;> assumption
    | add => apply mem_add <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

instance : CompleteLattice (SubRing α) := giGenerate.liftCompleteLattice

end SubRing

namespace SubRing

variable [RingOps α] [IsRing α]

def range_intCast : SubRing α where
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
  mem_mul' := by
    rintro _ _ ⟨a, _, rfl⟩ ⟨b, _, rfl⟩
    simp
    rw [←intCast_mul]
    apply Set.mem_range'

def bot_eq_range_intCast: ⊥ = range_intCast (α := α) := by
  apply le_antisymm
  apply bot_le
  rintro _ ⟨n, rfl⟩
  apply mem_intCast

end SubRing
