import Math.Algebra.Module.SetLike.Defs
import Math.Algebra.Module.Defs
import Math.Data.Set.Lattice
import Math.Order.GaloisConnection
import Math.Algebra.Semiring.Defs

namespace SubModule

section

variable [Add M] [Zero M] [SMul R M]

instance : LE (SubModule R M) where
  le := (· ⊆ ·)
instance : LT (SubModule R M) := IsLawfulLT.instLT _
instance : IsLawfulLT (SubModule R M) := IsLawfulLT.inst _

def oemb : SubModule R M ↪o Set M where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := Iff.rfl

instance : IsPartialOrder (SubModule R M) := oemb.inducedIsPartialOrder'

inductive Generate (U: Set M) : M -> Prop where
| of (x: M) : x ∈ U -> Generate U x
| zero : Generate U 0
| add : Generate U a -> Generate U b -> Generate U (a + b)
| smul (r: R) {a: M} : Generate U a -> Generate U (r • a)

def generate (U: Set M) : SubModule R M where
  carrier := Set.mk (Generate U)
  mem_zero' := Generate.zero
  mem_add' := Generate.add
  mem_smul' := Generate.smul

def giGenerate : @GaloisInsertion (Set M) (SubModule R M) _ _ generate (fun a => a.carrier) where
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
    mem_smul' := by
      intro r m hm
      apply hS
      apply Generate.smul
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
    | smul => apply mem_smul <;> assumption
    | add => apply mem_add <;> assumption
  le_l_u := by
    intro s x hx
    apply Generate.of
    assumption

end

instance [SemiringOps R] [AddMonoidOps M]
  [IsSemiring R] [IsAddMonoid M] [IsAddCommMagma M]
  [SMul R M] [IsModule R M] : CompleteLattice (SubModule R M) := {
  giGenerate.liftCompleteLattice with
  bot := {
    carrier := {0}
    mem_add' := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
    mem_smul' := by
      rintro r m rfl
      rw [smul_zero]; rfl
    mem_zero' := rfl
  }
  bot_le _ := by
    rintro x rfl
    apply mem_zero
}

end SubModule
