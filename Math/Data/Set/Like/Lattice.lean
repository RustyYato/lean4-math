import Math.Order.GaloisConnection
import Math.Data.Set.Like
import Math.Data.Set.Lattice

namespace SetLike

variable (S: Type*) {α: Type*} [SetLike S α]

abbrev coe_range : Set (Set α) := Set.range fun s: S => s

class LatticeBuilder where
  closure: Set α -> Set α
  closure_spec: ∀s, closure s ∈ SetLike.coe_range S
  create: ∀s: Set α, s ∈ SetLike.coe_range S -> S
  create_spec: ∀(s: Set α) (h: s ∈ SetLike.coe_range S), create s h = s
  gc: ∀(s: Set α) (t: S), s ≤ t ↔ closure s ≤ t

class CompleteLatticeLE (α: Type*) extends LE α, LT α, CompleteLattice α where

variable [LatticeBuilder S]

private def closure_ge: ∀s: Set α, s ≤ LatticeBuilder.closure (S := S) s := by
    intro s
    have := LatticeBuilder.gc s (LatticeBuilder.create (LatticeBuilder.closure S s) (LatticeBuilder.closure_spec s))
    rw [LatticeBuilder.create_spec] at this
    apply this.mpr
    rfl

local instance instLE : LE S where
  le a b := SetLike.coe a ≤ SetLike.coe b
local instance instLT : LT S where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder S where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl _ := Set.sub_refl _
  le_trans := Set.sub_trans
  le_antisymm := by
    intro a b ab ba
    apply SetLike.coe_inj
    apply le_antisymm
    assumption
    assumption

def giGenerate : @GaloisInsertion (Set α) S _ _ (fun s => LatticeBuilder.create (LatticeBuilder.closure S s) (LatticeBuilder.closure_spec s)) (fun s => s) where
  choice s h := LatticeBuilder.create s (by
    rw [LatticeBuilder.create_spec] at h
    suffices s = LatticeBuilder.closure S s by
      rw [this]
      apply LatticeBuilder.closure_spec
    apply le_antisymm _ h
    apply closure_ge)
  choice_eq := by
    intro a h
    dsimp
    apply SetLike.coe_inj
    rw [LatticeBuilder.create_spec, LatticeBuilder.create_spec]
    rw [LatticeBuilder.create_spec] at h
    apply le_antisymm _ h
    apply closure_ge
  gc := by
    intro a b
    dsimp
    apply Iff.intro
    intro h
    rw [LE.le, instLE] at h
    dsimp at h
    apply le_trans _ h
    rw [LatticeBuilder.create_spec]
    apply closure_ge
    intro h
    rw [LE.le, instLE]
    dsimp
    rw [LatticeBuilder.create_spec]
    apply (LatticeBuilder.gc _ _).mp
    assumption
  le_l_u := by
    intro x
    rw [LE.le, instLE]
    dsimp
    rw [LatticeBuilder.create_spec]
    apply closure_ge

def toCompleteLattice : CompleteLatticeLE S where
toCompleteLattice := (giGenerate S).liftCompleteLattice

end SetLike
