import Math.Order.GaloisConnection
import Math.Data.Set.Like
import Math.Data.Set.Lattice

namespace SetLike

section

variable (S: Type*) {α: Type*} [SetLike S α]

abbrev coe_range : Set (Set α) := Set.range fun s: S => s

def LatticeBuilder.bot_le'
  (closure: Set α -> Set α)
  (closure_spec: ∀s, closure s ∈ SetLike.coe_range S)
  (create: ∀s: Set α, s ∈ SetLike.coe_range S -> S)
  (create_spec: ∀(s: Set α) (h: s ∈ SetLike.coe_range S), create s h = s)
  (gc: ∀(s: Set α) (t: S), s ≤ t ↔ closure s ≤ t)
  : ∀s: Set α, closure ∅ ≤ closure s := by
  intro s
  apply le_trans
  apply (gc _ _).mp
  apply Set.empty_sub
  exact (create (closure s) (closure_spec s))
  rw [create_spec]

end

class LatticeBuilder (S: Type*) {α: outParam <| Type*} [SetLike S α] where
  closure: Set α -> Set α
  closure_spec: ∀s, closure s ∈ SetLike.coe_range S
  create: ∀s: Set α, s ∈ SetLike.coe_range S -> S
  create_spec: ∀(s: Set α) (h: s ∈ SetLike.coe_range S), create s h = s := by intros; rfl
  gc: ∀(s: Set α) (t: S), s ≤ t ↔ closure s ≤ t
  bot : { bot: S // ∀s, bot ≤ closure s } := ⟨create (closure ∅) (closure_spec _), by
    intro s
    rw [create_spec]
    apply le_trans
    apply (gc _ _).mp
    apply Set.empty_sub
    exact (create (closure s) (closure_spec s))
    rw [create_spec]⟩

class CompleteLatticeLE (α: Type*) extends LE α, LT α, CompleteLattice α where

variable [SetLike S α] [LatticeBuilder S]

private def closure_ge: ∀s: Set α, s ≤ LatticeBuilder.closure (S := S) s := by
    intro s
    have := LatticeBuilder.gc s (LatticeBuilder.create (LatticeBuilder.closure S s) (LatticeBuilder.closure_spec s))
    rw [LatticeBuilder.create_spec] at this
    apply this.mpr
    rfl

private def closure_eq: ∀s: S, LatticeBuilder.closure S s = s := by
  intro s
  apply le_antisymm
  apply (LatticeBuilder.gc _ _).mp
  rfl
  apply closure_ge

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
  toCompleteLattice := {
    giGenerate.liftCompleteLattice with
    bot := LatticeBuilder.bot.val
    bot_le s := by
      show _ ≤ coe s
      rw [←closure_eq s]
      apply LatticeBuilder.bot.property
  }

end SetLike
