import Math.Order.Filter.Directed
import Math.Order.Atom.Zorn

instance : IsAtomic (Filter α) := by
    apply IsAtomic.of_isChain_bounded
    intro S Schain Sne bot_not_mem
    refine ⟨_, ?_, (isGLB_sInf S).left⟩
    intro h
    have : S.IsChain (· ≥ ·) := Schain.opp
    have := FilterBase.sInf_neBot_of_directed' Sne this.directedOn bot_not_mem
    exact this.ne h

instance : IsAtomic (Filter α) := inferInstance

structure UltraFilterBase (α: Type*) [LE α] [LT α] [Min α] [Bot α] [IsSemiLatticeMin α] [IsAtomic (FilterBase α)] extends FilterBase α where
  protected neBot: toFilterBase.NeBot
  protected le_of_le : ∀g: FilterBase α, FilterBase.NeBot g → g ≤ toFilter → toFilter ≤ g

abbrev UltraFilter (α: Type*) := UltraFilterBase (Set α)

namespace UltraFilterBase

attribute [coe] UltraFilterBase.toFilterBase

variable [LE α] [LT α] [Min α] [Bot α] [IsSemiLatticeMin α] [IsAtomic (FilterBase α)]

instance : CoeTC (UltraFilterBase α) (FilterBase α) :=
  ⟨UltraFilterBase.toFilterBase⟩

instance : Membership α (UltraFilterBase α) := ⟨fun f s => s ∈ (f : FilterBase α)⟩

instance (f: UltraFilterBase α) : f.toFilterBase.NeBot := f.neBot

def unique (f : UltraFilterBase α) {g : FilterBase α} (h : g ≤ f) (hne : g.NeBot := by infer_instance) :
    g = f := le_antisymm h <| f.le_of_le g hne h

protected theorem isAtom (f : UltraFilterBase α) : IsAtom (f : FilterBase α) := by
  apply And.intro f.neBot.ne
  intro b hb
  apply Classical.byContradiction
  intro ne_bot
  cases f.unique (le_of_lt hb) ⟨ne_bot⟩
  exact lt_irrefl hb

@[simp]
theorem mem_coe (s: α) (f: UltraFilterBase α) : s ∈ (f : FilterBase α) ↔ s ∈ f :=
  Iff.rfl

theorem coe_injective : Function.Injective (UltraFilterBase.toFilterBase (α := α))
  | ⟨f, h₁, h₂⟩, ⟨g, _, _⟩, _ => by congr

def eq_of_le {f g : UltraFilterBase α} (h : (f : FilterBase α) ≤ g) : f = g := coe_injective (g.unique h)

@[ext]
theorem ext ⦃f g : UltraFilterBase α⦄ (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
  coe_injective <| FilterBase.ext h


end UltraFilterBase
