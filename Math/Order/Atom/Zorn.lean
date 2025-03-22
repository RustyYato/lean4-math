import Math.Order.Atom.Basic
import Math.Order.Zorn
import Math.Data.Set.Order.Interval

open Set

def IsCoatomic.of_isChain_bounded {α : Type*}
  [LE α] [LT α] [Top α] [IsPartialOrder α] [IsLawfulTop α]
  (h : ∀ c : Set α, c.IsChain (· ≤ ·) → c.Nonempty → ⊤ ∉ c → ∃ x ≠ ⊤, x ∈ c.upperBounds) :
  IsCoatomic α := by
  refine ⟨fun x htop => ?_⟩
  have : ∃ y ∈ Ico x ⊤, x ≤ y ∧ ∀ z ∈ Ico x ⊤, y ≤ z → z = y := by
    have ⟨y, y_in_up, hy⟩  := Zorn.partialorder_in (Ico x ⊤) ?_
    refine ⟨y, y_in_up, ?_, ?_⟩
    apply y_in_up.left
    assumption
    intro c c_sub hc
    by_cases gc:c.Nonempty
    have ⟨z, z_ne, z_in_up⟩  := h c hc gc  (fun g => ?_)
    refine ⟨z, ?_, ?_⟩
    apply And.intro
    obtain ⟨y, y_in_c⟩ := gc
    apply flip le_trans
    apply z_in_up
    assumption
    apply (c_sub y _).left
    assumption
    apply lt_of_le_of_ne
    apply le_top
    assumption
    apply z_in_up
    exact lt_irrefl (c_sub _ g).right
    cases Set.not_nonempty _ gc
    exists x
    apply And.intro
    apply And.intro
    apply le_refl
    apply lt_of_le_of_ne
    apply le_top
    assumption
    intros; contradiction
  obtain ⟨y, mem_y, x_le_y, hy⟩ := this
  refine ⟨y, ⟨?_, ?_⟩, x_le_y⟩
  intro h; subst y
  exact lt_irrefl mem_y.right
  intro z hz
  apply Classical.byContradiction
  intro g
  cases hy z ⟨le_trans x_le_y (le_of_lt hz), lt_of_le_of_ne (le_top _) g⟩ (le_of_lt hz)
  exact lt_irrefl hz

def IsAtomic.of_isChain_bounded {α : Type*}
  [LE α] [LT α] [Bot α] [IsPartialOrder α] [IsLawfulBot α]
  (h : ∀ c : Set α, c.IsChain (· ≤ ·) → c.Nonempty → ⊥ ∉ c → ∃ x ≠ ⊥, x ∈ c.lowerBounds) :
  IsAtomic α :=
  have := IsCoatomic.of_isChain_bounded (α := αᵒᵖ) <| by
    intro S Schain Sne g
    refine h (S.preimage Opposite.get) ?_ Sne g
    refine ⟨fun a b => ?_⟩
    rcases Schain.tri ⟨Opposite.mk a.val, a.property⟩ ⟨Opposite.mk b.val, b.property⟩ with h | h | h
    right; right
    assumption
    right; left
    assumption
    left
    assumption
  inferInstanceAs (IsAtomic αᵒᵖᵒᵖ)
