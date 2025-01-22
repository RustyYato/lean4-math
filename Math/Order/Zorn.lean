import Math.Order.Chain
import Math.Relation.Basic

namespace Zorn

section

variable {α β : Type*} {r : α → α → Prop} {c : Set α} [Relation.IsTrans r]

local infixl:50 " ≼ " => r

-- if every chain has an upper bound, then there exists a maximal chain
def exists_maximal_of_chains_bounded (h : ∀ c, Set.IsChain r c → ∃ ub, ∀ a ∈ c, a ≼ ub)
  (trans: ∀{a b c}, a ≼ b -> b ≼ c -> a ≼ c := by exact Relation.trans):
  ∃ m, ∀ a, m ≼ a → a ≼ m := by
  have : ∃ ub, ∀ a ∈ Set.maxChain r, a ≼ ub := h _ Set.maxChain_spec.left
  obtain ⟨ub, spec⟩ := this
  exists ub
  intro x rx
  apply spec
  suffices Set.maxChain r = insert x (Set.maxChain r) by
    rw [this]
    apply Set.mem_insert.mpr; left; rfl
  apply Set.maxChain_spec.right _ _
  intro y mem
  apply Set.mem_insert.mpr
  right; assumption
  apply (Set.IsChain.insert Set.maxChain_spec.left x)
  intro y mem
  right; right
  exact trans (spec _ mem) rx

end

section PreOrder

variable [LT α] [LE α] [IsPreOrder α]

def preorder (h : ∀ c : Set α, Set.IsChain (· ≤ ·) c → Set.BoundedAbove c) :
    ∃ m : α, ∀ a, m ≤ a → a ≤ m := exists_maximal_of_chains_bounded h

def preorder_in (U: Set α) (h : ∀c ⊆ U, Set.IsChain (· ≤ ·) c → ∃ub ∈ U, ∀x ∈ c, x ≤ ub) :
    ∃ m ∈ U, ∀a ∈ U, m ≤ a → a ≤ m := by
    have ⟨m, spec⟩  := exists_maximal_of_chains_bounded (α := U) (r := fun x y => (x.val ≤ y.val)) ?_ ?_
    refine ⟨_, m.property, ?_⟩
    intro a mem sub
    apply spec ⟨_, mem⟩ sub
    intro s c
    obtain h := h (s.image Subtype.val) (by
      intro s' ⟨_, eq, _⟩
      subst s'
      apply Subtype.property) (by
        refine ⟨?_⟩
        intro ⟨_, a, mema, eqa⟩ ⟨_, b, memb, eqb⟩
        subst eqa; subst eqb
        unfold Set.Induced
        dsimp
        rcases c.tri ⟨_, mema⟩ ⟨_, memb⟩ with lt | eq | gt
        left; assumption
        right; left
        cases eq; congr
        right; right; assumption)
    obtain ⟨ub, ub_in_S, h⟩ := h
    dsimp
    exists ⟨ub, ub_in_S⟩
    intro a mem
    dsimp
    apply h
    apply Set.mem_image'
    assumption
    intro a b c
    apply le_trans

end PreOrder

section PartialOrder

variable [LT α] [LE α] [IsPartialOrder α]

def partialorder (h : ∀ c : Set α, Set.IsChain (· ≤ ·) c → Set.BoundedAbove c) :
    ∃ m : α, ∀ a, m ≤ a → a = m := by
    have ⟨m, spec⟩  := preorder h
    exists m
    intro a le
    apply le_antisymm _ le
    apply spec
    assumption

def partialorder_in (U: Set α) (h : ∀c ⊆ U, Set.IsChain (· ≤ ·) c → ∃ub ∈ U, ∀x ∈ c, x ≤ ub) :
    ∃ m ∈ U, ∀a ∈ U, m ≤ a → a = m  := by
    have ⟨m, m_in, spec⟩ := preorder_in U h
    refine ⟨m, m_in, ?_⟩
    intro a a_in le
    apply le_antisymm _ le
    apply spec
    assumption
    assumption

end PartialOrder

def subset (S : Set (Set α))
    (h : ∀ c ⊆ S, Set.IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub):
    ∃ m ∈ S, ∀ a ∈ S, m ⊆ a → a = m := partialorder_in S h

def superset (S : Set (Set α))
    (h : ∀ c ⊆ S, Set.IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) :
    ∃ m ∈ S, ∀ a ∈ S, a ⊆ m → a = m := by
    apply partialorder_in (α := Opposite (Set α)) S
    intro s sub c
    apply h
    assumption
    refine ⟨?_⟩
    obtain ⟨c⟩ := c
    intro a b
    rcases c a b with lt | eq | gt
    right; right; assumption
    right; left; assumption
    left; assumption

end Zorn
