import Math.Algebra.Module.Submodule
import Math.Data.Cardinal.Order

namespace Submodule.Basis

noncomputable section

variable {V: Type*} (R: Type*) [FieldOps R] [IsField R]
  [AddGroupOps V] [IsAddGroup V] [IsAddCommMagma V]
  [SMul R V] [IsModule R V] [DecidableEq V]

-- def not_mem_zero [SetLike S V] [IsBasis R V S] (s: S) : ¬0 ∈ s := by
--   intro hs
--   have eq := is_linear_indep (M := V) R s (LinearCombination.single 1 0) ?_
--   simp at eq
--   have : LinearCombination.single (1: R) (0: V) 0 = 1 := by simp [LinearCombination.apply_single]
--   rw [eq] at this
--   exact zero_ne_one _ this
--   intro v hv
--   obtain ⟨_, rfl⟩ := LinearCombination.mem_support_single hv
--   assumption

-- def basis_of_subsingleton [Subsingleton V] : Basis R V where
--   carrier := ∅
--   indep lc supp_empty eq := by
--     induction lc with
--       | zero => rfl
--       | single r v hr =>
--         have : v ∈ Set.support (LinearCombination.single r v) := by
--           rwa [Set.mem_support, LinearCombination.apply_single, if_pos rfl]
--         rw [Set.sub_empty _ supp_empty] at this
--         contradiction
--       | add x y hx hy supp_eq of_add_eq_zero =>
--         rw [supp_eq] at supp_empty
--         rw [hx, hy, add_zero]
--         apply Set.sub_trans _ supp_empty
--         apply Set.sub_union_right
--         rw [LinearCombination.of_empty_support y, map_zero]
--         apply Set.of_sub_empty
--         apply Set.sub_trans _ supp_empty
--         apply Set.sub_union_right

--         apply Set.sub_trans _ supp_empty
--         apply Set.sub_union_left
--         rw [LinearCombination.of_empty_support x, map_zero]
--         apply Set.of_sub_empty
--         apply Set.sub_trans _ supp_empty
--         apply Set.sub_union_left
--   complete := by
--     intro v
--     rw [Subsingleton.allEq v 0]
--     apply mem_zero

-- instance [Subsingleton V] : Subsingleton (Basis R V) where
--   allEq := by
--     suffices ∀a, a = basis_of_subsingleton R by intro a b; rw [this a, this b]
--     intro b
--     ext v
--     show v ∈ b ↔ v ∈ (∅: Set V)
--     simp [Set.not_mem_empty]
--     intro hv
--     rw [Subsingleton.allEq v 0] at hv
--     exact not_mem_zero R b hv

-- private def basis_card_le (a b: Basis R V) : #a ≤ #b := by
--   rcases subsingleton_or_nontrivial V with hv | hv
--   rw [Subsingleton.allEq a b]
--   have ⟨v, v_ne_zero⟩ := exists_ne 0
--   sorry

-- def basis_card_eq (a b: Basis R V) : #a = #b := by
--   apply le_antisymm
--   apply basis_card_le
--   apply basis_card_le

-- private def to_basis (a b: Basis R V) (x: a) : b where
--   val := by
--     let lcx := Classical.choose (b.complete x.val)
--     have : Set.support lcx ⊆ b ∧ x.val = lcx := Classical.choose_spec (b.complete x.val)
--     obtain ⟨lcx_supp, lcx_eq⟩ := this
--     sorry
--   property := sorry

end

end Submodule.Basis
