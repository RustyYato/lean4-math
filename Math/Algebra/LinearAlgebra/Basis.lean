import Math.Algebra.LinearAlgebra.Basic
import Math.Order.Zorn
import Math.Data.List.Basic

namespace VectorSpace

structure PreBasis {R A: Type*} (V: VectorSpace R A) where
  set: Set V.Vector
  linear_indep: V.IsLinearlyIndependent set

instance : LE (PreBasis V) where
  le a b := a.set ⊆ b.set
instance : LT (PreBasis V) where
  lt a b := a ≤ b ∧ ¬b ≤ a
instance : IsLawfulLT (PreBasis V) where
  lt_iff_le_and_not_le := Iff.rfl

def orderEmbedSet (V: VectorSpace R A) : (PreBasis V) ↪o Set V.Vector where
  toFun a := a.set
  inj' := by intro a b eq; cases a; congr
  resp_rel := Iff.rfl

instance : IsPartialOrder (PreBasis V) :=
  (orderEmbedSet V).inducedIsPartialOrder'

open Classical in
noncomputable def PreBasis.sup (a b: PreBasis V) : PreBasis V :=
  if a ≤ b then b else a

def PreBasis.le_sup_left (a b: PreBasis V) : a ≤ sup a b := by
  unfold sup
  split
  assumption
  rfl

def PreBasis.le_sup_right (a b: PreBasis V) (h: a ≤ b ∨ b ≤ a) : b ≤ sup a b := by
  unfold sup
  split
  rfl
  cases h
  contradiction
  assumption

def existsBasis (V: VectorSpace R A) : ∃basis: Set V.Vector, V.IsBasis basis := by
  have ⟨basis, is_maximal⟩ := Zorn.partialorder (α := PreBasis V) ?_
  refine ⟨basis.set, basis.linear_indep, ?_⟩
  · apply Set.ext_univ
    intro v
    apply Classical.byContradiction
    intro hv
    have := is_maximal {
      set := insert v basis.set
      linear_indep := ?_
    } ?_
    have := PreBasis.mk.inj this
    apply hv
    rw [←this]
    refine ⟨[1], [v], ?_, ?_, ?_⟩
    rfl
    intro v' hv
    cases hv
    simp
    contradiction
    unfold linear_combination linear_combination
    dsimp
    rw [add_zero, one_smul]
    · intro xs xs_nodup hxs rs eq h
      by_cases v ∈ xs
      · rename_i hvx
        have ⟨i, hi, eq⟩ := List.getElem_of_mem hvx
        subst v; clear hvx
        rw [linear_combination_extract (i := i) (hi := by
          rw [List.length_zip, eq, Nat.min_self]
          exact hi)] at h
        by_cases hr:rs[i]=0
        · simp at h
          rw [hr, zero_smul, zero_add] at h
          have := basis.linear_indep (xs.eraseIdx i) (xs_nodup.eraseIdx _) ?_ (rs.eraseIdx i) (by
            rw [List.length_eraseIdx, List.length_eraseIdx, eq]) (by
            rw [←List.eraseIdx_zip]
            assumption)
          intro r hr
          have ⟨j, hj, eqj⟩ := List.getElem_of_mem hr
          rcases Nat.lt_trichotomy i j with ij | rfl | ji
          · apply this
            apply List.mem_iff_getElem.mpr
            refine ⟨j - 1, ?_, ?_⟩
            apply Nat.sub_lt_left_of_lt_add
            apply Nat.succ_le_of_lt
            apply Nat.zero_lt_of_lt
            assumption
            rw [List.length_eraseIdx, if_pos, Nat.add_sub_cancel']
            assumption
            apply Nat.succ_le_of_lt
            apply Nat.zero_lt_of_lt
            assumption
            apply Nat.lt_trans <;> assumption
            rw [List.getElem_eraseIdx, dif_neg, ←eqj]
            congr
            rw [Nat.sub_add_cancel]
            apply Nat.succ_le_of_lt
            apply Nat.zero_lt_of_lt
            assumption
            intro g
            have := Nat.lt_irrefl _ <| Nat.lt_of_le_of_lt (Nat.le_pred_of_lt ij) g
            contradiction
          · subst r
            assumption
          · apply this
            apply List.mem_iff_getElem.mpr
            refine ⟨j, ?_, ?_⟩
            rw [List.length_eraseIdx, if_pos]
            apply Nat.lt_pred_of_succ_lt
            show j.succ < rs.length
            rw [eq]
            apply flip Nat.lt_of_le_of_lt
            assumption
            apply Nat.succ_le_of_lt
            exact ji
            rw [eq]; assumption
            rw [List.getElem_eraseIdx, dif_pos, ←eqj]
            assumption
          · intro v hv'
            have := hxs v ?_; simp at this
            cases this
            subst v
            exfalso
            have ⟨j, hj, eq'⟩ := List.getElem_of_mem hv'
            rw [List.getElem_eraseIdx] at eq'
            split at eq'
            have := List.nodup_getElem_inj xs_nodup eq'
            subst i
            have := Nat.lt_irrefl j; contradiction
            have := List.nodup_getElem_inj xs_nodup eq'
            subst i
            have := Nat.lt_succ_self j; contradiction
            assumption
            apply List.mem_of_mem_eraseIdx
            assumption
        · exfalso
          rw [add_eq_iff_eq_sub, zero_sub] at h
          rw [List.getElem_zip] at h
          have : rs[i]⁻¹? • (rs[i] • xs[i]) = rs[i]⁻¹? • (-V.linear_combination ((rs.zip xs).eraseIdx i)) := by rw [h]
          rw [←mul_smul, inv?_mul_cancel, one_smul, smul_neg, ←neg_smul, smul_linear_combination] at this
          apply hv
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          exact List.map (fun r₀ => -rs[i]⁻¹? * r₀) (rs.eraseIdx i)
          exact xs.eraseIdx i
          rw [List.length_map]
          · rw [List.length_eraseIdx, List.length_eraseIdx, if_pos, if_pos, eq]
            assumption
            rw [eq]; assumption
          . intro x hx
            have := hxs x (List.mem_of_mem_eraseIdx hx)
            simp at this; cases this
            subst x
            have ⟨j, hj, eq'⟩ := List.getElem_of_mem hx
            rw [List.getElem_eraseIdx] at eq'
            split at eq'
            have := List.nodup_getElem_inj xs_nodup eq'
            subst i
            have := Nat.lt_irrefl j; contradiction
            have := List.nodup_getElem_inj xs_nodup eq'
            subst i
            have := Nat.lt_succ_self j; contradiction
            assumption
          rw [←List.eraseIdx_map, ←List.eraseIdx_zip, this, ←List.eraseIdx_map, List.zip_map_left]
          rfl
      · apply basis.linear_indep _ _ _ _ eq h
        assumption
        intro x hx
        have := hxs x hx
        simp at this
        cases this
        subst x
        contradiction
        assumption
    · intro x hx
      simp [hx]
  · intro S C
    refine ⟨{ set := ⋃ S.image PreBasis.set, linear_indep := ?_ }, ?_⟩
    · intro xs xs_nodup hx rs len_eq h
      by_cases hS:S.Nonempty
      · have : ∃s: V.PreBasis, s ∈ S ∧ Set.ofList xs ⊆ s.set := by
          clear h len_eq rs
          induction xs with
          | nil =>
            obtain ⟨v, _⟩ := hS
            exists v
            apply And.intro
            assumption
            intro _ _; contradiction
          | cons x xs ih =>
            have ⟨s, hs, sub⟩ := ih xs_nodup.tail (by
              apply Set.sub_trans _ hx
              intro
              apply List.Mem.tail _)
            have ⟨_, ⟨v, hv, rfl⟩, hxv⟩ := hx x (List.Mem.head _)
            exists s.sup v
            apply And.intro
            · unfold PreBasis.sup
              split
              assumption
              assumption
            · intro y hy
              cases hy
              apply PreBasis.le_sup_right
              rcases C.tri ⟨_, hs⟩ ⟨_, hv⟩ with h | h | h
              left; assumption
              cases h
              left; rfl
              right; assumption
              assumption
              apply PreBasis.le_sup_left
              apply sub
              assumption
        obtain ⟨s, hs, xs_sub⟩ := this
        exact s.linear_indep xs xs_nodup xs_sub rs len_eq h
      · intro r hr
        cases Set.not_nonempty _ hS
        rw [Set.empty_image, Set.sUnion_empty] at hx
        cases xs
        cases rs
        contradiction
        contradiction
        have := hx _ (List.Mem.head _)
        contradiction
    · intro s hs
      apply Set.sub_sUnion
      apply Set.mem_image'
      assumption

noncomputable
def basis (V: VectorSpace R A) : Set V.Vector := Classical.choose V.existsBasis

def basis_spec (V: VectorSpace R A) : V.IsBasis V.basis := Classical.choose_spec V.existsBasis

def basis_linear_indep (V: VectorSpace R A) : V.IsLinearlyIndependent V.basis := V.basis_spec.left
def mem_basis (V: VectorSpace R A) : ∀v, v ∈ V.Span V.basis := by
  intro v
  rw [V.basis_spec.right]
  trivial

end VectorSpace
