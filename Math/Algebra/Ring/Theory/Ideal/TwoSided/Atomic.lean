import Math.Algebra.Ring.Theory.Ideal.TwoSided.Lattice
import Math.Order.Zorn

variable [RingOps R] [IsRing R] {i: Ideal R}

private def ProperIdeal (i: Ideal R) := { j: Ideal R // j ≠ ⊤ ∧ i ≤ j }

private instance : LE (ProperIdeal i) where
  le a b := a.val ≤ b.val

private instance : LT (ProperIdeal i) where
  lt a b := a.val < b.val

private instance : IsLawfulLT (ProperIdeal i) where
  lt_iff_le_and_not_le := Iff.rfl

private def ProperIdeal.oemb (i: Ideal R) : ProperIdeal i ↪o Ideal R where
  toFun x := x.val
  inj' := Subtype.val_inj
  resp_rel := Iff.rfl

private instance : IsPartialOrder (ProperIdeal i) := (ProperIdeal.oemb _).inducedIsPartialOrder'

instance : IsCoatomic (Ideal R) where
  exists_coatom_of_ne_top := by
    intro i hi
    have ⟨a, ha⟩ : ∃a, a ∉ i := by
      apply Classical.byContradiction
      conv => { rw [not_exists]; arg 1; intro; rw [Classical.not_not] }
      intro h; apply hi
      apply SetLike.coe_inj
      apply Set.ext_univ
      assumption
    have ⟨mi, mi_spec⟩ := Zorn.partialorder (α := ProperIdeal i) ?_
    exists mi.val
    apply And.intro _ mi.property.right
    apply And.intro
    exact mi.property.left
    intro j h
    apply Classical.byContradiction
    intro ne
    have := mi_spec ⟨j, ne, ?_⟩ (le_of_lt h)
    rw [←this] at h
    exact lt_irrefl h
    apply le_trans _ (le_of_lt h)
    apply mi.property.right
    intro C Cchain
    by_cases h:C.Nonempty
    let bound : Ideal R :=
      {
        carrier := ⋃ C.image fun x => x.val.carrier
        mem_zero' := by
          have ⟨j, j_mem⟩ := h
          exists j.val.carrier
          apply And.intro
          apply Set.mem_image'; assumption
          apply mem_zero j.val
        mem_add' := by
          intro a b ⟨_, ⟨c, c_in_C, rfl⟩, a_in_c⟩ ⟨_, ⟨d, d_in_C, rfl⟩, b_in_d⟩
          rcases Relation.total (C.Induced (· ≤ ·)) ⟨c, c_in_C⟩ ⟨d, d_in_C⟩ with h | h
          refine ⟨d.val.carrier, ?_, ?_⟩
          apply Set.mem_image'; assumption
          apply mem_add d.val
          apply h; assumption
          assumption
          refine ⟨c.val.carrier, ?_, ?_⟩
          apply Set.mem_image'; assumption
          apply mem_add c.val
          assumption
          apply h; assumption
        mem_neg' := by
          intro x ⟨_, ⟨a, _, rfl⟩, _⟩
          refine ⟨a.val.carrier, ?_, ?_⟩
          apply Set.mem_image'; assumption
          apply mem_neg a.val
          assumption
        mem_mul_left' := by
          intro r x ⟨_, ⟨a, _, rfl⟩, _⟩
          refine ⟨a.val.carrier, ?_, ?_⟩
          apply Set.mem_image'; assumption
          show _ ∈ a.val
          apply mem_mul_left
          assumption
        mem_mul_right' := by
          intro r x ⟨_, ⟨a, _, rfl⟩, _⟩
          refine ⟨a.val.carrier, ?_, ?_⟩
          apply Set.mem_image'; assumption
          show _ ∈ a.val
          apply mem_mul_right
          assumption
      }
    refine ⟨⟨bound, ?_, ?_⟩ , ?_⟩
    · intro g
      have : 1 ∈ bound := by rw [g]; trivial
      replace ⟨_, ⟨j, j_in_C, rfl⟩, one_in_j⟩ := Set.mem_sUnion.mp this
      exact j.property.left (Ideal.eq_univ_of_mem_unit j.val 1 one_in_j)
    · obtain ⟨j, j_in_C⟩ := h
      apply le_trans j.property.right
      apply Set.sub_sUnion
      apply Set.mem_image'
      assumption
    · intro j j_in_C
      unfold LE.le instLEProperIdeal
      simp
      apply Set.sub_sUnion
      apply Set.mem_image'
      assumption
    · refine ⟨⟨i, hi, le_refl _⟩, ?_⟩
      cases Set.not_nonempty _ h
      intro _ _; contradiction

-- there is always a maximal ideal larger than every proper ideal
def Ideal.le_maximal_of_ne_top (i: Ideal R) (h: i ≠ ⊤) : ∃m: Ideal R, m.isMaximal ∧ i ≤ m :=
  exists_coatom_of_ne_top i h
