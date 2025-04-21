import Math.Data.FastFintype.Defs

private def Remove (a: α) := { x: α // x ≠ a }

open Classical

noncomputable instance (α: Type u) [fα: Fintype α] (a: α) : Fintype (Remove a) :=
  fα.map fun fα =>
  have : fα.card ≠ 0 := by
    intro h
    induction Fintype.equiv_of_card_eq PEmpty.{u+1} α (ha := inferInstance) (hb := ⟨Trunc.mk fα⟩) (by symm; simpa) with | _ eqv =>
    have := eqv.symm a
    contradiction
  let n := fα.card - 1
  let ia := (fα.equiv_fin_card a).cast (m := n + 1) (by omega)
  have := Embedding.fin_erase ia
  {
    card := n
    all := {
      toFun i :=
        if hi:i.val < ia.val then
          {
            val := fα.all ⟨i.val, by omega⟩
            property := by
              rw [←fα.equiv_fin_card.coe_symm a,
                fα.equiv_fin_card_symm_eq]
              intro h
              rw [fα.all.inj.eq_iff, ←Fin.val_inj] at h
              replace h : i.val = ia.val := h
              rw [h] at hi
              exact Nat.lt_irrefl _ hi
          }
        else
          {
            val := fα.all ⟨i.val + 1, by omega⟩
            property := by
              rw (occs := [2]) [←fα.equiv_fin_card.coe_symm a]
              rw [fα.equiv_fin_card_symm_eq]
              intro h
              rw [fα.all.inj.eq_iff, ←Fin.val_inj] at h
              replace h : i.val + 1 = ia.val := h
              rw [←h] at hi
              omega
          }
      inj' := by
        intro ⟨x, xLt⟩ ⟨y, yLt⟩ h
        simp at h
        split at h <;> split at h <;> rename_i hx hy
        all_goals
        cases fα.all.inj (Subtype.mk.inj h)
        omega
    }
    complete x := by
      have ⟨i, hi⟩ := fα.complete x.val
      simp
      rcases Nat.lt_trichotomy i.val ia.val with h | h | h
      · exists ⟨i.val, by omega⟩
        rw [dif_pos]
        apply Subtype.val_inj
        simpa
        assumption
      · have : i = fα.equiv_fin_card a := by ext; assumption
        subst i
        simp [← fα.equiv_fin_card_symm_eq] at hi
        have := x.property
        contradiction
      · exists ⟨i.val - 1, by omega⟩
        rw [dif_neg]
        apply Subtype.val_inj
        rw [hi]
        congr; ext; dsimp; omega
        dsimp; omega
  }

private noncomputable def card_succ_eqv_option (α: Type u) (a: α) :
  α ≃ Option (Remove a) where
  toFun x := if h:x = a then .none else .some ⟨x, h⟩
  invFun
  | .none => a
  | .some x => x.val
  leftInv x := by by_cases h:x = a <;> simp [h]
  rightInv x := by
    cases x <;> simp
    rename_i x
    exists x.property

def induction
  {motive: ∀α: Type u, Fintype α -> Prop}
  (empty: motive PEmpty inferInstance)
  (option: ∀(α: Type u) (f: Fintype α), motive α f -> motive (Option α) inferInstance)
  (resp: ∀(α β: Type u) (fα: Fintype α) (fβ: Fintype β), α ≃ β -> motive α fα -> motive β fβ)
  {α: Type u} (f: Fintype α) : motive _ f := by
  classical
  induction h:Fintype.card α generalizing α with
  | zero =>
    induction Fintype.equiv_of_card_eq PEmpty α (ha := inferInstance) (by symm; simpa) with | _ eqv =>
    refine resp PEmpty α inferInstance f ?_ empty
    assumption
  | succ n ih =>
    induction f with | mk f =>
    replace h : f.card = n + 1 := h
    let ft : Fintype α := ⟨Trunc.mk f⟩
    apply resp _ _ inferInstance inferInstance (card_succ_eqv_option α (f.all ⟨0, by omega⟩)).symm
    apply option
    apply ih
    show f.card - 1 = _
    omega
