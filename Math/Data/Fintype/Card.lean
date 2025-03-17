import Math.Data.Fintype.Algebra
import Math.Data.Fintype.Cases
import Math.Data.Nat.Factorial

namespace Fintype

def card_sigma {α: Type*} {β: α -> Type*} [ha: Fintype α] [hb: ∀x, Fintype (β x)] : card (Σx: α, β x) = ∑x: α, card (β x) := by
  induction ha using typeInduction with
  | empty => rfl
  | option α _ ih =>
    rw [sum_option, card_eq_of_equiv Equiv.option_sigma_equiv_sum_sigma,
      card_sum]
    congr
    apply ih
  | eqv α' α eqv _ ih =>
    let eqv' := Fintype.ofEquiv' eqv
    have := @ih (β <| eqv ·) _
    apply Eq.trans _ (Eq.trans this _)
    apply card_eq_of_equiv
    refine Equiv.congrSigma ?_ ?_
    symm; assumption
    intro x
    rw [Equiv.symm_coe]
    refine sum_eq_of_equiv (ι₀ := α') (ι₁ := α) (α := Nat) _ _ eqv ?_
    intro i
    rfl

def card_prod {α: Type*} {β: Type*} [ha: Fintype α] [hb: Fintype β] : card (α × β) = card α * card β := by
  rw [card_eq_of_equiv (Equiv.prod_equiv_sigma _ _), card_sigma, sum_const]
  rfl

def card_pi {α: Type*} {β: α -> Type*} [dec: DecidableEq α] [ha: Fintype α] [hb: ∀x, Fintype (β x)] : card (∀x: α, β x) = ∏x: α, card (β x) := by
  classical
  revert β dec
  induction ha using typeInduction with
  | empty =>
    intro β _ _
    rfl
  | option α _ ih =>
    intro β _ hb
    rw [prod_option, card_eq_of_equiv Equiv.option_pi_equiv_prod_pi,
      card_prod]
    congr
    apply ih
  | eqv α' α eqv _ ih =>
    intro β _ hb
    let eqv' := Fintype.ofEquiv' eqv
    have := @ih (β <| eqv ·) _
    apply Eq.trans _ (Eq.trans this _)
    apply card_eq_of_equiv
    refine Equiv.congrPi ?_ ?_
    symm; assumption
    intro x
    rw [Equiv.symm_coe]
    refine prod_eq_of_equiv (ι₀ := α') (ι₁ := α) (α := Nat) _ _ eqv ?_
    intro i
    rfl

def card_function {α: Type*} {β: Type*} [DecidableEq α] [ha: Fintype α] [hb: Fintype β] : card (α -> β) = card β ^ card α := by
  rw [card_pi, prod_const]

def card_perm {α: Type*} [ha: Fintype α] [dec: DecidableEq α] : card (α ≃ α) = fact (card α) := by
  revert dec
  induction ha using typeInduction with
  | empty =>
    intro
    rfl
  | option α _ ih =>
    intro dec
    have dec : DecidableEq α := Embedding.optionSome.DecidableEq
    rw [card_option]
    simp; rw [←ih]
    rw [card_eq_of_equiv Equiv.option_perm_equiv_prod_perm,
      card_prod, card_option]
  | eqv α β e _ ih=>
    intro dec
    have := e.toEmbedding.DecidableEq
    let f := Fintype.ofEquiv e.symm
    rw [card_eq_of_equiv (Equiv.congrEquiv e e).symm, ih,
      card_eq_of_equiv e]

def card_equiv {α: Type*} {β: Type*} [DecidableEq α] [DecidableEq β] [ha: Fintype α] [hb: Fintype β] :
  card (α ≃ β) = if card α = card β then fact (card α) else 0 := by
  split <;> rename_i h
  · rw [←card_perm]
    induction equivOfCardEq h with | mk h' =>
    apply card_eq_of_equiv
    apply Equiv.congrEquiv
    rfl; symm; assumption
  · match g:card (α ≃ β) with
    | 0 => rfl
    | n + 1 =>
      induction inferInstanceAs (Fintype (α ≃ β)) with
      | mk all nodup complete =>
      let f := Fintype.ofList all nodup complete
      replace g : all.length = n.succ := by
        rw [←g]
        show f.card = _
        congr
        apply Subsingleton.allEq
      match all with
      | eqv::_ =>
      have := card_eq_of_equiv eqv
      contradiction

def card_embed {α: Type*} {β: Type*} [DecidableEq α] [ha: Fintype α] [hb: Fintype β] : card (α ↪ β) = if card α ≤ card β then npr (card β) (card α) else 0 := by
  split <;> rename_i h
  · rename_i dec; revert dec
    induction ha using typeInduction generalizing β with
    | empty =>
      intro dec
      rw [card_eq_of_equiv Equiv.empty_emb_equiv_unit]
      unfold npr
      rw [card_empty, Nat.sub_zero, Nat.div_self]
      rfl
      apply fact_pos
    | option α _ ih =>
      intro dec
      induction hb using typeInduction with
      | empty =>
        rw [card_option] at h; contradiction
        assumption
      | option β _ ih' =>
        clear ih'
        classical
        rw [card_option, card_option] at h
        rw [card_eq_of_equiv Embedding.option_emb_equiv_prod_emb,
          card_prod, ih (Nat.le_of_succ_le_succ h)]
        simp [card_option, npr_succ_succ]
      | eqv β β' eqv _ ih =>
        let f := Fintype.ofEquiv' eqv
        rw [←card_eq_of_equiv eqv] at *
        classical
        rw [←ih h]
        apply card_eq_of_equiv
        apply Equiv.congrEmbed
        rfl
        symm; assumption
    | eqv α α' eqv _ ih =>
      intro _
      let f := Fintype.ofEquiv' eqv
      rw [←card_eq_of_equiv eqv] at *
      classical
      rw [←ih h]
      apply card_eq_of_equiv
      apply Equiv.congrEmbed
      symm; assumption
      rfl
  · match g:card (α ↪ β) with
    | 0 => rfl
    | n + 1 =>
      induction inferInstanceAs (Fintype (α ↪ β)) with
      | mk all nodup complete =>
      let f := Fintype.ofList all nodup complete
      replace g : all.length = n.succ := by
        rw [←g]
        show f.card = _
        congr
        apply Subsingleton.allEq
      match all with
      | emb::_ =>
      have := card_le_of_embed emb
      contradiction

end Fintype
