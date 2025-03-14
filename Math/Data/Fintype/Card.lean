import Math.Data.Fintype.Algebra
import Math.Data.Fintype.Cases

namespace Fintype

def fact (n: ℕ) := ∏x: Fin n, x.val + 1
def npr (n r: ℕ) := fact n / fact (n - r)

def option_sigma_equiv_sum_sigma {β: Option α -> Type*} : (Σx: Option α, β x) ≃ β .none ⊕ Σx: α, β x where
  toFun
  | ⟨.none, b⟩ => .inl b
  | ⟨.some a, b⟩ => .inr ⟨a, b⟩
  invFun
  | .inl b => ⟨.none, b⟩
  | .inr ⟨a, b⟩ => ⟨.some a, b⟩
  leftInv x := by
    rcases x with ⟨a, b⟩
    cases a <;> rfl
  rightInv x := by cases x <;> rfl

def option_pi_equiv_prod_pi {β: Option α -> Type*} : (∀x: Option α, β x) ≃ β .none × ∀x: α, β x where
  toFun f := ⟨f _, fun _ => f _⟩
  invFun f x := match x with
     | .none => f.1
     | .some x => f.2 x
  leftInv f := by
    dsimp
    ext x
    cases x <;> rfl
  rightInv x := by cases x <;> rfl

def card_sigma {α: Type*} {β: α -> Type*} [ha: Fintype α] [hb: ∀x, Fintype (β x)] : card (Σx: α, β x) = ∑x: α, card (β x) := by
  induction ha using typeInduction with
  | empty => rfl
  | option α _ ih =>
    rw [sum_option, card_eq_of_equiv option_sigma_equiv_sum_sigma,
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
    rw [prod_option, card_eq_of_equiv option_pi_equiv_prod_pi,
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

def option_perm_equiv_prod_perm [DecidableEq α] : (Option α ≃ Option α) ≃ Option α × (α ≃ α) where
  toFun f := (f .none, Equiv.of_equiv_option_option f)
  invFun | ⟨x, f⟩ => (Equiv.congrOption f).set .none x
  leftInv := by
    intro f
    simp
    ext a b
    cases a
    rw [Equiv.set_spec]
    rename_i a
    simp [Equiv.apply_set, Equiv.of_equiv_option_option, Equiv.congrOption]
    apply Iff.intro
    intro ⟨⟨h₀, h₁⟩, h₂⟩
    rw [if_neg h₀] at h₂
    assumption
    intro h
    iterate 2 apply And.intro
    intro g; rw [g] at h
    contradiction
    intro g
    have := f.inj g
    contradiction
    rw [if_neg]
    assumption
    intro g; rw [g] at h
    contradiction
  rightInv := by
    intro (a, f)
    simp [Equiv.apply_set]
    ext x
    simp [f.apply_set, Equiv.of_equiv_option_option]
    apply Option.some.inj
    rw [Option.some_get]
    rw [Equiv.apply_set, if_neg]
    split <;> rename_i h
    rw [Equiv.set_spec]
    rw [Equiv.apply_set, if_neg] at h
    split at h
    rename_i g
    rw [←g]; rfl
    contradiction
    intro; contradiction
    rw [Equiv.apply_set, if_neg]
    split
    · rename_i g
      rw [Equiv.apply_set, if_neg, if_pos g] at h
      contradiction
      intro; contradiction
    rfl
    intro; contradiction
    intro; contradiction

def card_perm {α: Type*} [ha: Fintype α] [dec: DecidableEq α] : card (α ≃ α) = fact (card α) := by
  unfold fact
  revert dec
  induction ha using typeInduction with
  | empty =>
    intro
    rfl
  | option α _ ih =>
    intro dec
    have dec : DecidableEq α := Embedding.optionSome.DecidableEq
    rw [card_option, prod_succ]
    simp; rw [←ih]
    rw [card_eq_of_equiv option_perm_equiv_prod_perm,
      card_prod, card_option]
  | eqv α β e _ ih=>
    intro dec
    have := e.toEmbedding.DecidableEq
    let f := Fintype.ofEquiv e.symm
    rw [card_eq_of_equiv (Equiv.congrEquiv e e).symm, ih,
      prod_eq_of_equiv (h := Equiv.fin (card_eq_of_equiv e))]
    intro i
    rfl

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

def empty_emb_equiv_unit [_root_.IsEmpty α] : (α ↪ β) ≃ Unit where
  toFun _ := ()
  invFun _ := Embedding.empty
  rightInv _ := rfl
  leftInv _ := by
    ext x
    exact elim_empty x

def option_emb_equiv_prod_emb [DecidableEq α] [DecidableEq β] : (Option α ↪ Option β) ≃ Option β × (α ↪ β) where
  toFun f := (f .none, Embedding.of_option_embed_option f)
  invFun | ⟨x, f⟩ => {
    toFun
    | .some a =>
      if f a = x then
        .none
      else
        f a
    | .none => x
    inj' := by
      intro a b eq
      cases a <;> cases b <;> dsimp at eq
      rfl
      iterate 2
        split at eq
        subst x
        contradiction
        subst x
        contradiction
      split at eq
      subst x
      split at eq
      rename_i h
      congr; symm
      exact f.inj (Option.some.inj h)
      contradiction
      split at eq
      subst x
      contradiction
      congr
      rename_i h
      exact f.inj (Option.some.inj eq)
  }
  leftInv := by
    intro f
    simp
    ext a b
    cases a <;> simp [Embedding.of_option_embed_option]
    rename_i a
    split <;> rename_i b' h
    apply Iff.intro
    rintro ⟨h, rfl⟩
    assumption
    intro g
    apply And.intro
    intro g'
    have := f.inj (h.trans g')
    contradiction
    rw [h] at g
    exact Option.some.inj g
    simp
    rw [h]; exact nofun
  rightInv := by
    intro (b, f)
    unfold Embedding.of_option_embed_option
    ext a
    simp
    dsimp
    rw [Embedding.mk_apply _ _ a]
    simp
    split <;> rename_i h
    simp [Embedding.mk_apply] at h
    exact h.right.symm
    simp at h
    apply Option.some.inj
    rw [Option.some_get]; symm; assumption

@[simp] def fact_zero : fact 0 = 1 := rfl
@[simp] def fact_succ : fact (n + 1) = (n + 1) * fact n := by
  rw [fact, prod_succ]
  rfl

def fact_pos (n: ℕ) : 0 < fact n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

def npr_succ_succ (n m: Nat) : (n + 1) * npr n m = npr (n + 1) (m + 1) := by
  unfold npr
  simp
  rw [Nat.mul_div_assoc]
  induction m with
  | zero => apply Nat.dvd_refl
  | succ m ih =>
    apply Nat.dvd_trans _ ih
    rw [Nat.sub_succ]
    clear ih
    generalize n - m=k; clear n m
    cases k
    apply Nat.dvd_refl
    simp
    apply Nat.dvd_mul_left

def card_embed {α: Type*} {β: Type*} [DecidableEq α] [ha: Fintype α] [hb: Fintype β] : card (α ↪ β) = if card α ≤ card β then npr (card β) (card α) else 0 := by
  split <;> rename_i h
  · rename_i dec; revert dec
    induction ha using typeInduction generalizing β with
    | empty =>
      intro dec
      rw [card_eq_of_equiv empty_emb_equiv_unit]
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
        rw [card_eq_of_equiv option_emb_equiv_prod_emb,
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
