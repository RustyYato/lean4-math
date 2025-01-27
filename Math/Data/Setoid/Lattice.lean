import Math.Order.Lattice.Complete

open Relation

variable {α: Type*}

instance : LE (Setoid α) where
  le a b := ∀⦃x y⦄, a.r x y -> b.r x y

instance : LT (Setoid α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : Bot (Setoid α) where
  bot := setoid (· = ·)

instance : Top (Setoid α) where
  top := setoid trivial

instance : Inf (Setoid α) where
  inf a b := setoid (relAnd a.r b.r)

instance : Sup (Setoid α) where
  sup a b := setoid (TransGen (relOr a.r b.r))

instance : InfSet (Setoid α) where
  sInf U := {
    r x y := ∀s ∈ U, s.r x y
    iseqv := {
      refl x s _ := s.iseqv.refl x
      symm r s hs := s.iseqv.symm (r _ hs)
      trans ab bc s hs := s.iseqv.trans (ab _ hs) (bc _ hs)
    }
  }

def preSSup (U: Set (Setoid α)) (x y: α) : Prop := ∃s ∈ U, s.r x y

instance : IsSymmetric (preSSup U) where
  symm r := by
    obtain ⟨s, hs, r⟩ := r
    refine ⟨_, hs, s.iseqv.symm r⟩

instance : SupSet (Setoid α) where
  sSup U := setoid (ReflTransGen (preSSup U))

instance : IsPartialOrder (Setoid α) where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl a x y := id
  le_trans ab bc x y a := bc (ab a)
  le_antisymm := by
    intro a b ab ba
    cases a with | mk a aeqv =>
    cases b with | mk b beqv =>
    congr
    ext x y
    apply Iff.intro
    apply ab
    apply ba

instance : IsCompleteLattice (Setoid α) where
  bot_le := by
    intro a x y r
    subst y
    rfl
  le_top := by
    intro _ _ _ _
    trivial
  le_sup_left := by
    intro a b x y r
    apply TransGen.single
    left; assumption
  le_sup_right := by
    intro a b x y r
    apply TransGen.single
    right; assumption
  sup_le := by
    intro a b k ak bk x y r
    induction r with
    | single r =>
      rcases r with r | r
      apply ak
      assumption
      apply bk
      assumption
    | tail _ r =>
      apply Relation.trans
      assumption
      rcases r with r | r
      apply ak
      assumption
      apply bk
      assumption
  inf_le_left := by
    intro a b x y r
    exact r.left
  inf_le_right := by
    intro a b x y r
    exact r.right
  le_inf := by
    intro a b k ak bk x y r
    exact ⟨ak r, bk r⟩
  le_sSup := by
    intro U s hs x y r
    apply ReflTransGen.single
    exists s
  sSup_le := by
    intro k U h x y r
    induction r with
    | refl => rfl
    | cons r _ ih =>
      apply Relation.trans _ ih
      obtain ⟨s, hs, r⟩ := r
      apply h
      assumption
      assumption
  sInf_le := by
    intro U s hs x y r
    apply r
    assumption
  le_sInf := by
    intro k U h x y r s hs
    apply h
    assumption
    assumption
