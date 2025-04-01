import Math.Data.Fintype.Basic
import Math.Order.Lattice.Basic

namespace Finset

variable [DecidableEq α]

instance : LE (Finset α) where
  le a b := a ⊆ b
instance : LT (Finset α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : Max (Finset α) where
  max a b := a ∪ b
instance : Min (Finset α) where
  min a b := a ∩ b

instance [Fintype α] : Top (Finset α) := ⟨.univ _⟩
instance : Bot (Finset α) := ⟨∅⟩

instance : IsLattice (Finset α) where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl _ _ := id
  le_trans := by
    intro a b c ab bc x hx
    apply bc
    apply ab
    assumption
  le_antisymm := by
    intro a b ab ba
    ext x;
    apply Iff.intro
    apply ab
    apply ba
  le_sup_left := by
    intro a b x mem
    exact mem_union.mpr (.inl mem)
  le_sup_right := by
    intro a b x mem
    exact mem_union.mpr (.inr mem)
  inf_le_left := by
    intro a b x mem
    exact (mem_inter.mp mem).left
  inf_le_right := by
    intro a b x mem
    exact (mem_inter.mp mem).right
  sup_le := by
    intro a b k ka kb x mem
    cases mem_union.mp mem
    apply ka; assumption
    apply kb; assumption
  le_inf := by
    intro a b k ka kb x mem
    apply mem_inter.mpr
    apply And.intro
    apply ka; assumption
    apply kb; assumption

instance : IsLawfulBot (Finset α) where
  bot_le a x _ := by contradiction

instance [Fintype α] : IsLawfulTop (Finset α) where
  le_top _ _ _ := mem_univ _

def lt_spec {a b: Finset α} : a < b -> ∃x ∈ b, x ∉ a := by
  cases a with | mk a ha =>
  cases b with | mk b hb =>
  cases a with | mk a =>
  cases b with | mk b =>
  show a ⊆ b ∧ ¬b ⊆ a -> ∃x ∈ b, x ∉ a
  clear ha hb
  intro ⟨sub, nsub⟩
  have := Classical.not_forall.mp nsub
  conv at this => { arg 1; intro; rw [not_imp] }
  assumption

instance : @Relation.IsWellFounded (Finset α) (· < ·) where
  wf := by
    apply WellFounded.intro
    intro ⟨a, ha⟩
    cases a with | mk a =>
    generalize hl:a.length=l
    induction l using Nat.strongRecOn generalizing a with
    | ind l ih =>
      apply Acc.intro
      intro ⟨b, hb⟩ r
      cases b with | mk b =>
      have ⟨x, hxa, hxb⟩ := lt_spec r
      obtain ⟨r₀, r₁⟩ := r
      obtain r₀ : b ⊆ a := r₀
      obtain r₁ : ¬a ⊆ b := r₁
      obtain hxa: x ∈ a := hxa
      obtain hxb: x ∉ b := hxb
      apply ih b.length
      any_goals rfl
      apply Nat.lt_of_lt_of_le
      apply Nat.lt_of_le_of_ne
      exact Finset.card_le_of_sub (a := ⟨Multiset.mk b, hb⟩) (b := ⟨Multiset.mk a, ha⟩) r₀
      intro eq
      have b_perm_a := Quotient.exact <| Subtype.mk.inj <| Finset.eq_of_sub_of_card_eq (a := ⟨Multiset.mk b, ?_⟩) (b := ⟨Multiset.mk a, ?_⟩) r₀ eq
      have := b_perm_a.mem_iff.mpr hxa
      contradiction
      assumption
      assumption
      rw [←hl]
      apply Nat.le_refl

def Finset.relIso [Fintype α] [DecidableEq α] : (· > (·: Finset α)) ≃r (· < (·: Finset α)) where
  toFun x := xᶜ
  invFun x := xᶜ
  leftInv := by
    intro x
    simp
  rightInv := by
    intro x
    simp
  resp_rel := by
    intro a b
    dsimp
    suffices ∀{a b: Finset α}, a > b -> aᶜ < bᶜ by
      apply Iff.intro
      apply this
      intro
      rw [←compl_compl a, ←compl_compl b]
      apply this
      assumption
    intro a b ⟨h, g⟩
    apply And.intro; intro x
    simp [mem_compl]
    intro ha hb
    exact ha (h _ hb)
    intro i
    apply g
    intro x mem
    have := i x
    simp [mem_compl] at this
    exact Decidable.not_not.mp (this · mem)

instance [Fintype α] [DecidableEq α] : @Relation.IsWellFounded (Finset α) (· > ·) :=
  Finset.relIso.toRelHom.wf

end Finset
