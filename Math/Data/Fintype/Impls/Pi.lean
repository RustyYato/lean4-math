import Math.Data.Fintype.Defs
import Math.Logic.Equiv.Basic

namespace Pi

private def cons
  [DecidableEq α] {β: α -> Type _} (b: β a) (nodup: (a ::ₘ as).Nodup) : ((x : α) → x ∈ as → β x) ↪ (x : α) → x ∈ a ::ₘ as → β x where
  toFun := by
    intro g
    intro x h
    if h':x = a then
      exact Eq.ndrec b h'.symm
    else
      apply g
      rw [Multiset.mem_cons] at h
      cases h
      contradiction
      assumption
  inj' := by
    intro f₀ f₁ eq
    dsimp only at eq
    ext x h
    have := congrFun (congrFun eq x) (by simp only [Multiset.mem_cons, h, or_true])
    rw [dif_neg, dif_neg] at this
    exact this
    intro h
    clear this
    rw [←h] at nodup
    have := nodup.head
    contradiction
    intro h
    clear this
    rw [←h] at nodup
    have := nodup.head
    contradiction

private def push_cast
  (P₀: α -> Prop)
  (P₁: α -> Prop)
  (β: α -> Sort*)
  (f₀: ∀x (_: P₀ x), β x)
  (h: (∀x (_: P₀ x), β x) = (∀x (_: P₁ x), β x))
  (g: P₀ = P₁)
  (x: α)
  (h₀: P₁ x):
  (h ▸ f₀) x h₀ = f₀ x (g.symm ▸ h₀) := by
  cases g
  cases h
  rfl

private def allOn [DecidableEq α] (list: Finset α) (β: α -> Type _) (f: ∀x, Finset (β x)) : Finset (∀x ∈ list, β x) := by
  refine list.val.rec (motive := fun list => list.Nodup -> Finset (∀x ∈ list, β x)) ?_ ?_ ?_ list.property
  · intro
    exact {nofun}
  · intro a as ih nodup
    refine (f a).flatMap_embed ?_ ?_
    · intro b
      refine (ih nodup.tail).map_emb ⟨?_, ?_⟩
      · intro f
        exact (cons b nodup) f
      · apply (cons b nodup).inj
    · intro x y hx hy
      intro f h₀ h₁
      rw [Finset.mem_map_emb] at h₀ h₁
      obtain ⟨f₀, mem₀, eq₀⟩ := h₀
      obtain ⟨f₁, mem₁, eq₁⟩ := h₁
      replace : Pi.cons x nodup f₀ = f := eq₀
      replace : Pi.cons y nodup f₁ = f := eq₁
      have eq := eq₀.trans eq₁.symm
      simp [DFunLike.coe] at eq
      have := congrFun (congrFun eq a) (by simp only [Multiset.mem_cons, true_or])
      unfold Pi.cons at this
      dsimp at this
      rw [dif_pos rfl, dif_pos rfl] at this
      exact this
  · intro a b as ih
    apply Function.hfunext
    rw [Multiset.cons_comm]
    intro as₀ as₁ eq
    simp
    refine Finset.hext _ _ ?_ ?_
    rw [Multiset.cons_comm]
    intro f₀
    simp [Finset.mem_flatMap_embed, Finset.mem_map_emb]
    apply Iff.intro
    · intro ⟨Ba, ba_in_fa, f₁, ⟨Bb, Bb_in_fb, f₂, f₂_in_ih, f₂_eq_f₁⟩, f₁_eq_f₀⟩
      refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      any_goals assumption
      intro x hx
      · if h:x = a then
          rw [h]
          assumption
        else
          apply f₂
          simpa [h] using hx
      · ext x hx
        simp at hx
        rcases hx with rfl | hx
        simp [Pi.cons]
        simp [Pi.cons]
        rw [dif_neg, dif_neg]
        all_goals
        intro h
        rw [h] at hx
        exact as₁.tail.head hx
      · ext x hx
        simp at hx
        rcases hx with rfl | rfl | hx
        simp [Pi.cons]
        · subst f₁; subst f₀
          rw [push_cast]
          simp [Pi.cons]
          rw [dif_neg]
          intro h
          rw [h] at as₀
          exact as₀.head (by simp)
          rw [Multiset.cons_comm]
        · simp [Pi.cons]
          rw [dif_neg]
          subst f₁_eq_f₀
          rw [push_cast]
          simp [Pi.cons]
          rw [Multiset.cons_comm]
          intro h
          rw [h] at as₀
          exact as₀.head (by simp)
        · simp [Pi.cons]
          rw [push_cast]
          conv => { rhs; rw [←f₁_eq_f₀]; rw [←f₂_eq_f₁] }
          simp [Pi.cons]
          rw [dif_neg, dif_neg, dif_neg, dif_neg]
          intro h
          rw [←h] at as₁
          exact as₁.head (by rw [Multiset.mem_cons]; right; assumption)
          intro h
          rw [←h] at as₀
          exact as₀.head (by rw [Multiset.mem_cons]; right; assumption)
          intro h
          rw [←h] at as₀
          exact as₀.head (by rw [Multiset.mem_cons]; right; assumption)
          intro h
          rw [←h] at as₁
          exact as₁.head (by rw [Multiset.mem_cons]; right; assumption)
          rw [Multiset.cons_comm]
    · intro ⟨Ba, ba_in_fa, f₁, ⟨Bb, Bb_in_fb, f₂, f₂_in_ih, f₂_eq_f₁⟩, f₁_eq_f₀⟩
      refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      any_goals assumption
      intro x hx
      · if h:x = b then
          rw [h]
          assumption
        else
          apply f₁
          simp [h] at hx
          simp; right; assumption
      · ext x hx
        simp at hx
        rcases hx with rfl | hx
        simp [Pi.cons]
        simp [Pi.cons]
        rw [dif_neg, dif_neg]
        rw [←f₂_eq_f₁]
        simp [Pi.cons]
        rw [dif_neg]
        intro h
        rw [h] at hx
        exact as₁.tail.head hx
        intro h
        rw [h] at hx
        exact as₀.tail.head hx
        intro h
        rw [h] at hx
        exact as₀.tail.head hx
      · ext x hx
        simp at hx
        rcases hx with rfl | rfl | hx
        simp [Pi.cons]
        rw [←f₂_eq_f₁] at f₁_eq_f₀
        have := congrFun (congrFun f₁_eq_f₀ x) (by simp)
        rw [push_cast] at this
        rw [←this]
        simp [Pi.cons]
        rw [dif_neg]
        intro h
        clear this
        rw [h] at as₁
        exact as₁.head (by simp)
        rw [Multiset.cons_comm]
        simp [Pi.cons]
        rw [dif_neg]
        have := congrFun (congrFun f₁_eq_f₀ x) (by simp)
        rw [push_cast] at this
        rw [←this]
        simp [Pi.cons]
        rw [Multiset.cons_comm]
        intro h
        rw [h] at as₁
        exact as₁.head (by simp)
        simp [Pi.cons]
        rw [dif_neg, dif_neg]
        have := congrFun (congrFun f₁_eq_f₀ x) (by simp [hx])
        rw [push_cast] at this
        rw [←this]; simp [Pi.cons]
        rw [dif_neg]
        intro h
        clear this
        rw [←h] at as₀
        exact as₀.tail.head (by simp [hx])
        rw [Multiset.cons_comm]
        intro h
        rw [←h] at as₀
        exact as₀.tail.head (by simp [hx])
        intro h
        rw [←h] at as₁
        exact as₁.tail.head (by simp [hx])

end Pi

namespace Fintype

instance {β: α -> Type*} [DecidableEq α] [ha: Fintype α] [hb: ∀x, Fintype (β x)] : Fintype (∀x, β x) where
  all := ((Pi.allOn ha.all β (fun x => (hb x).all))).map_emb ⟨fun f x => f x (Fintype.complete _), by
    intro x y h
    replace h := congrFun h
    dsimp at h
    ext
    apply h⟩
  complete := by
    intro f
    apply Finset.mem_map_emb.mpr
    refine ⟨fun x _ => f x, ?_, rfl⟩
    induction ha with
    | mk all nodup complete =>
    unfold Fintype.all ofList
    simp
    clear complete
    induction all with
    | nil =>
      show _ ∈ Pi.allOn ⟨∅, _⟩  _ _
      unfold Pi.allOn
      rw [Multiset.rec_nil]
      apply List.mem_singleton.mpr
      ext
      contradiction
    | cons a as ih =>
      show _ ∈ Pi.allOn ⟨Multiset.cons a (Multiset.mk as), _⟩  _ _
      unfold Pi.allOn
      rw [Multiset.rec_cons]
      apply Finset.mem_flatMap_embed.mpr

      sorry

end Fintype
