import Math.Data.Cardinal.Order
import Math.Data.Cardinal.Algebra

import Math.Data.Set.Finite

open Classical

namespace Cardinal

def natCast_lt_ℵ₀ (n: ℕ) : n < ℵ₀ where
  left := by
    refine ⟨?_⟩
    apply Equiv.congrEmbed (Equiv.ulift _).symm .rfl _
    apply Equiv.congrEmbed Equiv.fin_equiv_nat_subtype.symm .rfl _
    apply Embedding.subtypeVal
  right := by
    intro ⟨h⟩
    replace h := Equiv.congrEmbed .rfl (Equiv.ulift _) h
    have := Equiv.antisymm h (Equiv.congrEmbed Equiv.fin_equiv_nat_subtype.symm .rfl Embedding.subtypeVal)
    have : Fintype ℕ := Fintype.ofEquiv this
    exact Fintype.nat_not_fintype this

private noncomputable def findDifferent
  (emb: Fin (n + 1) ↪ α)
  (f: Fin n -> α) (x: Nat) (h: x ≤ n)
  (g: ∀x, emb x ∈ Set.range f): α :=
  match x with
  | 0 => by
    exfalso
    have := Fintype.ofIsFinite (Set.range f)
    have := Fintype.ofIsFinite (Set.range emb)
    have : Fintype.card (Set.range f) ≤ n := by
      conv => { rhs; rw [←Fintype.card_fin n] }
      apply Fintype.card_le_of_embed
      refine ⟨?_, ?_⟩
      intro ⟨x, hx⟩
      exact Classical.choose hx
      intro ⟨x, hx⟩ ⟨y, hy⟩ eq
      dsimp at eq
      congr
      rw [Classical.choose_spec hx, Classical.choose_spec hy, eq]
    have : Fintype.card (Set.range emb) ≤ Fintype.card (Set.range f) := by
      apply Fintype.card_le_of_embed
      refine ⟨?_, ?_⟩
      intro ⟨x, hx⟩
      refine ⟨?_, ?_⟩
      assumption
      obtain ⟨i, eq⟩ := hx
      have := g i
      rw [←eq] at this
      assumption
      intro x y eq
      dsimp at eq
      cases x; cases y;cases eq
      rfl
    -- have := Fintype.card_embed

    sorry
  | x + 1 =>
    let a := emb ⟨x, by
      apply Nat.lt_of_succ_le
      apply Nat.le_trans h
      apply Nat.le_succ⟩
    if a  ∈ Set.range f then
      findDifferent emb f x sorry sorry
    else
      a

private noncomputable def toInfinite (embs: ∀n: ℕ, n ≤ #α) (n: ℕ) : α :=
  have : ∃a: α, ∀x (h: x < n), toInfinite embs x ≠ a := by
    have emb := Classical.choice (embs (n + 1))
    replace emb := Equiv.congrEmbed (Equiv.ulift _) .rfl emb
    let finv : Fin n -> α := fun x => toInfinite embs x.val

    sorry

  sorry
termination_by n
decreasing_by
  any_goals assumption
  apply Fin.isLt


def aleph0_le {c : Cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c := by
  cases c with | mk α =>
  apply Iff.intro
  intro ⟨h⟩ n
  have := h
  refine ⟨?_⟩
  apply Embedding.trans _ this
  apply Equiv.congrEmbed (Equiv.ulift _).symm .rfl _
  apply Equiv.congrEmbed Equiv.fin_equiv_nat_subtype.symm .rfl _
  apply Embedding.subtypeVal
  intro h
  refine ⟨?_⟩
  refine ⟨?_, ?_⟩
  intro n
  sorry
  sorry

def lt_ℵ₀ (c: Cardinal) : c < ℵ₀ ↔ ∃n: Nat, c = n := by
  apply flip Iff.intro
  rintro ⟨n, rfl⟩
  apply natCast_lt_ℵ₀
  cases c with | mk α =>
  intro ⟨⟨h⟩, g⟩
  replace g := g ∘ Nonempty.intro
  apply Classical.byContradiction
  intro notfin
  rw [not_exists] at notfin
  apply g
  refine ⟨?_, ?_⟩
  · have := fun n => (notfin n) ∘ Quotient.sound ∘ Nonempty.intro
    intro n
    sorry
  · sorry

end Cardinal
