class LEM: Prop where
  em: ∀P: Prop, P ∨ ¬P

def em [LEM]: ∀P: Prop, P ∨ ¬P := LEM.em

namespace Classical

scoped instance : LEM where
  em := Classical.em

end Classical

section

variable [LEM]

def byCases (P: Prop) {Q: Prop} (h: P -> Q) (g: ¬P -> Q) : Q := by
  rcases em P with p | p
  exact h p
  exact g p

def byContradiction {P: Prop} (h: ¬P -> False) : P := by
  rcases em P with p | p
  exact p
  exact (h p).elim

def not_and_iff_not_or_not {P Q: Prop} : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  apply Iff.intro
  intro h
  rcases em P with p | np
  right; intro q
  exact h ⟨p, q⟩
  left; assumption
  intro h g
  rcases h with p | q
  exact p g.left
  exact q g.right

def not_or_iff_not_and_not {P Q: Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := not_or

def not_iff_not {P Q: Prop} : (P ↔ Q) ↔ (¬P ↔ ¬Q) := by
  apply Iff.intro
  · intro h
    apply Iff.intro
    intro np q
    exact np (h.mpr q)
    intro nq p
    exact nq (h.mp p)
  · intro h
    apply Iff.intro
    intro p
    apply byContradiction
    intro q
    exact h.mpr q p
    intro q
    apply byContradiction
    intro p
    exact h.mp p q

def not_forall {P: α -> Prop} : (¬∀x, P x) ↔ (∃x, ¬P x) := by
  apply Iff.intro
  intro h
  apply byContradiction
  intro g
  exact h fun x => byContradiction (not_exists.mp g x)
  intro ⟨x, hx⟩ g
  exact hx (g x)

instance LEM.instNonemptyDecidable : Nonempty (Decidable P) := by
  rcases em P with p | p
  exact ⟨.isTrue p⟩
  exact ⟨.isFalse p⟩

def or_iff_not_imp_left: ∀ {a b : Prop}, a ∨ b ↔ ¬a → b := by
  obtain h := inferInstanceAs (∀P, Nonempty (Decidable P))
  intro a b
  have ⟨_⟩ := h a
  have ⟨_⟩ := h b
  apply Decidable.or_iff_not_imp_left

def or_iff_not_imp_right: ∀ {a b : Prop}, a ∨ b ↔ ¬b → a := by
  obtain h := inferInstanceAs (∀P, Nonempty (Decidable P))
  intro a b
  have ⟨_⟩ := h a
  have ⟨_⟩ := h b
  apply Decidable.or_iff_not_imp_right

def em' (P: Prop) : ¬P ∨ P := Or.symm (em P)

def not_iff : ∀ {a b : Prop}, ¬(a ↔ b) ↔ (¬a ↔ b) := by
  intro A B
  have ⟨_⟩ := inferInstanceAs (Nonempty (Decidable A))
  have ⟨_⟩ := inferInstanceAs (Nonempty (Decidable B))
  apply Iff.intro
  intro h
  apply Iff.intro
  intro na
  apply byContradiction
  intro nb
  apply h
  apply not_iff_not.mpr
  apply Iff.intro <;> (intro; assumption)
  intro b a
  apply h
  apply Iff.intro <;> (intro; assumption)
  intro h g
  have := h.trans g.symm
  rcases em A with a | a
  exact this.mpr a a
  exact a (this.mp a)

def not_not {P: Prop} : ¬¬P ↔ P := by
  apply Iff.intro
  apply byContradiction
  intro p np
  exact np p

def forall_or_exists_not (P : α → Prop) : (∀a, P a) ∨ ∃a, ¬ P a := by
  apply or_iff_not_imp_left.mpr
  apply not_forall.mp

def exists_or_forall_not (P : α → Prop) : (∃a, P a) ∨ ∀a, ¬ P a := by
  apply or_iff_not_imp_left.mpr
  apply not_exists.mp

def not_exists_not {P: α -> Prop} : (¬∃a, ¬P a) ↔ ∀a, P a := by
  apply not_exists.trans
  apply Iff.intro
  intro h x
  apply not_not.mp
  apply h
  intro h x
  apply not_not.mpr
  apply h

def not_forall_not {P: α -> Prop} : (¬∀a, ¬P a) ↔ ∃a, P a := by
  apply not_forall.trans
  apply Iff.intro
  intro ⟨x, h⟩
  exists x
  apply not_not.mp
  apply h
  intro ⟨x, h⟩
  exists x
  apply not_not.mpr
  apply h

def not_imp_iff_and_not : ¬(P → Q) ↔ P ∧ ¬Q := by
  have ⟨_⟩ := inferInstanceAs (Nonempty (Decidable P))
  have ⟨_⟩ := inferInstanceAs (Nonempty (Decidable Q))
  apply Decidable.not_imp_iff_and_not

end
