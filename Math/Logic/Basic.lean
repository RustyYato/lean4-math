def Iff.not_iff_not : (P ↔ Q) -> (¬P ↔ ¬Q) := by
  intro h
  apply Iff.intro
  intro np q
  exact np (h.mpr q)
  intro nq p
  exact nq (h.mp p)

def Classical.not_iff_not : (P ↔ Q) ↔ (¬P ↔ ¬Q) := by
  apply Iff.intro
  apply Iff.not_iff_not
  intro h
  replace h := h.not_iff_not
  rwa [Classical.not_not, Classical.not_not] at h

def Iff.and (h: P ↔ Q) (g: S ↔ R) : (P ∧ S ↔ Q ∧ R) := by
  apply Iff.intro
  intro ⟨p, s⟩
  exact ⟨h.mp p, g.mp s⟩
  intro ⟨q, r⟩
  exact ⟨h.mpr q, g.mpr r⟩

def contrapositive {P Q: Prop} (f: P -> Q) : ¬Q -> ¬P := by
  intro nq p
  apply nq
  apply f
  assumption

def Classical.contrapositive {P Q: Prop}: (¬Q -> ¬P) ↔ (P -> Q) := by
  apply Iff.intro _ _root_.contrapositive
  intro h
  replace h := _root_.contrapositive h
  rwa [Classical.not_not, Classical.not_not] at h

def cast_eq_of_heq
  {a: α}
  {b: β}
  (h: HEq a b) : cast g a = b := by
  cases h
  rfl
