def Iff.not_iff_not : (P ↔ Q) -> (¬P ↔ ¬Q) := by
  intro h
  apply Iff.intro
  intro np q
  exact np (h.mpr q)
  intro nq p
  exact nq (h.mp p)
