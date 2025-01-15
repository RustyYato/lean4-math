def Iff.not_iff_not : (P ↔ Q) -> (¬P ↔ ¬Q) := by
  intro h
  apply Iff.intro
  intro np q
  exact np (h.mpr q)
  intro nq p
  exact nq (h.mp p)

def contrapositive {P Q: Prop} (f: P -> Q) : ¬Q -> ¬P := by
  intro nq p
  apply nq
  apply f
  assumption
