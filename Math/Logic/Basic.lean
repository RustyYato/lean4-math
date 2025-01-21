def Iff.not_iff_not : (P ↔ Q) -> (¬P ↔ ¬Q) := by
  intro h
  apply Iff.intro
  intro np q
  exact np (h.mpr q)
  intro nq p
  exact nq (h.mp p)

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

def Option.get_inj (a b: Option α) (ha: a.isSome) (hb: b.isSome) :
  a.get ha = b.get hb -> a = b := by
  intro h
  have : some (a.get ha) = some (b.get hb) := by
    rw [h]
  rw [Option.some_get, Option.some_get] at this
  assumption
