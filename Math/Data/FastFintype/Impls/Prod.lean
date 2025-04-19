import Math.Data.FastFintype.Defs
import Math.Data.Fin.Pairing

instance {α β: Type*} [fα: Fintype α] [fβ: Fintype β] : Fintype (α × β) :=
  fα.bind fun fα =>
  fβ.map fun fβ =>
  {
    card := fα.card * fβ.card
    all := by
      apply Equiv.finProd.symm.toEmbedding.trans
      exact {
        toFun x := (fα.all x.1, fβ.all x.2)
        inj' := by
          intro x y h
          simp [fα.all.inj.eq_iff, fβ.all.inj.eq_iff] at h
          apply Prod.ext h.1 h.2
      }
    complete x := by
      simp
      have ⟨a, ha⟩ := fα.complete x.1
      have ⟨b, hb⟩ := fβ.complete x.2
      exists a.pair b
      simp; ext <;> assumption
  }
