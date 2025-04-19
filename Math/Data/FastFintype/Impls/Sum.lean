import Math.Data.FastFintype.Defs
import Math.Data.Fin.Pairing

instance {α β: Type*} [fα: Fintype α] [fβ: Fintype β] : Fintype (α ⊕ β) :=
  fα.bind fun fα =>
  fβ.map fun fβ =>
  {
    card := fα.card + fβ.card
    all := by
      apply Equiv.finSum.symm.toEmbedding.trans
      exact {
        toFun
        | .inl x => .inl (fα.all x)
        | .inr x => .inr (fβ.all x)
        inj' := by
          intro x y h
          cases x <;> cases y <;> dsimp at h
          simpa [Sum.inl.inj_iff, fα.all.inj.eq_iff] using h
          contradiction
          contradiction
          simpa [Sum.inr.inj_iff, fβ.all.inj.eq_iff] using h
      }
    complete x := by
      simp
      cases x <;> rename_i x
      have ⟨a, ha⟩ := fα.complete x
      exists a.castAdd _
      rw [Equiv.symm_apply_finSum]
      simpa
      have ⟨a, ha⟩ := fβ.complete x
      exists a.natAdd _
      rw [Equiv.symm_apply_finSum]
      simp; rw [dif_neg]
      simp
      rw [ha]; congr
      ext; simp
      omega
      omega
    decode :=
      fα.decode.bind fun deca =>
      fβ.decode.map fun decb x =>
      match x with
      | .inl x => Equiv.finSum (.inl (deca x))
      | .inr x => Equiv.finSum (.inr (decb x))
    decode_spec := by
      intro f hf i
      obtain ⟨cardα, fα, _, deca, deca_spec⟩ := fα
      obtain ⟨cardβ, fβ, _, decb, decb_spec⟩ := fβ
      simp; simp at i f hf
      cases deca with
      | none => contradiction
      | some deca =>
      cases decb with
      | none => contradiction
      | some decb =>
      cases hf
      rw [Equiv.symm_apply_finSum]
      simp; refine if hi:i.val < cardα then ?_ else ?_
      rw [dif_pos hi]; simp; rw [deca_spec deca rfl]; rfl
      rw [dif_neg hi]; simp; rw [decb_spec decb rfl]
      simp; congr; omega
  }
