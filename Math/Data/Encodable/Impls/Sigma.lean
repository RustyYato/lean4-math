import Math.Data.Encodable.Choice

instance {α: ι -> Type*} [eι: Encodable ι] [eα: ∀i, Encodable (α i)] : Encodable (Σi, α i) :=
  eι.toRepr.recOnSubsingleton fun eι =>
  (Quotient.countableChoice (S := fun _ => Setoid.trueSetoid _) (fun i => (eα i).toRepr)).recOnSubsingleton fun eα => {
    toRepr := Trunc.mk {
      encode x := Equiv.nat_equiv_nat_prod_nat.symm (eι x.1, eα _ x.2)
      decode x :=
        have x := Equiv.nat_equiv_nat_prod_nat x
        (eι.decode x.1).bind fun i => ((eα i).decode x.2).map fun a => ⟨i, a⟩
      encode_decode x := by simp
      spec n := by
        apply Iff.intro
        · intro h
          let x := Equiv.nat_equiv_nat_prod_nat n
          simp at h
          cases g₀:eι.decode x.fst
          simp [x, g₀] at h
          rename_i i
          cases g₁:(eα i).decode x.snd
          simp [x, g₀, g₁] at h
          clear h
          rename_i a
          exists ⟨i, a⟩
          simp [x, g₀, g₁]
          replace g₀ := eι.of_decode_eq_some _ _ g₀
          replace g₁ := (eα _).of_decode_eq_some _ _ g₁
          rw [g₀, g₁]
          show _ = Equiv.nat_equiv_nat_prod_nat.symm (Equiv.nat_equiv_nat_prod_nat _)
          simp
        · rintro ⟨⟨i, a⟩, rfl⟩
          simp
    }
  }
