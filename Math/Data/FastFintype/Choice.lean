import Math.Data.FastFintype.Defs
import Math.Data.Setoid.Basic

variable {ι : Type*} [fι: Fintype ι] [DecidableEq ι]

@[match_pattern]
private def finsucc (x: Fin n) : Fin (n + 1) := ⟨x.val + 1, by omega⟩

def Fin.choice {α : Fin n → Sort*} {S : ∀i, Setoid (α i)} (q: ∀i: Fin n, Quotient (S i)) :
  Quotient (Setoid.forallSetoid α) :=
  match n with
  | 0 => Quotient.mk _ <| fun i => i.elim0
  | n + 1 =>
    (Fin.choice (fun i => q i.succ)).liftOn₂ (q 0)
      (fun fs f0 =>
        Quotient.mk _ <| fun i =>
        match i with
        | 0 => f0
        | ⟨i + 1, hi⟩ => fs ⟨i, Nat.lt_of_succ_lt_succ hi⟩) <| by
      intro f₀ a₀ f₁ a₁ feq aeq
      simp
      apply Quotient.sound
      intro i
      cases i using Fin.cases
      assumption
      apply feq

variable {α : ι → Sort*} {S : ∀ i, Setoid (α i)} {β : Sort*}

-- private def cast_equiv (i j: ι) (h: i = j) (x y: α i) :
--   x ≈ y -> cast (β := α j) (by rw [h]) x ≈ cast (β := α j) (by rw [h]) y := by
--   cases h
--   exact id

-- private def cast_rw (i j k: ι) (h: i = k) (g: j = k) (x: α i) (y: α j) (eq: HEq x y) :
--   cast (by rw [h]) x = cast (by rw [g]) y := by
--   cases h; cases g; cases eq
--   rfl

-- private def wrap_finChoice
-- (aenc: Fin n ↪ ι)
-- (ainv: ι -> Fin n)
-- (ha: ∀i, aenc (ainv i) = i)
-- (respa)
-- (q : ∀i: ι, Quotient (S i)) :=
--   (Quotient.lift (fun f => Quotient.mk (Setoid.forallSetoid α) fun i => cast (by rw [ha]) (f (ainv i))) respa
--       (Fin.choice fun i => q (aenc i)))

-- def wrap_finChoice_eval
--   (aenc: Fin n ↪ ι)
--   (ainv: ι -> Fin n)
--   (ha: ∀i, aenc (ainv i) = i)
--   {respa}
--   (q : ∀i: ι, Quotient (S i)) :
--   Setoid.forallsetoid_eval (wrap_finChoice aenc ainv ha respa q) = q := by
--   induction n generalizing q with
--   | zero => ext i; exact (ainv i).elim0
--   | succ n ih =>
--     unfold wrap_finChoice Fin.choice
--     dsimp
--     sorry

-- private def finChoice_sound
--   (aenc benc: Fin n ↪ ι)
--   (ainv binv: ι -> Fin n)
--   (ha: ∀i, aenc (ainv i) = i)
--   (hb: ∀i, benc (binv i) = i)
--   {respa} {respb}
--   (q : ∀i: ι, Quotient (S i))
--   : Setoid.forallsetoid_eval (wrap_finChoice aenc ainv ha respa q) i =
--     Setoid.forallsetoid_eval (wrap_finChoice benc binv hb respb q) i := by
--     rw [wrap_finChoice_eval, wrap_finChoice_eval]

-- def finChoice (q : ∀i: ι, Quotient (S i)) :
--   Quotient (Setoid.forallSetoid α) := by
--   refine fι.hrec ι (motive := fun _ => _) ?_ ?_
--   · intro enc
--     apply (Fin.choice fun i => q (enc.all i)).lift
--       (fun f => Quotient.mk (Setoid.forallSetoid α) (fun i =>
--         cast (by simp [←Fintype.Encoding.equiv_fin_card_symm_eq]) (f (enc.equiv_fin_card i))))
--          <| by
--       intro a b h
--       apply Quotient.sound
--       intro i
--       have := h (enc.equiv_fin_card i)
--       simp
--       apply cast_equiv
--       simp [←Fintype.Encoding.equiv_fin_card_symm_eq]
--       assumption
--   · intro a b
--     simp
--     apply Setoid.forallsetoid_ext
--     intro i
--     have ⟨ainv, ainv_eq⟩ := Classical.axiomOfChoice a.complete
--     have ⟨binv, binv_eq⟩ := Classical.axiomOfChoice b.complete
--     have : a.equiv_fin_card = ainv := by
--       apply funext
--       intro i
--       have := ainv_eq i
--       apply a.equiv_fin_card.symm.inj
--       simp; rwa [a.equiv_fin_card_symm_eq]
--     conv => {
--       lhs; arg 1; arg 1; intro f
--       arg 2; intro i
--       rw [cast_rw _ (a.all (ainv i)) _ (by
--         simp [←a.equiv_fin_card_symm_eq]) (by
--         rw [←ainv_eq]) _ (f _) (by
--         rw [this])]
--     }
--     have : b.equiv_fin_card = binv := by
--       apply funext
--       intro i
--       have := binv_eq i
--       apply b.equiv_fin_card.symm.inj
--       simp; rwa [b.equiv_fin_card_symm_eq]
--     conv => {
--       rhs; arg 1; arg 1; intro f
--       arg 2; intro i
--       rw [cast_rw _ (b.all (binv i)) _ (by
--         simp [←b.equiv_fin_card_symm_eq]) (by
--         rw [←binv_eq]) _ (f _) (by
--         rw [this])]
--     }
--     have card_eq := a.card_eq b
--     obtain ⟨acard, aenc, asurj, adec, adec_spec⟩ := a
--     obtain ⟨bcard, benc, bsurj, bdec, bdec_spec⟩ := b
--     dsimp at ainv binv ainv_eq binv_eq card_eq
--     dsimp
--     subst bcard
--     apply finChoice_sound
--     intro i; symm; apply ainv_eq
--     intro i; symm; apply binv_eq
