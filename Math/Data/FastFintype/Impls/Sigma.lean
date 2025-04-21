import Math.Data.FastFintype.Defs
import Math.Data.FastFintype.Choice
import Math.Data.Fin.Pairing

private def fin_sum (n: Nat) (f: Nat -> Nat) : Nat :=
match n with
| 0 => 0
| n + 1 => f n + fin_sum n f

def fin_sum_congr (n: Nat) (f g: Nat -> Nat) :
  (∀i, i < n -> f i = g i) -> fin_sum n f = fin_sum n g := by
  intro h
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold fin_sum; rw [h]
    rw [ih]
    intro i h'; apply h
    apply Nat.lt_trans h'
    apply Nat.lt_succ_self
    apply Nat.lt_succ_self

private def sigma_card {α: Fin n -> Type*} (fα: ∀i, Fintype.Encoding (α i)) : Nat :=
  fin_sum n (fun i => if h:i < n then (fα ⟨i, h⟩).card else 0)

def sigma_card_succ
   {α: Fin (n + 1) -> Type*} (fα: ∀i, Fintype.Encoding (α i)) :
   sigma_card fα = (fα ⟨n, Nat.lt_succ_self _⟩).card + sigma_card (fun i => fα i.castSucc) := by
   unfold sigma_card
   simp
   rw [fin_sum]
   rw [dif_pos]
   congr 1
   apply fin_sum_congr
   intro i h
   simp [h]
   rw [dif_pos]

private def sigma_all
  {α: Fin n -> Type*}
  (fα: ∀i, Fintype.Encoding (α i)) :
  Fin (sigma_card fα) ↪ Σ(i : Fin n), α i :=
  match n with
  | 0 => {
    inj' _ _ _ := Subsingleton.allEq (α := Fin 0) _ _
    toFun x := x.elim0
  }
  | n + 1 =>
    have sigma_all := sigma_all (fun i => fα i.castSucc)
    (Equiv.fin (m := (fα (Fin.last _)).card + sigma_card (fun i => fα i.castSucc)) (by
      rw [sigma_card_succ]; rfl)).trans Equiv.finSum.symm |>.toEmbedding.trans <| {
        toFun
        | .inl o => ⟨Fin.last _, ((fα _).all o)⟩
        | .inr o =>
          have := (sigma_all o)
          ⟨Fin.castSucc this.1, this.2⟩
        inj' := by
          classical
          intro f₀ f₁ eq
          dsimp at eq
          cases f₀ <;> cases f₁ <;> simp only at eq <;> rename_i eq
          simp [←(fα (Fin.last _)).equiv_fin_card_symm_eq] at eq
          rw [Equiv.inj _ eq]
          simp at eq
          have := eq.left
          rw [←Fin.val_inj] at this
          simp at this
          omega
          simp at eq
          have := eq.left
          rw [←Fin.val_inj] at this
          simp at this
          omega
          congr
          apply sigma_all.inj
          simp at eq
          ext
          have := Fin.val_inj.mpr eq.left
          simp at this
          assumption
          exact eq.right
      }

private instance
  (α: Fin n -> Type*) [fα: ∀i, Fintype (α i)]
  : Fintype (Σi, α i) :=
  (Fin.choice (fun i => (fα i).encode)).recOnSubsingleton fun fα =>
  Fintype.mk <| Quotient.mk _ {
    card := sigma_card fα
    all := sigma_all fα
    complete f := by
      rename_i h; clear h
      induction n with
      | zero => exact f.fst.elim0
      | succ n ih =>
        obtain ⟨x, f⟩ := f
        obtain ⟨i₀, hi₀⟩ := (fα _).complete f
        cases x using Fin.lastCases with
        | last =>
          cases hi₀
          refine ⟨(Equiv.finSum (m := sigma_card (fun i => fα i.castSucc)) (.inl i₀)).cast ?_, ?_⟩
          · rw [sigma_card_succ]; rfl
          · unfold sigma_all
            simp [Equiv.symm_apply_finSum]
        | cast x =>
          have ⟨f', f'_eq⟩ := ih (fun i => α i.castSucc) (fun i => fα i.castSucc) ⟨x, f⟩
          cases hi₀
          refine ⟨(Equiv.finSum (n := (fα (Fin.last n)).card) (m := sigma_card (fun i => fα i.castSucc)) (.inr f')).cast ?_, ?_⟩
          · rw [sigma_card_succ]; rfl
          · unfold sigma_all
            simp [Equiv.symm_apply_finSum]
            rw [dif_neg]
            simp
            have := Sigma.mk.inj f'_eq
            have eq :
              (fα (Fin.last n)).card + f'.val - (fα (Fin.last n)).card =
              f'.val := by omega
            apply And.intro
            rw (occs := [1]) [this.left]
            simp [eq]
            apply this.right.trans
            congr; symm; ext; assumption
            omega
  }

instance Fintype.sigma
  {ι: Type*} [fι: Fintype ι]
  (α: ι -> Type*) [fα: ∀i: ι, Fintype (α i)] : Fintype (Σi, α i) :=
  (Fintype.bij_fin_card ι).recOnSubsingleton fun eqv =>
  Fintype.ofBij (fun x: Σi: Fin (Fintype.card ι), α (eqv.val i) => ⟨eqv.val x.1, x.2⟩) <| by
    apply And.intro
    · intro x y h
      simp at h
      apply Sigma.ext
      exact eqv.property.left h.left
      exact h.right
    · intro x
      have ⟨i, eq⟩ := eqv.property.right x.1
      exists ⟨i, eq ▸ x.2⟩
      simp
      ext
      simp; assumption
      simp; symm
      exact eqRec_heq eq x.snd
