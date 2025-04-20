import Math.Data.FastFintype.Defs
import Math.Data.FastFintype.Choice
import Math.Data.Fin.Pairing

private def fin_prod (n: Nat) (f: Nat -> Nat) : Nat :=
match n with
| 0 => 1
| n + 1 => f n * fin_prod n f

def fin_prod_congr (n: Nat) (f g: Nat -> Nat) :
  (∀i, i < n -> f i = g i) -> fin_prod n f = fin_prod n g := by
  intro h
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold fin_prod; rw [h]
    rw [ih]
    intro i h'; apply h
    apply Nat.lt_trans h'
    apply Nat.lt_succ_self
    apply Nat.lt_succ_self

private def pi_card {α: Fin n -> Type*} (fα: ∀i, Fintype.Encoding (α i)) : Nat :=
  fin_prod n (fun i => if h:i < n then (fα ⟨i, h⟩).card else 0)

def pi_card_succ
   {α: Fin (n + 1) -> Type*} (fα: ∀i, Fintype.Encoding (α i)) :
   pi_card fα = (fα ⟨n, Nat.lt_succ_self _⟩).card * pi_card (fun i => fα i.castSucc) := by
   unfold pi_card
   simp
   rw [fin_prod]
   rw [dif_pos]
   congr 1
   apply fin_prod_congr
   intro i h
   simp [h]
   rw [dif_pos]

private def pi_all
  {α: Fin n -> Type*}
  (fα: ∀i, Fintype.Encoding (α i)) :
  Fin (pi_card fα) ↪ (i : Fin n) → α i :=
  match n with
  | 0 => {
    inj' _ _ _ := Subsingleton.allEq (α := Fin 1) _ _
    toFun _ x := x.elim0
  }
  | n + 1 =>
    have pi_all := pi_all (fun i => fα i.castSucc)
    (Equiv.fin (m := (fα (Fin.last _)).card * pi_card (fun i => fα i.castSucc)) (by
      rw [pi_card_succ]; rfl)).trans Equiv.finProd.symm |>.toEmbedding.trans <| {
        toFun o x :=
          if h:x.val = n then
            cast (by
              congr; ext; symm
              assumption) ((fα _).all o.1)
          else
            pi_all o.2 ⟨x.val, by omega⟩
        inj' := by
          classical
          intro f₀ f₁ eq
          dsimp at eq
          replace eq := congrFun eq
          have fst_eq := eq (Fin.last _)
          simp [←(fα (Fin.last _)).equiv_fin_card_symm_eq] at fst_eq
          replace fst_eq := Equiv.inj _ fst_eq
          apply Prod.ext
          assumption
          apply pi_all.inj
          ext i
          have := eq i.castSucc
          simp at this
          rwa [dif_neg, dif_neg] at this
          omega
          omega
      }

private instance
  (α: Fin n -> Type*) [fα: ∀i, Fintype (α i)]
  : Fintype (∀i, α i) :=
  (Fin.choice (fun i => (fα i).encode)).recOnSubsingleton fun fα =>
  Fintype.mk <| Quotient.mk _ {
    card := pi_card fα
    all := pi_all fα
    complete f := by
      rename_i h; clear h
      induction n with
      | zero =>
        exists ⟨0, Nat.zero_lt_succ _⟩
        ext i; exact i.elim0
      | succ n ih =>
        have ⟨f', f'_eq⟩ := ih (fun i => α i.castSucc) (fun i => fα i.castSucc)
          (fun i => f i.castSucc)
        let a₀ := f (Fin.last _)
        have ⟨i₀, eq⟩ := (fα (Fin.last _)).complete a₀
        refine ⟨(Equiv.finProd (i₀, f')).cast ?_, ?_⟩
        · rw [pi_card_succ]; rfl
        · ext i
          unfold pi_all
          cases i using Fin.lastCases with
          | last =>
            simp
            assumption
          | cast i =>
            simp
            rw [dif_neg]
            apply congrFun f'_eq
            omega
  }

instance Fintype.pi
  {ι: Type*} [DecidableEq ι] [fι: Fintype ι]
  (α: ι -> Type*) [fα: ∀i: ι, Fintype (α i)]
  : Fintype (∀i, α i) :=
  (Fintype.equiv_fin_card ι).recOnSubsingleton fun eqv =>
  Fintype.ofEquiv (Equiv.congrPi
    (β₁ := fun i: Fin (Fintype.card ι) => (α (eqv.symm i)))
    eqv (fun i => by simp; rfl))

instance Fintype.function
  {ι α: Type*} [DecidableEq ι] [fι: Fintype ι] [fα:Fintype α]
  : Fintype (ι -> α) :=
  inferInstance
