import Math.Data.Fintype.Choice

namespace Fintype

private def fin_prod (f: Fin n -> ℕ) : ℕ :=
  Fin.foldr n (fun x acc => acc * f x) 1

@[simp]
private def fin_prod_zero (f: Fin 0 -> ℕ) : fin_prod f = 1 := rfl

@[simp]
private def fin_prod_succ (f: Fin (n + 1) -> ℕ) : fin_prod f = f 0 * fin_prod (f ∘ Fin.succ) := by
  rw [fin_prod, Fin.foldr_succ, Nat.mul_comm]
  rfl

private def fin_prod_eq_zero (f: Fin n -> ℕ) : fin_prod f = 0 ↔ ∃i, f i = 0 := by
  induction n with
  | zero => simp; nofun
  | succ n ih =>
    by_cases h:f 0 = 0
    simp [h]
    exists 0
    simp [Nat.mul_eq_zero, h, ih]
    apply Iff.intro
    intro ⟨i, h⟩
    exists i.succ
    intro ⟨i, h⟩
    cases i using Fin.cases
    contradiction
    rename_i i; exists i

private def fin_prod_to (f: Fin n -> ℕ) (x: Fin n) : ℕ :=
  fin_prod (fun i: Fin x.val => f (i.castLE (by omega)))

private def extract (f: Fin n -> ℕ) (data: Fin (fin_prod f)) (x: Fin n) : Fin (f x) where
  val := (data.val / fin_prod_to f x) % (f x)
  isLt := by
    apply Nat.mod_lt
    apply Nat.pos_iff_ne_zero.mpr
    intro g
    suffices fin_prod f = 0 by
      have pos := data.pos
      rw [this] at pos
      contradiction
    rw [(fin_prod_eq_zero _).mpr]
    exists x

private def extract_inj (f: Fin n -> ℕ) (x y: Fin (fin_prod f)) (h: ∀i, extract f x i = extract f y i) : x = y := by
  obtain ⟨x, xLt⟩ := x
  obtain ⟨y, yLt⟩ := y
  congr
  induction n generalizing x y with
  | zero => simp at xLt yLt; subst x; subst y; rfl
  | succ n ih =>
    simp at xLt yLt
    rw [←Nat.div_add_mod x (f 0), ←Nat.div_add_mod y (f 0)]
    congr 1
    · congr 1
      refine ih (f ∘ Fin.succ)  _ ?_ _ ?_ ?_
      · rwa [Nat.div_lt_iff_lt_mul, Nat.mul_comm]
        rw [Nat.pos_iff_ne_zero]
        rintro h
        rw [h] at xLt
        simp at xLt
      · rwa [Nat.div_lt_iff_lt_mul, Nat.mul_comm]
        rw [Nat.pos_iff_ne_zero]
        rintro h
        rw [h] at xLt
        simp at xLt
      · intro i
        have := h i.succ
        simp [Fintype.extract, Nat.div_div_eq_div_mul, fin_prod_to]
        simp [Fintype.extract, fin_prod_to] at this
        assumption
    · have := h 0
      simpa [Fintype.extract, Fintype.fin_prod_to] using this

private def encode (f: Fin n -> ℕ) (g: ∀i: Fin n, Fin (f i)) : ℕ :=
  match n with
  | 0 => 0
  | _ + 1 => (g 0).val + f 0 * encode (f ∘ Fin.succ) (fun i => g i.succ)

private def encode_lt (f: Fin n -> ℕ) (g: ∀i: Fin n, Fin (f i)) : encode f g < fin_prod f := by
  induction n with
  | zero => apply Nat.zero_lt_succ
  | succ n ih =>
    rw [Fintype.encode, fin_prod_succ]
    have := ih (f ∘ Fin.succ) (fun i => g i.succ)
    generalize hprd: fin_prod (f ∘ Fin.succ) = prd
    cases prd with
    | zero =>
      rw [fin_prod_eq_zero] at hprd
      obtain ⟨i, hi⟩ := hprd
      simp at hi
      have := (g i.succ).pos
      rw [hi] at this
      contradiction
    | succ prd =>
    rw [Nat.mul_succ, Nat.add_comm _ (f 0)]
    apply Nat.add_lt_add_of_lt_of_le
    apply Fin.isLt
    apply Nat.mul_le_mul_left
    rw [←Nat.lt_succ]
    simp [←hprd]
    apply ih

private def extract_encode (f: Fin n -> ℕ) (g: ∀i: Fin n, Fin (f i)) :
  extract f ⟨encode f g, encode_lt f g⟩ i = g i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simp [Fintype.extract, Fintype.encode, fin_prod_to]
      rw [←Fin.val_inj]
      simp
      rw [Nat.mod_eq_of_lt]
      simp
    | succ i =>
      simp [Fintype.extract, Fintype.encode, fin_prod_to]
      rw [←Fin.val_inj]
      simp
      rw [←Nat.div_div_eq_div_mul, Nat.add_mul_div_left, Nat.div_eq_of_lt (b := f 0)]
      simp
      replace ih := ih (fun i => f i.succ) (fun i => g i.succ) (i := i)
      rw [←Fin.val_inj] at ih
      assumption
      simp
      exact (g _).pos

instance instPi [DecidableEq ι] {α: ι -> Type*} [fι: Fintype ι] [fα: ∀i, Fintype (α i)] : Fintype (∀i, α i) :=
  fι.toRepr.recOnSubsingleton fun rι : Repr (card ι) ι =>
  (Quotient.finChoice (S := fun _ => Setoid.trueSetoid _) (fun i => (fα i).toRepr)).recOnSubsingleton fun rα : ∀i, Repr (card (α i)) (α i) =>
  let eqv := rι.toEquiv
  let get_card := (fun i => card (α (eqv i)))
  {
    card_thunk := Thunk.mk fun _ => fin_prod get_card
    toRepr := Trunc.mk (α := Repr (fin_prod get_card) _) {
        decode data i :=
          (rα _).decode <| (extract get_card data (eqv.symm i)).cast (by
            simp [get_card]; rw [Equiv.symm_coe])
        bij := by
          apply And.intro
          · intro x y
            simp
            intro h
            replace h := congrFun h
            conv at h => {
              intro i
              rw [(rα i).bij.Injective.eq_iff, ←Fin.val_inj]
            }
            simp [Fin.val_inj] at h
            exact extract_inj get_card x y (by
              intro i
              rw [←eqv.coe_symm i]
              apply h)
          · intro f
            simp
            have (i: ι) : ∃x, f i = (rα i).decode x := by
              apply (rα _).bij.Surjective
            replace this := rι.axiomOfChoice' this
            obtain ⟨g, hg⟩ := this
            exists ⟨encode get_card (fun i => g (eqv i)), encode_lt _ _⟩
            ext i
            rw [hg]
            congr
            rw [←Fin.val_inj]
            simp [extract_encode]
            congr; all_goals simp
        encode := .none
    }
  }

end Fintype
