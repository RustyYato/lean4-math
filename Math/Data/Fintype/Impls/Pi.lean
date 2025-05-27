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

variable (ι: Type*) [DecidableEq ι]

private def detect_card_step (α: ι -> Type*) [fα: ∀i, Fintype (α i)] (i: ι) (acc: Bool ⊕ ℕ) : Bool ⊕ ℕ :=
    let c := card (α i)
    match acc with
    | .inl false => .inr c
    | .inl true => .inl true
    | .inr acc =>
      if acc = c then
        .inr acc
      else
        .inl true

private def detect_card (α: ι -> Type*) [fι: Fintype ι] [fα: ∀i, Fintype (α i)] :=
  Fintype.fold (α := ι) (β := Bool ⊕ Nat) (detect_card_step ι α) (.inl false) (by
        simp [detect_card_step]
        intro i j b
        match b with
        | .inl false =>
          simp [Eq.comm]
          split <;> rename_i h
          rw [h]
          rfl
        | .inl true => simp
        | .inr b =>
          simp
          by_cases h₀:b = card (α j) <;> simp [h₀]
          by_cases h₁:card (α j)= card (α i) <;> simp [h₁]
          by_cases h₁:b = card (α i) <;> simp [h₁]
          rw [if_neg]
          subst b; assumption)

private def detect_card_empty (α: ι -> Type*) [IsEmpty ι] [f: Fintype ι] [fα: ∀i, Fintype (α i)] :
  detect_card ι α = .inl false := by
  rw [detect_card, Subsingleton.allEq f]
  rw [fold_empty]

variable [fι: Fintype ι] [fι₀: Fintype ι₀] [fι₁: Fintype ι₁]

private def detect_card_option (α: Option ι -> Type*) [fα: ∀i, Fintype (α i)] :
  detect_card (Option ι) α = detect_card_step (Option ι) α .none (detect_card ι (fun i => α (some i))) := by
  rw [detect_card]
  rw [fold_option]
  rfl

private def detect_card_eqv (α: ι₁ -> Type*) (h: ι₀ ≃ ι₁) [fα: ∀i, Fintype (α i)] :
  detect_card ι₁ α = detect_card ι₀ (fun i => α (h i)) := by
  rw [detect_card]
  apply fold_eqv

private def detect_card_eq_inl_false {α: ι -> Type*} [fα: ∀i, Fintype (α i)] : detect_card ι α = .inl false -> IsEmpty ι := by
  intro h
  induction fι using indType' with
  | empty => infer_instance
  | option =>
    rw [detect_card_option] at h
    unfold detect_card_step at h
    simp at h
    split at h
    contradiction
    contradiction
    split at h
    contradiction
    contradiction
  | eqv ι₀ ι₁ eqv ih =>
    rw [detect_card_eqv _ eqv] at h
    have := ih h
    apply Function.isEmpty eqv.symm

private def detect_card_eq_inr_false {α: ι -> Type*} [fα: ∀i, Fintype (α i)] : detect_card ι α = .inr card' -> ∀i, card (α i) = card' := by
  intro hc i
  have : DecidableEq ι := inferInstance
  · induction fι using indType' generalizing card' with
    | empty => simp [detect_card_empty] at hc
    | option ι ih =>
      have := Embedding.DecidableEq (Embedding.optionSome (α := ι))
      simp [detect_card_option, detect_card_step] at hc
      split at hc
      · replace hc := Sum.inr.inj hc
        cases i
        assumption
        rename_i h₀ i
        have := detect_card_eq_inl_false _ h₀
        exact elim_empty i
      · contradiction
      · rename_i heq
        replace ih := ih (α := fun i => α (some i)) heq
        split at hc <;> rename_i h
        subst h
        cases i
        apply Sum.inr.inj
        assumption
        rw [ih]
        apply Sum.inr.inj
        apply_assumption
        infer_instance
        contradiction
    | eqv ι₀ ι₁ h ih =>
      have := Embedding.DecidableEq h.toEmbedding
      rw [detect_card_eqv _ h] at hc
      have := ih hc
      rw [←h.symm_coe i]
      apply this
      assumption

private def decode_function (h: n ≠ 0) (data: Fin (n ^ m)) (i: Fin m) : Fin n where
  val := (data.val / (n ^ i.val)) % n
  isLt := by
    apply Nat.mod_lt
    omega

private def encode_function (n: ℕ) (f: Fin m -> ℕ) : ℕ :=
  Fin.foldr m (fun i acc => acc + f i * n ^ i.val) 0

private def encode_function_zero (n: ℕ) (f: Fin 0 -> ℕ) : encode_function n f = 0 := rfl
private def encode_function_succ (n: ℕ) (f: Fin (m + 1) -> ℕ) : encode_function n f = encode_function n (f ∘ Fin.succ) * n + f 0 := by
  unfold encode_function
  rw [Fin.foldr_succ]
  show _ + _ * 1 = _
  simp
  simp [Nat.pow_succ]
  induction m with
  | zero => simp
  | succ m ih =>
    simp [Fin.foldr_succ]
    rw [Nat.add_mul]
    simp
    conv => {
      lhs; simp [Nat.pow_succ', Nat.mul_assoc]
      arg 2; intro i acc
      rw [←Nat.mul_assoc]
    }
    rw [ih (fun i => f i.succ * n)]
    congr; ext i acc
    rw [Nat.mul_assoc, Nat.pow_succ']
private def encode_function_lt (f: Fin m -> Fin n) : encode_function n (fun i => f i) < n ^ m := by
  induction m with
  | zero => simp [encode_function_zero]
  | succ m ih =>
    simp [encode_function_succ]
    apply Nat.lt_of_succ_le
    rw [←Nat.add_succ]
    simp
    rw [Nat.pow_succ]
    rw [←Nat.sub_add_cancel (n := n ^ m) (m := 1) (by
      apply Nat.succ_le_of_lt
      apply Nat.pow_pos
      exact (f 0).pos)]
    rw [Nat.succ_mul]
    apply Nat.add_le_add
    apply Nat.mul_le_mul
    · apply Nat.le_of_lt_succ
      apply Nat.lt_of_lt_of_eq
      apply ih
      simp
      rw [Nat.sub_add_cancel]
      apply Nat.succ_le_of_lt
      apply Nat.pow_pos
      exact (f 0).pos
    · apply Nat.le_refl
    · rw [Nat.succ_le]
      apply Fin.isLt

private def Nat.pow_pos_iff : ∀ {a n : ℕ}, 0 < a ^ n ↔ 0 < a ∨ n = 0 := by
  intro a b
  cases a with
  | zero =>
    cases b with
    | zero => simp
    | succ b =>
      rw [Nat.pow_succ, Nat.mul_zero]
      apply Iff.intro
      intro x; contradiction
      intro h
      cases h
      contradiction
      contradiction
  | succ a =>
    simp
    induction b with
    | zero => simp
    | succ n ih =>
      rw [Nat.pow_succ]
      apply Nat.mul_pos
      assumption
      apply Nat.zero_lt_succ

private def decode_function_add_succ (h: n ≠ 0) (data: Fin (n ^ m)) (data₀: Fin n) (i: Fin m) :
  decode_function h ⟨data.val * n + data₀, by
    match n with
    | n + 1 =>
    have : 0 < (n + 1) ^ m := by
      rw [Nat.pow_pos_iff]
      left; apply Nat.zero_lt_succ
    conv => { rhs; rw [Nat.pow_succ, ←Nat.sub_add_cancel (n := ((n + 1) ^ m)) (m := 1) (by omega)] }
    rw [Nat.succ_mul]
    apply Nat.add_lt_add_of_le_of_lt
    apply Nat.mul_le_mul
    apply Nat.le_of_lt_succ
    simp; omega
    apply Nat.le_refl
    apply Fin.isLt⟩ i.succ = decode_function h data i := by
    unfold decode_function
    simp
    rw [Nat.pow_succ', ←Nat.div_div_eq_div_mul, Nat.mul_comm _ n, Nat.mul_add_div,
      Nat.div_eq_of_lt data₀.isLt, Nat.add_zero]
    exact data₀.pos

private def decode_encode_function (h: n ≠ 0) (f: Fin m -> Fin n) (i: Fin m) : decode_function (n := n) (m := m) h ⟨encode_function n _, encode_function_lt f⟩ i = f i := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    cases i using Fin.cases with
    | zero =>
      simp [encode_function_succ, decode_function]
      rw [←Fin.val_inj]
      simp; rw [Nat.mod_eq_of_lt]
      apply Fin.isLt
    | succ m =>
      simp [encode_function_succ]
      rw [decode_function_add_succ (data := ⟨_, _⟩) (i := m)]
      rw [ih (fun i => f i.succ)]

instance instPi {α: ι -> Type*} [fα: ∀i, Fintype (α i)] : Fintype (∀i, α i) :=
  match hc:detect_card ι α with
  | .inl false =>
    have : IsEmpty ι := by
      apply detect_card_eq_inl_false _ hc
    have : Inhabited (∀i: ι, α i) := {
      default i := elim_empty i
    }
    inferInstance
  | .inr card_out =>
    -- all targets have the same cardinality, so this is likely a
    -- normal function, instead of a depenent funciton
    -- so we can use a more efficient implementation
    have cardα (i: ι) : card (α i) = card_out := by
      apply detect_card_eq_inr_false
      assumption
    fι.toRepr.recOnSubsingleton fun rι : Repr (card ι) ι =>
    (Quotient.finChoice (S := fun _ => Setoid.trueSetoid _) (fun i => (fα i).toRepr)).recOnSubsingleton fun rα : ∀i, Repr (card (α i)) (α i) =>
    have cardι_nz : card ι ≠ 0 := by
      intro h; rw [card_eq_zero_iff_empty] at h
      rw [detect_card_empty ι α] at hc
      contradiction
    {
      card_thunk := Thunk.mk fun _ => card_out ^ card ι
      toRepr := Trunc.mk (α := Repr (card_out ^ card ι) _) {
          decode data i :=
            (rα _).decode <| Fin.cast (cardα _).symm (
              decode_function (by
                    have := data.pos
                    rintro  rfl
                    rw [Nat.zero_pow] at this
                    contradiction
                    omega) data (rι.toEquiv.symm i))
          bij := by
            apply And.intro
            · intro x y h
              simp at h
              replace h := fun i =>
                propext Fin.val_inj ▸
                (propext (rα i).bij.Injective.eq_iff ▸ (congrFun h) i)
              simp at h
              replace h: ∀(i : Fin (card ι)), ↑x / card_out ^ i.val % card_out = ↑y / card_out ^ i.val % card_out := by
                intro i
                have := h (rι.toEquiv i)
                simpa using this
              revert h x y cardι_nz
              generalize card ι = cι
              clear rα rι cardα hc
              intro ne_zero x y h
              rw [←Fin.val_inj]
              clear ne_zero
              induction cι with
              | zero => rw [Subsingleton.allEq (α := Fin 1) x]
              | succ n ih =>
                rw [←Nat.div_add_mod x card_out, ←Nat.div_add_mod y card_out]
                congr 1; congr 1
                apply ih (x := ⟨x.val / card_out, ?_⟩) (y := ⟨y.val / card_out, ?_⟩)
                intro i
                simp
                rw [Nat.div_div_eq_div_mul ,Nat.div_div_eq_div_mul, ←Nat.pow_succ']
                apply h i.succ
                rw [Nat.div_lt_iff_lt_mul, ←Nat.pow_succ]
                apply x.isLt
                have := x.pos
                rw [Nat.pow_pos_iff] at this
                apply this.resolve_right
                omega
                rw [Nat.div_lt_iff_lt_mul, ←Nat.pow_succ]
                apply y.isLt
                have := x.pos
                rw [Nat.pow_pos_iff] at this
                apply this.resolve_right
                omega
                have := h 0
                simpa using this
            · intro f
              have (i: ι) : ∃x: Fin (card (α i)), f i = (rα i).decode x := by
                apply (rα _).bij.Surjective
              replace := axiomOfChoice' this
              obtain ⟨g, hg⟩ := this
              exists ⟨encode_function card_out (fun i => (g (rι.decode i)).cast (cardα _)), ?_⟩
              · apply encode_function_lt
              · ext i
                dsimp only
                rw [←rι.apply_toEquiv]
                conv => {
                  rhs; arg 1
                  rw [decode_encode_function (n := card_out) (by
                    have := (g i).pos
                    rw [cardα] at this
                    omega) (f := fun i => _)]
                }
                simp [Fin.cast]
                rw [hg]
                congr
                rw [←Fin.val_inj]
                simp
                rw [Equiv.symm_coe]
          encode := Thunk.mk fun _ => .none
      }
    }
  | .inl true =>
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
        encode := Thunk.mk fun _ => .none
    }
  }

instance instFunction {α: Type*} [fα: Fintype α] : Fintype (ι -> α) :=
  inferInstance

end Fintype
