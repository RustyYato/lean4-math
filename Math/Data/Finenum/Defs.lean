import Math.Data.Trunc
import Math.Logic.Equiv.Basic
import Math.Data.Fin.Pairing

class Finenum.Repr (card: ℕ) (α: Type*) where
  decode : Fin card -> α
  bij: Function.Bijective decode
  encode: Option {
    f : α -> Fin card //
    Function.IsLeftInverse decode f
  }

class Finenum (α: Type*) where
  ofRepr ::
  card_thunk: Thunk ℕ
  toRepr : Trunc (Finenum.Repr card_thunk.get α)

namespace Finenum

attribute [local simp] Thunk.get

namespace Repr

def card_eq (a: Repr card₀ α) (b: Repr card₁ α) : card₀ = card₁ := by
  have ⟨h₀, _⟩ := Equiv.ofBij a.bij
  have ⟨h₁, _⟩ := Equiv.ofBij b.bij
  exact Fin.eq_of_equiv (h₀.trans h₁.symm)

def findIdx [DecidableEq α] {card: ℕ} (f: Fin card -> α) (a: α) (h: ∃i, a = f i) : Σ'x: Fin card, a = f x :=
  match card with
  | 0 => False.elim <| nomatch h
  | card + 1 =>
    if g:a = f (Fin.last _) then
      ⟨_, g⟩
    else
      have ⟨x, hx⟩ := findIdx (f ∘ Fin.castSucc) a (by
        obtain ⟨i, hi⟩ := h
        cases i using Fin.lastCases
        contradiction
        rename_i i; exists i)
      ⟨_, hx⟩

def toEquiv [DecidableEq α] {card: ℕ} (f: Repr card α) : Fin card ≃ α :=
  match f.encode with
  | .some g => {
    toFun := f.decode
    invFun := g.val
    rightInv := g.property
    leftInv := by
      intro x
      apply f.bij.Injective
      rw [g.property]
  }
  | .none => {
    toFun := f.decode
    invFun a := (findIdx f.decode a (f.bij.Surjective a)).fst
    leftInv x := by
      apply f.bij.Injective
      rw [←(findIdx f.decode (f.decode x) _).snd]
    rightInv x := by
      simp
      rw [←(findIdx f.decode x _).snd]
  }

end Repr

instance : Subsingleton (Finenum α) where
  allEq a b := by
    cases a with | ofRepr card₀ ha =>
    cases b with | ofRepr card₁ hb =>
    induction ha with | mk ha =>
    induction hb with | mk hb =>
    congr 1
    ext
    apply ha.card_eq hb
    apply Subsingleton.helim
    congr
    ext
    apply ha.card_eq hb

def card (α: Type*) [f: Finenum α] : ℕ := f.card_thunk.get

def toEquiv (α: Type*) [DecidableEq α] [f: Finenum α] : Trunc (Fin (card α) ≃ α) :=
  f.toRepr.recOnSubsingleton fun repr => Trunc.mk repr.toEquiv

instance : Finenum (Fin n) where
  card_thunk := n
  toRepr := Trunc.mk {
    decode := id
    bij := by
      apply And.intro
      intro _ _
      apply id
      intro x; exists x
    encode := .some {
      val := id
      property _ := rfl
    }
  }

instance : Finenum Bool where
  card_thunk := Thunk.mk (fun _ => 2)
  toRepr := Trunc.mk (α := Repr 2 _) {
    decode x := x.val != 0
    bij := by
      apply And.intro
      decide
      intro x
      cases x
      exists 0
      exists 1
    encode := .some {
      val
      | false => 0
      | true => 1
      property x := by decide +revert
    }
  }

instance : Finenum Prop where
  card_thunk := Thunk.mk (fun _ => 2)
  toRepr := Trunc.mk (α := Repr 2 _) {
    decode x := x.val ≠ 0
    bij := by
      apply And.intro
      · intro x y h
        simp at h
        match x, y with
        | 0, 0 | 1, 1 => rfl
        | 0, 1 | 1, 0 => simp at h
      · intro x
        by_cases h:x
        exists 1
        simp [h]
        exists 0
        simp [h]
    encode := .none
  }

instance [fα: Finenum α] [fβ: Finenum β] : Finenum (α ⊕ β) where
  card_thunk := Thunk.mk (fun _ => card α + card β)
  toRepr :=
    fα.toRepr.bind fun rα =>
    fβ.toRepr.map fun rβ => {
      decode x :=
        match Equiv.finSum.symm x with
        | .inl x => .inl (rα.decode x)
        | .inr x => .inr (rβ.decode x)
      bij := by
        apply And.intro
        · intro x y h
          simp at h
          split at h <;> split at h <;> rename_i h₀ _ _ h₁
          simp [rα.bij.Injective.eq_iff] at h
          subst h
          rwa [←h₁, Equiv.finSum.symm.inj.eq_iff] at h₀
          contradiction
          contradiction
          simp [rβ.bij.Injective.eq_iff] at h
          subst h
          rwa [←h₁, Equiv.finSum.symm.inj.eq_iff] at h₀
        · intro x
          cases x <;> rename_i x
          have ⟨y₀, h₀⟩ := rα.bij.Surjective x
          exists Equiv.finSum (.inl y₀)
          simp only [Equiv.coe_symm, h₀]
          have ⟨y₀, h₀⟩ := rβ.bij.Surjective x
          exists Equiv.finSum (.inr y₀)
          simp only [Equiv.coe_symm, h₀]
      encode :=
        rα.encode.bind fun eα =>
        rβ.encode.map fun eβ => {
          val
          | .inl x => Equiv.finSum (.inl (eα.val x))
          | .inr x => Equiv.finSum (.inr (eβ.val x))
          property := by
            intro x; cases x <;> simp only [Equiv.coe_symm]
            rw [eα.property]
            rw [eβ.property]
        }
    }

instance [fα: Finenum α] [fβ: Finenum β] : Finenum (α × β) where
  card_thunk := Thunk.mk (fun _ => card α * card β)
  toRepr :=
    fα.toRepr.bind fun rα =>
    fβ.toRepr.map fun rβ => {
      decode x :=
        have (x, y) := Equiv.finProd.symm x
        (rα.decode x, rβ.decode y)
      bij := by
        apply And.intro
        · intro x y h
          simp at h
          rw [rα.bij.Injective.eq_iff, rβ.bij.Injective.eq_iff] at h
          rw [←Fin.pair_split_eq_self x, ←Fin.pair_split_eq_self y, h.left, h.right]
        · intro x
          have ⟨y₀, h₀⟩ := rα.bij.Surjective x.1
          have ⟨y₁, h₁⟩ := rβ.bij.Surjective x.2
          exists Equiv.finProd (y₀, y₁)
          simp
          ext
          assumption
          assumption
      encode :=
        rα.encode.bind fun eα =>
        rβ.encode.map fun eβ => {
          val x :=
            have x₀ := eα.val x.1
            have x₁ := eβ.val x.2
            Equiv.finProd (x₀, x₁)
          property := by
            intro x
            simp
            rw [eα.property, eβ.property]
        }
    }

instance [Inhabited α] [Subsingleton α] : Finenum α where
  card_thunk := Thunk.mk fun _ => 1
  toRepr := Trunc.mk (α := Repr 1 _) {
    decode _ := default
    bij := by
      apply And.intro
      intro x y h
      apply Subsingleton.allEq
      intro x
      exists 0
      apply Subsingleton.allEq
    encode := .some <| {
      val _ := 0
      property _ := Subsingleton.allEq  _ _
    }
  }

instance [IsEmpty α] : Finenum α where
  card_thunk := Thunk.mk fun _ => 0
  toRepr := Trunc.mk (α := Repr 0 _) {
    decode := Fin.elim0
    bij := by
      apply And.intro
      intro x y h
      apply Subsingleton.allEq
      intro x
      exact elim_empty x
    encode := .some <| {
      val := elim_empty
      property _ := Subsingleton.allEq  _ _
    }
  }

def card_fin (n: ℕ) {f: Finenum (Fin n)} : card (Fin n) = n := by
  rw [Subsingleton.allEq f (instFin (n := n))]
  rfl

def card_bool {f: Finenum Bool} : card Bool = 2 := by
  rw [Subsingleton.allEq f instBool]
  rfl

def card_prop {f: Finenum Prop} : card Prop = 2 := by
  rw [Subsingleton.allEq f instProp]
  rfl

def card_sum' (α β: Type*) {f: Finenum α} {g: Finenum β} {h: Finenum (α ⊕ β)} : card (α ⊕ β) = card α + card β := by
  rw [Subsingleton.allEq h instSum]
  rfl

def card_sum (α β: Type*) [Finenum α] [Finenum β] {h: Finenum (α ⊕ β)} : card (α ⊕ β) = card α + card β := by
  apply card_sum'

def card_prod' (α β: Type*) {f: Finenum α} {g: Finenum β} {h: Finenum (α × β)} : card (α × β) = card α * card β := by
  rw [Subsingleton.allEq h instProd]
  rfl

def card_prod (α β: Type*) [Finenum α] [Finenum β] {h: Finenum (α × β)} : card (α × β) = card α * card β := by
  apply card_prod'

def card_unique (α: Type*) {f: Finenum α} [Inhabited α] [Subsingleton α] : card α = 1 := by
  rw [Subsingleton.allEq f instOfInhabitedOfSubsingleton]
  rfl

def card_empty (α: Type*) {f: Finenum α} [IsEmpty α] : card α = 0 := by
  rw [Subsingleton.allEq f instOfIsEmpty]
  rfl

instance {P: ι -> Prop} [DecidablePred P] [f: Finenum ι] : Decidable (∃i, P i) :=
  f.toRepr.recOnSubsingleton fun f =>
  decidable_of_iff (∃(x: ℕ) (h: x < card ι), P (f.decode ⟨x, h⟩)) <| by
    apply Iff.intro
    intro ⟨x, hx, h⟩
    refine ⟨_, h⟩
    intro ⟨i, h⟩
    obtain ⟨i, rfl⟩ := f.bij.Surjective i
    exists i.val
    exists i.isLt

instance {P: ι -> Prop} [DecidablePred P] [f: Finenum ι] : Decidable (∀i, P i) :=
  decidable_of_iff (¬∃i, ¬P i) Decidable.not_exists_not

def ind {motive: Finenum α -> Prop}
  (ind: ∀{card: ℕ} (r: Repr card α), motive (.ofRepr (Thunk.mk fun _ => card) (Trunc.mk r)))
  (f: Finenum α) : motive f := by
  obtain ⟨c, f⟩ := f
  induction f
  apply @ind c.get

private def axiomOfChoice' {α: Fin n -> Sort*} (f: ∀i, Nonempty (α i)) : Nonempty (∀i, α i) :=
  match n with
  | 0 => ⟨nofun⟩
  | _ + 1 =>
    have ⟨a⟩ := f 0
    have ⟨g⟩ := axiomOfChoice' (fun i => f i.succ)
    ⟨fun
      | 0 => a
      | ⟨i + 1, h⟩ => g ⟨i, Nat.lt_of_succ_lt_succ h⟩⟩

def axiomOfChoice [DecidableEq ι] [Finenum ι] {α: ι -> Sort*} (f: ∀i, Nonempty (α i)) : Nonempty (∀i, α i) := by
  induction toEquiv ι with | _ eqv =>
  have ⟨f⟩ := axiomOfChoice' (fun i: Fin (card ι) => f (eqv i))
  exact ⟨fun i => cast (by simp) (f (eqv.symm i))⟩

def ofEquiv' [f: Finenum α] (h: α ≃ β) : Finenum β where
  card_thunk := card α
  toRepr := f.toRepr.recOnSubsingleton fun r => Trunc.mk <| {
    decode x := h (r.decode x)
    bij := by
      apply And.intro
      · apply Function.Injective.comp
        exact h.inj
        exact r.bij.Injective
      · intro b
        have ⟨i, h⟩ := r.bij.Surjective (h.symm b)
        exists i
        simp [←h]
    encode :=
      r.encode.map fun e =>  {
        val := e.val ∘ h.symm
        property := by
          intro x; simp
          rw [e.property, Equiv.symm_coe]
      }
  }
def ofEquiv [Finenum β] (h: α ≃ β) : Finenum α := ofEquiv' h.symm

def card_eq_of_equiv' {fα: Finenum α} {fβ: Finenum β} (h: α ≃ β) : card α = card β := by
  rw [Subsingleton.allEq fα (ofEquiv h)]
  rfl

def card_eq_of_equiv [Finenum α] [Finenum β] (h: α ≃ β) : card α = card β := by
  apply card_eq_of_equiv' h

instance [Finenum α] : Finenum (Option α) := ofEquiv (Equiv.option_equiv_unit_sum α)

def card_option' {fα: Finenum α} {f: Finenum (Option α)} : card (Option α) = card α + 1 := by
  rw [Nat.add_comm, ←card_unique Unit, card_eq_of_equiv (Equiv.option_equiv_unit_sum α)]
  apply card_sum

def card_option [Finenum α] [Finenum (Option α)] : card (Option α) = card α + 1 := by
  apply card_option'

def card_ne_zero_iff_nonempty [f: Finenum α] : card α ≠ 0 ↔ Nonempty α := by
  induction f with | _ card r =>
  show card.get ≠ 0 ↔ _
  revert r; generalize card.get = card
  rename_i c; clear c
  intro r
  induction r with | _ r =>
  cases card
  · simp; intro ⟨a⟩
    nomatch r.bij.Surjective a
  · simp
    exact ⟨r.decode 0⟩

def card_eq_zero_iff_empty [f: Finenum α] : card α = 0 ↔ IsEmpty α := by
  apply flip Iff.intro
  intro; rw [card_empty]
  intro h
  refine { elim x := ?_ }
  induction f with | _ card_thunk r =>
  induction r with | _ r =>
  replace h : card_thunk.get = 0 := h
  rw [h] at r
  nomatch r.bij.Surjective x

def Fintype.subsingleton [f: Finenum α] (h: card α ≤ 1) : Subsingleton α where
  allEq a b := by
    induction f using ind with | @ind card r =>
    have ⟨i, hi⟩ := r.bij.Surjective a
    have ⟨j, hj⟩ := r.bij.Surjective b
    rw [hi, hj]
    congr
    have := i.pos
    replace h : card ≤ 1 := h
    replace h : card = 1 := by omega
    subst card
    apply Subsingleton.allEq

private def pull_fold_spec
  (f: α -> β -> β)
  (dec: Fin (n + 1) -> α)
  (h: ∀(a₀ a₁: α) (b: β), f a₀ (f a₁ b) = f a₁ (f a₀ b))
  (i: Fin (n + 1)) :
  Fin.foldr (n + 1) (fun a => f (dec a)) start = (Fin.foldr n (fun a => f (dec (Embedding.fin_erase i a))) (f (dec i) start)) := by
  induction n generalizing start with
  | zero =>
    simp [Fin.foldr_succ]
    congr; apply Subsingleton.allEq (α := Fin 1)
  | succ n ih =>
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.foldr_succ_last]
      simp [Embedding.apply_fin_erase_of_lt]
    | cast i =>
      rw [Fin.foldr_succ_last, ih (fun i => dec i.castSucc) i]
      rw [Fin.foldr_succ_last]
      congr 1
      · ext j b
        refine if h:j.val < i.val then ?_ else ?_
        rw [Embedding.apply_fin_erase_of_lt _ _ h, Embedding.apply_fin_erase_of_lt i.castSucc _ h]
        simp at h
        rw [Embedding.apply_fin_erase_of_ge _ _ h, Embedding.apply_fin_erase_of_ge i.castSucc j.castSucc h]
        rfl
      · rw [h, Embedding.apply_fin_erase_of_ge]; rfl
        simp
        omega

private def fold_spec
  (f: α -> β -> β)
  (dec₀ dec₁: Fin n -> α)
  (h₀: ∀(a₀ a₁: α) (b: β), f a₀ (f a₁ b) = f a₁ (f a₀ b))
  (h₁: ∀x: α, (∃i, x = dec₀ i) -> (∃i, x = dec₁ i))
  (h₂: Function.Injective dec₀)
  (h₃: Function.Injective dec₁) :
  Fin.foldr n (fun a => f (dec₀ a)) start = Fin.foldr n (fun a => f (dec₁ a)) start := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    have ⟨i, hi⟩ := (h₁ (dec₀ (Fin.last _))) ⟨_, rfl⟩
    rw [Fin.foldr_succ_last, pull_fold_spec f dec₁ h₀ i, ←hi]
    apply ih
    · rintro a ⟨i₀, rfl⟩
      have ⟨j, hj⟩ := h₁ (dec₀ i₀.castSucc) ⟨_, rfl⟩
      rw [hj]
      rcases Nat.lt_trichotomy i j with h | h | h
      · exists ⟨j.val - 1, ?_⟩
        omega
        rw [Embedding.apply_fin_erase_of_ge]
        congr; simp [←Fin.val_inj]
        omega
        simp; omega
      · rw [Fin.val_inj] at h
        subst j
        rw [←hi, h₂.eq_iff, ←Fin.val_inj] at hj
        simp at hj
        omega
      · exists ⟨j, ?_⟩
        omega
        rw [Embedding.apply_fin_erase_of_lt]
        simp
        assumption
    · apply Function.Injective.comp
      assumption
      intro _ _
      apply Fin.castSucc_inj.mp
    · apply Function.Injective.comp
      assumption
      apply Embedding.inj

def fold [fα: Finenum α] (f: α -> β -> β) (start: β) (h: ∀(a₀ a₁: α) (b: β), f a₀ (f a₁ b) = f a₁ (f a₀ b)) : β :=
  fα.toRepr.lift (fun rα : Repr (card α) α => Fin.foldr (card α) (fun a acc => f (rα.decode a) acc) start) <| by
    intro a b
    dsimp
    apply fold_spec (f := f)
    assumption
    intro x
    intro; apply b.bij.Surjective
    apply a.bij.Injective
    apply b.bij.Injective

end Finenum
