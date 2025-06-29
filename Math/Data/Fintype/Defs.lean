import Math.Data.Trunc
import Math.Logic.Equiv.Basic
import Math.Data.Fin.Pairing
import Math.Data.List.Defs
import Math.AxiomBlame

structure Fintype.Repr (card: ℕ) (α: Type*) where
  decode : Fin card ⇔ α
  encode: Thunk (Option {
    f : α -> Fin card //
    Function.IsLeftInverse decode f
  })

class Fintype (α: Type*) where
  ofRepr ::
  card_thunk: Thunk ℕ
  toRepr : Trunc (Fintype.Repr card_thunk.get α)

namespace Fintype

attribute [local simp] Thunk.get

namespace Repr

def card_eq (a: Repr card₀ α) (b: Repr card₁ α) : card₀ = card₁ := by
  apply Fin.eq_of_common_bijection
  exact a.decode
  exact b.decode

private def findIdx {card: ℕ} (f: Fin card -> α) (a: α) [∀x, Decidable (a = x)] (h: ∃i, a = f i) : Σ'x: Fin card, a = f x :=
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

def toEmbed {card: ℕ} (f: Repr card α) : Fin card ↪ α where
  toFun := f.decode
  inj' := f.decode.inj

def toEquiv [DecidableEq α] {card: ℕ} (f: Repr card α) : Fin card ≃ α :=
  match f.encode.get with
  | .some g => {
    toFun := f.decode
    invFun := g.val
    rightInv := g.property
    leftInv := by
      intro x
      apply f.decode.inj
      rw [g.property]
  }
  | .none => {
    toFun := f.decode
    invFun a := (findIdx f.decode a (f.decode.surj a)).fst
    leftInv x := by
      apply f.decode.inj
      rw [←(findIdx f.decode (f.decode x) _).snd]
    rightInv x := by
      simp
      rw [←(findIdx f.decode x _).snd]
  }

def apply_toEmbed {card: ℕ} (f: Repr card α) : (f.toEmbed: Fin card -> α) = f.decode := rfl
def apply_toEquiv [DecidableEq α] {card: ℕ} (f: Repr card α) : (f.toEquiv: Fin card -> α) = f.decode := by
  unfold toEquiv
  split <;> rfl

end Repr

instance : Subsingleton (Fintype α) where
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

def card (α: Type*) [f: Fintype α] : ℕ := f.card_thunk.get

def toEmbed (α: Type*) [f: Fintype α] : Trunc (Fin (card α) ↪ α) :=
  f.toRepr.recOnSubsingleton fun repr => Trunc.mk repr.toEmbed

def toEquiv (α: Type*) [DecidableEq α] [f: Fintype α] : Trunc (Fin (card α) ≃ α) :=
  f.toRepr.recOnSubsingleton fun repr => Trunc.mk repr.toEquiv

def ofBij [f: Fintype α] (h: α ⇔ β) : Fintype β where
  card_thunk := card α
  toRepr := f.toRepr.recOnSubsingleton fun r => Trunc.mk <| {
    decode := r.decode.trans h
    encode := Thunk.mk fun () => .none
  }

-- def ofEquiv' [f: Fintype α] (h: α ≃ β) : Fintype β := ofBij h.toBijection
def ofEquiv [Fintype β] (h: α ≃ β) : Fintype α := ofBij h.symm.toBijection

instance : Fintype (Fin n) where
  card_thunk := n
  toRepr := Trunc.mk {
    decode := .rfl
    encode := Thunk.mk (fun _ => .some {
      val := id
      property _ := rfl
    })
  }

-- this is carefully written to ensure that no axioms are used
instance : Fintype Bool where
  card_thunk := Thunk.mk (fun _ => 2)
  toRepr :=
    let zero : Fin 2 := ⟨0, by decide⟩
    let one : Fin 2 := ⟨1, by decide⟩
    Trunc.mk (α := Repr 2 _) {
    decode := {
      toFun x := x.val != Fin.mk (n := 2) 0 (by decide)
      inj'
      | ⟨0, _⟩, ⟨0, _⟩, h
      | ⟨1, _⟩, ⟨1, _⟩, h => rfl
      | ⟨1, _⟩, ⟨0, _⟩, h
      | ⟨0, _⟩, ⟨1, _⟩, h => nomatch h
      | ⟨n + 2, _⟩, _, _ | _, ⟨n + 2, _⟩, _ => by
        rename n + 2 < 2 => h
        refine (Nat.not_le_of_lt h (Nat.le_add_left _ _)).elim
      surj' := by
        intro x
        cases x
        exact ⟨zero, rfl⟩
        exact ⟨one, rfl⟩
    }
    encode := Thunk.mk (fun _ => .some {
      val
      | false => zero
      | true => one
      property x := by cases x <;> rfl
    })
  }

instance : Fintype Prop := ofBij Bijection.bool_bij_prop

instance [fα: Fintype α] [fβ: Fintype β] : Fintype (α ⊕ β) where
  card_thunk := Thunk.mk (fun _ => card α + card β)
  toRepr :=
    fα.toRepr.bind fun rα =>
    fβ.toRepr.map fun rβ => {
      decode := {
        toFun x :=
          match Equiv.finSum.symm x with
          | .inl x => .inl (rα.decode x)
          | .inr x => .inr (rβ.decode x)
        inj' := by
          intro x y h
          simp at h
          split at h <;> split at h <;> rename_i h₀ _ _ h₁
          simp at h; cases rα.decode.inj h
          rwa [←h₁, Equiv.finSum.symm.inj.eq_iff] at h₀
          contradiction
          contradiction
          simp at h; cases rβ.decode.inj h
          rwa [←h₁, Equiv.finSum.symm.inj.eq_iff] at h₀
        surj' := by
          intro x
          cases x <;> rename_i x
          have ⟨y₀, h₀⟩ := rα.decode.surj x
          exists Equiv.finSum (.inl y₀)
          simp only [Equiv.coe_symm, h₀]
          have ⟨y₀, h₀⟩ := rβ.decode.surj x
          exists Equiv.finSum (.inr y₀)
          simp only [Equiv.coe_symm, h₀]
      }
      encode :=
        rα.encode.bind fun eα =>
        rβ.encode.map fun eβ =>
        eα.bind fun eα =>
        eβ.map fun eβ => {
          val
          | .inl x => Equiv.finSum (.inl (eα.val x))
          | .inr x => Equiv.finSum (.inr (eβ.val x))
          property := by
            intro x; cases x <;> simp only [Equiv.coe_symm, Bijection.apply_mk]
            erw [eα.property]
            erw [eβ.property]
        }
    }

instance [fα: Fintype α] [fβ: Fintype β] : Fintype (α × β) where
  card_thunk := Thunk.mk (fun _ => card α * card β)
  toRepr :=
    fα.toRepr.bind fun rα =>
    fβ.toRepr.map fun rβ => {
      decode := {
        toFun x :=
          have (x, y) := Equiv.finProd.symm x
          (rα.decode x, rβ.decode y)
        inj' := by
          intro x y h
          simp at h
          erw [rα.decode.inj.eq_iff, rβ.decode.inj.eq_iff] at h
          rw [←Fin.pair_split_eq_self x, ←Fin.pair_split_eq_self y, h.left, h.right]
        surj' := by
          intro x
          have ⟨y₀, h₀⟩ := rα.decode.surj x.1
          have ⟨y₁, h₁⟩ := rβ.decode.surj x.2
          exists Equiv.finProd (y₀, y₁)
          simp
          ext
          assumption
          assumption
      }
      encode :=
        rα.encode.bind fun eα =>
        rβ.encode.map fun eβ =>
        eα.bind fun eα =>
        eβ.map fun eβ => {
          val x :=
            have x₀ := eα.val x.1
            have x₁ := eβ.val x.2
            Equiv.finProd (x₀, x₁)
          property := by
            intro x
            simp [Equiv.finProd]
            erw [eα.property, eβ.property]
        }
    }

instance [Inhabited α] [Subsingleton α] : Fintype α where
  card_thunk := Thunk.mk fun _ => 1
  toRepr := Trunc.mk (α := Repr 1 _) {
    decode := {
      toFun _ := default
      inj' := by
        intro x y h
        apply Subsingleton.allEq
      surj' := by
        intro x
        exists 0
        apply Subsingleton.allEq
    }
    encode := Thunk.mk (fun _ => .some <| {
      val _ := 0
      property _ := Subsingleton.allEq  _ _
    })
  }

instance [IsEmpty α] : Fintype α where
  card_thunk := Thunk.mk fun _ => 0
  toRepr := Trunc.mk (α := Repr 0 _) {
    decode := {
      toFun := Fin.elim0
      inj' := by
        intro x y h
        apply Subsingleton.allEq
      surj' := by
        intro x
        exact elim_empty x
    }
    encode := Thunk.mk (fun _ => .some <| {
      val := elim_empty
      property _ := Subsingleton.allEq  _ _
    })
  }

@[simp]
def card_fin (n: ℕ) {f: Fintype (Fin n)} : card (Fin n) = n := by
  rw [Subsingleton.allEq f (instFin (n := n))]
  rfl

@[simp]
def card_bool {f: Fintype Bool} : card Bool = 2 := by
  rw [Subsingleton.allEq f instBool]
  rfl

@[simp]
def card_prop {f: Fintype Prop} : card Prop = 2 := by
  rw [Subsingleton.allEq f instProp]
  rfl

@[simp]
def card_sum' (α β: Type*) {f: Fintype α} {g: Fintype β} {h: Fintype (α ⊕ β)} : card (α ⊕ β) = card α + card β := by
  rw [Subsingleton.allEq h instSum]
  rfl

def card_sum (α β: Type*) [Fintype α] [Fintype β] {h: Fintype (α ⊕ β)} : card (α ⊕ β) = card α + card β := by
  apply card_sum'

@[simp]
def card_prod' (α β: Type*) {f: Fintype α} {g: Fintype β} {h: Fintype (α × β)} : card (α × β) = card α * card β := by
  rw [Subsingleton.allEq h instProd]
  rfl

def card_prod (α β: Type*) [Fintype α] [Fintype β] {h: Fintype (α × β)} : card (α × β) = card α * card β := by
  apply card_prod'

@[simp]
def card_unique (α: Type*) {f: Fintype α} [Inhabited α] [Subsingleton α] : card α = 1 := by
  rw [Subsingleton.allEq f instOfInhabitedOfSubsingleton]
  rfl

@[simp]
def card_empty (α: Type*) {f: Fintype α} [IsEmpty α] : card α = 0 := by
  rw [Subsingleton.allEq f instOfIsEmpty]
  rfl

instance (priority := 50) {P: ι -> Prop} [DecidablePred P] [f: Fintype ι] : Decidable (∃i, P i) :=
  f.toRepr.recOnSubsingleton fun f =>
  decidable_of_iff (∃(x: ℕ) (h: x < card ι), P (f.decode ⟨x, h⟩)) <| by
    apply Iff.intro
    intro ⟨x, hx, h⟩
    refine ⟨_, h⟩
    intro ⟨i, h⟩
    obtain ⟨i, rfl⟩ := f.decode.surj i
    exists i.val
    exists i.isLt

instance (priority := 50) {P: ι -> Prop} [DecidablePred P] [f: Fintype ι] : Decidable (∀i, P i) :=
  decidable_of_iff (¬∃i, ¬P i) Decidable.not_exists_not

def ind {motive: Fintype α -> Prop}
  (ind: ∀{card: ℕ} (r: Repr card α), motive (.ofRepr (Thunk.mk fun _ => card) (Trunc.mk r)))
  (f: Fintype α) : motive f := by
  obtain ⟨c, f⟩ := f
  induction f
  apply @ind c.get

private def axiomOfChoice_aux {α: Fin n -> Sort*} (f: ∀i, Nonempty (α i)) : Nonempty (∀i, α i) :=
  match n with
  | 0 => ⟨nofun⟩
  | _ + 1 =>
    have ⟨a⟩ := f 0
    have ⟨g⟩ := axiomOfChoice_aux (fun i => f i.succ)
    ⟨fun
      | 0 => a
      | ⟨i + 1, h⟩ => g ⟨i, Nat.lt_of_succ_lt_succ h⟩⟩

def Repr.axiomOfChoice {card ι} [DecidableEq ι] (r: Repr card ι) {α: ι -> Sort*} (f: ∀i, Nonempty (α i)) : Nonempty (∀i, α i) := by
  let eqv := r.toEquiv
  have ⟨f⟩ := axiomOfChoice_aux (fun i: Fin card => f (eqv i))
  exact ⟨fun i => cast (by simp) (f (eqv.symm i))⟩

def Repr.axiomOfChoice' {card ι} [DecidableEq ι] (r: Repr card ι) {α: ι -> Sort*} {P: ∀i: ι, α i -> Prop} (f: ∀i, ∃a: α i, P i a) : ∃f: ∀i:ι, α i, ∀i, P i (f i) := by
  have ⟨f⟩ := r.axiomOfChoice (ι := ι) (α := fun i => Σ'a: α i, P i a) ?_
  exists fun i => (f i).fst
  intro i
  apply (f i).snd
  intro i
  have ⟨a, pa⟩ := f i
  exists a

def axiomOfChoice [DecidableEq ι] [Fintype ι] {α: ι -> Sort*} (f: ∀i, Nonempty (α i)) : Nonempty (∀i, α i) := by
  induction toEquiv ι with | _ eqv =>
  have ⟨f⟩ := axiomOfChoice_aux (fun i: Fin (card ι) => f (eqv i))
  exact ⟨fun i => cast (by simp) (f (eqv.symm i))⟩

def axiomOfChoice' [DecidableEq ι] [Fintype ι] {α: ι -> Sort*} {P: ∀i: ι, α i -> Prop} (f: ∀i, ∃a: α i, P i a) : ∃f: ∀i:ι, α i, ∀i, P i (f i) := by
  have ⟨f⟩ := axiomOfChoice (ι := ι) (α := fun i => Σ'a: α i, P i a) ?_
  exists fun i => (f i).fst
  intro i
  apply (f i).snd
  intro i
  have ⟨a, pa⟩ := f i
  exists a

def card_eq_of_equiv' {fα: Fintype α} {fβ: Fintype β} (h: α ≃ β) : card α = card β := by
  rw [Subsingleton.allEq fα (ofEquiv h)]
  rfl

def card_eq_of_equiv [Fintype α] [Fintype β] (h: α ≃ β) : card α = card β := by
  apply card_eq_of_equiv' h

instance [Fintype α] : Fintype (Option α) := ofEquiv (Equiv.option_equiv_unit_sum α)

@[simp]
def card_option' {fα: Fintype α} {f: Fintype (Option α)} : card (Option α) = card α + 1 := by
  rw [Nat.add_comm, ←card_unique Unit, card_eq_of_equiv (Equiv.option_equiv_unit_sum α)]
  apply card_sum

def card_option [Fintype α] [Fintype (Option α)] : card (Option α) = card α + 1 := by
  apply card_option'

def trunc_of_card_ne_zero [f: Fintype α] (h: card α ≠ 0) : Trunc α :=
  f.toRepr.map fun r : Repr (card α) α => r.decode ⟨0, by omega⟩

def card_eq_zero_iff_empty [f: Fintype α] : card α = 0 ↔ IsEmpty α := by
  apply flip Iff.intro
  intro; rw [card_empty]
  intro h
  refine { elim x := ?_ }
  induction f with | _ card_thunk r =>
  induction r with | _ r =>
  replace h : card_thunk.get = 0 := h
  rw [h] at r
  nomatch r.decode.surj x

def card_ne_zero_iff_nonempty [f: Fintype α] : card α ≠ 0 ↔ Nonempty α := by
  apply Iff.intro
  · intro h
    induction trunc_of_card_ne_zero (α := α) h with | mk a =>
    exact ⟨a⟩
  · intro ⟨a⟩ g
    rw [card_eq_zero_iff_empty] at g
    exact elim_empty a

instance {α: ι -> Sort*} [f: Fintype ι] [∀i, DecidableEq (α i)]  : DecidableEq (∀i, α i) :=
  fun a b =>
  if h:∀i, a i = b i then
    .isTrue (funext h)
  else
    .isFalse <| fun g => h fun _ => g ▸ rfl

def Fineum.subsingleton [f: Fintype α] (h: card α ≤ 1) : Subsingleton α where
  allEq a b := by
    induction f using ind with | @ind card r =>
    have ⟨i, hi⟩ := r.decode.surj a
    have ⟨j, hj⟩ := r.decode.surj b
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
        have := i₀.isLt
        rw [hj] at this
        have := Nat.lt_irrefl _ this
        contradiction
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

def fold [fα: Fintype α] (f: α -> β -> β) (start: β) (h: ∀(a₀ a₁: α) (b: β), f a₀ (f a₁ b) = f a₁ (f a₀ b)) : β :=
  fα.toRepr.lift (fun rα : Repr (card α) α => Fin.foldr (card α) (fun a acc => f (rα.decode a) acc) start) <| by
    intro a b
    dsimp
    apply fold_spec (f := f)
    assumption
    intro x
    intro; apply b.decode.surj
    apply a.decode.inj
    apply b.decode.inj

private def cast_card (f: Fintype α) (h: n = card α) : Fintype α where
  card_thunk := n
  toRepr :=
    f.toRepr.map fun r => {
      decode := {
        toFun x := r.decode (x.cast h)
        inj' := by
          intro x y g
          simp at g; replace g := r.decode.inj g
          simpa [Fin.cast, Fin.val_inj] using g
        surj' := by
          intro x
          have ⟨i, g⟩ := r.decode.surj x
          exists i.cast h.symm
      }
      encode := Thunk.mk fun _ => .none
    }

def fold_empty [IsEmpty α] (f: α -> β -> β) (start: β) (h) : fold f start h = start := by rfl
def fold_option [Fintype α] (f: Option α -> β -> β) (start: β) (h) : fold f start h =
  f .none (fold (f ∘ Option.some) start (by intro x y z; apply h)) := by
  rename_i fα
  rw [Subsingleton.allEq (instOption (α := α)) (Fintype.cast_card (instOption (α := α)) (n := card α + 1) (by rw [card_option]))]
  induction fα using ind with | _ r =>
  rename_i card
  show Fin.foldr (card + 1) _ start = f _ (Fin.foldr _ _ _)
  rw [Fin.foldr_succ]
  rfl
def fold_eqv [Fintype α] [Fintype β] (f: β -> γ -> γ) (start: γ) (eqv: α ≃ β) (h) : fold f start h = fold (fun a => f (eqv a)) start (by
  intro a b start
  apply h) := by
  rename_i fα fβ
  rw [Subsingleton.allEq fβ (ofBij eqv.toBijection)]
  induction fα using ind with | _ r =>
  rfl

private instance (priority := 10) [f: Fintype (Option α)] : Fintype α where
  card_thunk := Thunk.mk fun _ => card (Option α) - 1
  toRepr := f.toRepr.map (β := Repr (card (Option α) - 1) _) fun r : Repr (card (Option α)) _ =>
    have : 0 < card (Option α) := by
      rw [Nat.pos_iff_ne_zero, card_ne_zero_iff_nonempty]
      exact ⟨.none⟩
    have (o: Option α) : Decidable (.none = o) := decidable_of_bool o.isNone <| by
      simp; apply Eq.comm
    have ⟨noneIdx, hnoneIdx⟩ := Repr.findIdx r.decode none (by
      apply r.decode.surj)
    let emb := Embedding.fin_erase (noneIdx.cast (by rw [Nat.sub_add_cancel]; omega))
    {
      encode := Thunk.mk fun _ => none
      decode := {
        toFun x :=
          Option.get (r.decode <| (Embedding.fin_erase (noneIdx.cast (by omega)) x).cast <| by omega) <| by
          rw [Option.isSome_iff_ne_none]
          rw [hnoneIdx]
          simp; rw [r.decode.inj.eq_iff, ←Fin.val_inj]
          simp
          show ¬(Embedding.fin_erase _) x = (noneIdx.cast (m := card (Option α) - 1 + 1) (by omega)).val
          rw [Fin.val_inj]
          apply Embedding.fin_erase_not_eq
        inj' := by
          intro x y h
          simp at h
          rw [Option.get_inj, r.decode.inj.eq_iff, ←Fin.val_inj] at h
          simp at h
          rwa [Fin.val_inj, (Embedding.inj _).eq_iff] at h
        surj' := by
          intro x
          have ⟨i, hi⟩ := r.decode.surj x
          simp
          refine if h:i.val <  noneIdx.val then ?_ else ?_
          exists ⟨i, by omega⟩
          apply Option.some.inj
          rw [hi]; simp; congr
          rw [←Fin.val_inj]
          simp
          rw [Embedding.apply_fin_erase_of_lt]
          rfl
          simpa
          simp at h
          have : noneIdx.val < i.val := by
            rcases Nat.lt_or_eq_of_le h with h | h
            assumption
            rw [Fin.val_inj] at h
            subst i
            rw [←hnoneIdx] at hi
            contradiction
          exists ⟨i - 1, ?_⟩
          omega
          apply Option.some.inj
          simp; rw [hi]
          congr; rw [←Fin.val_inj]
          simp
          rw [Embedding.apply_fin_erase_of_ge]
          simp; omega
          simp; omega
      }
    }

def indType'
  {motive: ∀α: Type u, Fintype α -> Prop}
  (empty: motive PEmpty inferInstance)
  (option: ∀(α: Type u) [Fintype α], motive α inferInstance -> motive (Option α) inferInstance)
  (eqv: ∀(α β: Type u) [Fintype α] [Fintype β], α ≃ β -> motive α inferInstance -> motive β inferInstance)
  {α: Type u} (f: Fintype α) [DecidableEq α]
  : motive α f := by
  induction h:card α generalizing α with
  | zero =>
    rw [card_eq_zero_iff_empty] at h
    apply eqv PEmpty
    apply Equiv.empty
    apply empty
  | succ n ih =>
    induction trunc_of_card_ne_zero (α := α) (by omega) with | mk x =>
    let instOpt := Fintype.ofEquiv (Equiv.erase x).symm
    apply eqv _ _ (Equiv.erase x).symm
    rw [Subsingleton.allEq instOpt instOption]
    apply option
    apply ih
    apply Nat.succ.inj
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
    rw [←card_option]
    rwa [card_eq_of_equiv (β := α)]
    symm; apply Equiv.erase

@[induction_eliminator]
def indType
  {motive: ∀α: Type u, Fintype α -> Prop}
  (empty: motive PEmpty inferInstance)
  (option: ∀(α: Type u) [Fintype α], motive α inferInstance -> motive (Option α) inferInstance)
  (eqv: ∀(α β: Type u) [Fintype α] [Fintype β], α ≃ β -> motive α inferInstance -> motive β inferInstance)
  {α: Type u} (f: Fintype α)
  : motive α f := by
  classical
  apply indType' <;> assumption

private def natMax [Fintype ι] (f: ι -> ℕ) : ℕ :=
  fold (fun i => max (f i)) 0 <| by
    intro i j b
    simp
    ac_rfl

private def le_natMax [fι: Fintype ι] (f: ι -> ℕ) : ∀i, f i ≤ natMax f := by
  induction fι with
  | empty => intro i; contradiction
  | option α ih =>
    intro o
    rw [Fintype.natMax]
    rw [fold_option]
    simp
    show _ ≤ max _ (natMax (f ∘ some))
    cases o with
    | none => apply Nat.le_max_left
    | some o =>
      apply flip Nat.le_trans
      apply Nat.le_max_right
      apply ih (f ∘ some)
  | eqv α β h ih =>
    intro i
    rw [Fintype.natMax, fold_eqv (eqv := h)]
    show f i ≤ natMax (f ∘ h)
    rw [←h.symm_coe i]
    apply ih (f ∘ h)

def nat_not_Fintype : Fintype Nat -> False := by
  intro
  let m := natMax id
  have : m + 1 ≤ m := le_natMax id (m + 1)
  omega

private def Repr.list_nodup_length_le (as bs: List α) (nodup: as.Nodup) (h: ∀x ∈ as, x ∈ bs) : as.length ≤ bs.length := by
  induction as generalizing bs with
  | nil => apply Nat.zero_le
  | cons a as ih =>
    have := h a (List.Mem.head _)
    rw [List.mem_iff_append] at this
    obtain ⟨s, t, rfl⟩ := this
    simp [←Nat.add_assoc]
    rw [←List.length_append]
    apply ih
    exact nodup.tail
    intro x hx
    replace h := h x (List.Mem.tail _ hx)
    simp at h; simp
    rcases h with h | rfl | h
    left; assumption
    have := nodup.head _ hx
    contradiction
    right; assumption

def card_le_of_embed' {fα: Fintype α} {fβ: Fintype β} (f: α ↪ β) : card α ≤ card β := by
  induction fα using ind with | @ind cα rα =>
  induction fβ using ind with | @ind cβ rβ =>
  let range := List.ofFn (n := cα) (f ∘ rα.decode)
  have range_nodup : range.Nodup := (List.nodup_ofFn _).mp (by
    apply Function.Injective.comp
    exact f.inj
    exact rα.decode.inj)
  have range_len : range.length = cα := by rw [List.length_ofFn]
  show cα ≤ cβ
  rw [←range_len]
  let all := List.ofFn rβ.decode
  have all_len : all.length = cβ := by rw [List.length_ofFn]
  rw [←all_len]
  apply Repr.list_nodup_length_le
  assumption
  intro x hx
  rw [List.mem_ofFn]
  have ⟨i, h⟩ := rβ.decode.surj x
  exists i; symm; assumption

def card_le_of_embed [Fintype α] [Fintype β] (h: α ↪ β) : card α ≤ card β := by
  apply card_le_of_embed' h

end Fintype
