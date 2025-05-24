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

end Finenum
