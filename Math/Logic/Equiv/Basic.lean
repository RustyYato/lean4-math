import Math.Logic.Equiv.Defs
import Math.Logic.Basic
import Math.Logic.IsEmpty
import Math.Logic.Nontrivial

namespace Embedding

def optionSome {α: Type*} : α ↪ Option α where
  toFun := .some
  inj' _ _ := Option.some.inj

def subtypeVal {P: α -> Prop} : Subtype P ↪ α where
  toFun := Subtype.val
  inj' a b eq := by
    cases a; cases b; congr

def DecidableEq (emb: α ↪ β) [DecidableEq β] : DecidableEq α :=
  fun a b =>
  match inferInstanceAs (Decidable (emb a = emb b)) with
  | .isTrue h => .isTrue (emb.inj h)
  | .isFalse h => .isFalse fun g => h (g ▸ _root_.rfl)

def empty [IsEmpty α] : α ↪ β where
  toFun := elim_empty
  inj' x := elim_empty x

def of_option_embed_option (emb: Option α ↪ Option β) : α ↪ β where
  toFun a :=
    match h:emb a with
    | .some x => x
    | .none => (emb .none).get <| by
      cases g:emb .none
      have := emb.inj (h.trans g.symm)
      contradiction
      rfl
  inj' := by
    intro x y eq
    dsimp at eq
    split at eq <;> split at eq
    rename_i h₀ _ h₁
    subst eq
    exact Option.some.inj <| emb.inj (h₀.trans h₁.symm)
    subst eq
    rename_i h₀ h₁
    rw [Option.some_get] at h₁
    have := emb.inj h₁; contradiction
    rename_i h₀ eq h₁; subst eq
    rw [Option.some_get] at h₁
    have := emb.inj h₁; contradiction
    rename_i h₀ h₁
    exact Option.some.inj <| emb.inj (h₀.trans h₁.symm)

private def cantorProp (α: Sort*) : ((α -> Prop) ↪ α) -> False := by
  intro h
  let cantorFun (x: α) : Prop := ∃f: α -> Prop, h f = x ∧ ¬f x
  let P := cantorFun (h cantorFun)
  by_cases p:P
  have ⟨f, eq, spec⟩  := p
  cases h.inj eq
  contradiction
  apply p
  exists cantorFun

-- it's not possible to embed functions from α to some non-trivial type into α
def cantor (α β: Sort*) [h: IsNontrivial β] : ((α -> β) ↪ α) -> False := by
  classical
  obtain ⟨b₀, b₁, h⟩ := h
  intro g
  apply Embedding.cantorProp α
  refine ⟨?_, ?_⟩
  intro f
  refine g ?_
  intro x
  exact if f x then b₀ else b₁
  intro x y eq
  dsimp at eq
  ext a
  have := congrFun (g.inj eq) a
  split at this <;> split at this
  rename_i hx hy
  exact (iff_true_right hy).mpr hx
  contradiction
  have := this.symm
  contradiction
  rename_i hx hy
  exact (iff_false_right hy).mpr hx

end Embedding

namespace Equiv

def congrEquiv {α₀ α₁ β₀ β₁} (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ≃ β₀) ≃ (α₁ ≃ β₁) where
  toFun f := h.symm.trans (f.trans g)
  invFun f := h.trans (f.trans g.symm)
  leftInv := by
    intro f
    dsimp only
    rw [trans_assoc, trans_assoc, trans_symm,
      ←trans_assoc, trans_symm]
    rfl
  rightInv := by
    intro f
    dsimp only
    rw [trans_assoc, trans_assoc, symm_trans,
      ←trans_assoc, symm_trans]
    rfl

@[simp]
def congrEquiv' {α₀ α₁ β₀ β₁} (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ≃ β₀) -> (α₁ ≃ β₁) :=
  congrEquiv h g

@[simp]
def apply_congrEquiv (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) (x: α₀ ≃ β₀) :
  congrEquiv h g x = h.symm.trans (x.trans g) := by rfl
def symm_congrEquiv (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) :
  (congrEquiv h g).symm = congrEquiv h.symm g.symm := by rfl

def ulift (α: Type*) : ULift α ≃ α where
  toFun := ULift.down
  invFun := ULift.up
  leftInv _ := by rfl
  rightInv _ := by rfl

def plift (α: Sort*) : PLift α ≃ α where
  toFun := PLift.down
  invFun := PLift.up
  leftInv _ := by rfl
  rightInv _ := by rfl

def liftULift : (α ≃ β) ≃ (ULift α ≃ ULift β) :=
  (congrEquiv (ulift α) (ulift β)).symm

def liftPLift : (α ≃ β) ≃ (PLift α ≃ PLift β) :=
  (congrEquiv (plift α) (plift β)).symm

def congrULift {α β: Type*} (h: α ≃ β) : ULift α ≃ ULift β :=
  liftULift h

def congrPLift {α β: Sort*} (h: α ≃ β) : PLift α ≃ PLift β :=
  liftPLift h

def prod_equiv_pprod (α β: Type*) : α × β ≃ α ×' β where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv _ := by rfl
  rightInv _ := by rfl

def liftProd : ((α₀ ×' β₀) ≃ (α₁ ×' β₁)) ≃ ((α₀ × β₀) ≃ (α₁ × β₁)) :=
  (congrEquiv (prod_equiv_pprod _ _) (prod_equiv_pprod _ _)).symm

def prod_equiv_sigma (α β: Type*) : α × β ≃ Σ_: α, β where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv _ := by rfl
  rightInv _ := by rfl

def congrPProd {α₀ α₁ β₀ β₁: Sort*} (a: α₀ ≃ α₁) (b: β₀ ≃ β₁) : α₀ ×' β₀ ≃ α₁ ×' β₁ where
  toFun x := ⟨a x.1, b x.2⟩
  invFun x := ⟨a.symm x.1, b.symm x.2⟩
  leftInv x := by
    cases x; dsimp; congr
    rw [coe_symm]
    rw [coe_symm]
  rightInv x := by
    cases x; dsimp; congr
    rw [symm_coe]
    rw [symm_coe]

def congrProd {α₀ α₁ β₀ β₁: Type*} (a: α₀ ≃ α₁) (b: β₀ ≃ β₁) : α₀ × β₀ ≃ α₁ × β₁ :=
  liftProd (congrPProd a b)

def commPProd (α β: Sort*) : α ×' β ≃ β ×' α where
  toFun x := ⟨x.2, x.1⟩
  invFun x := ⟨x.2, x.1⟩
  leftInv x := by rfl
  rightInv x := by rfl

def commProd (α β: Type*) : α × β ≃ β × α :=
  liftProd (commPProd _ _)

def congrOption {α β: Type*} (h: α ≃ β) : Option α ≃ Option β where
  toFun
  | .some x => .some (h x)
  | .none => .none
  invFun
  | .some x => .some (h.symm x)
  | .none => .none
  leftInv x := by
    cases x
    rfl
    dsimp
    rw [coe_symm]
  rightInv x := by
    cases x
    rfl
    dsimp
    rw [symm_coe]

def sum_equiv_psum (α β: Type*) : α ⊕ β ≃ α ⊕' β where
  toFun
  | .inl x => .inl x
  | .inr x => .inr x
  invFun
  | .inl x => .inl x
  | .inr x => .inr x
  leftInv x := by cases x <;> rfl
  rightInv x := by cases x <;> rfl

def congrPSum {α₀ α₁ β₀ β₁: Sort*} (a: α₀ ≃ α₁) (b: β₀ ≃ β₁) : α₀ ⊕' β₀ ≃ α₁ ⊕' β₁ where
  toFun
  | .inl x => .inl (a x)
  | .inr x => .inr (b x)
  invFun
  | .inl x => .inl (a.symm x)
  | .inr x => .inr (b.symm x)
  leftInv x := by
    cases x <;> dsimp
    rw [coe_symm]
    rw [coe_symm]
  rightInv x := by
    cases x <;> dsimp
    rw [symm_coe]
    rw [symm_coe]

def liftSum {α₀ α₁ β₀ β₁: Type*} : (α₀ ⊕' β₀ ≃ α₁ ⊕' β₁) ≃ (α₀ ⊕ β₀ ≃ α₁ ⊕ β₁) :=
  (congrEquiv (sum_equiv_psum _ _) (sum_equiv_psum _ _)).symm

def congrSum {α₀ α₁ β₀ β₁: Type*} (a: α₀ ≃ α₁) (b: β₀ ≃ β₁) : α₀ ⊕ β₀ ≃ α₁ ⊕ β₁ :=
  liftSum (congrPSum a b)

def commPSum (α β: Sort*) : α ⊕' β ≃ β ⊕' α where
  toFun
  | .inl x => .inr x
  | .inr x => .inl x
  invFun
  | .inl x => .inr x
  | .inr x => .inl x
  leftInv x := by cases x <;> rfl
  rightInv x := by cases x <;> rfl

def commSum (α β: Type*) : α ⊕ β ≃ β ⊕ α := liftSum (commPSum _ _)

def sigma_equiv_psigma {α: Type*} (β: α -> Type*) : (Σa: α, β a) ≃ (Σ'a: α, β a) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv x := by rfl
  rightInv x := by rfl

def congrPSigma {α₀ α₁: Sort*} {β₀: α₀ -> Sort*} {β₁: α₁ -> Sort*} (h: α₀ ≃ α₁) (g: ∀a: α₀, β₀ a ≃ β₁ (h a)) : (Σ'a: α₀, β₀ a) ≃ (Σ'a: α₁, β₁ a) where
  toFun x := ⟨h x.1, g _ x.2⟩
  invFun x :=
    ⟨h.symm x.1, ((g _).symm (cast (by rw [symm_coe]) x.2))⟩
  leftInv x := by
    dsimp
    congr
    rw [coe_symm]
    conv => { rhs; rw [←coe_symm (g x.fst) x.snd] }
    congr 1
    any_goals rw [coe_symm]
    apply cast_heq
  rightInv := by
    intro a
    dsimp
    congr
    rw [symm_coe]
    rw [(g _).symm_coe]
    apply cast_heq

def liftSigma {α₀ α₁: Type*} {β₀: α₀ -> Type*} {β₁: α₁ -> Type*} :
  ((Σ'a: α₀, β₀ a) ≃ (Σ'a: α₁, β₁ a)) ≃ ((Σa: α₀, β₀ a) ≃ (Σa: α₁, β₁ a)) :=
  (congrEquiv (sigma_equiv_psigma _) (sigma_equiv_psigma _)).symm

def congrSigma {α₀ α₁: Type*} {β₀: α₀ -> Type*} {β₁: α₁ -> Type*} (h: α₀ ≃ α₁) (g: ∀a: α₀, β₀ a ≃ β₁ (h a)) : (Σa: α₀, β₀ a) ≃ (Σa: α₁, β₁ a) :=
  liftSigma (congrPSigma h g)

def congrPi {α₀ α₁: Sort*} {β₀: α₀ -> Sort*} {β₁: α₁ -> Sort*} (h: α₀ ≃ α₁) (g: ∀a: α₀, β₀ a ≃ β₁ (h a)) : (∀a: α₀, β₀ a) ≃ (∀a: α₁, β₁ a) where
  toFun f a := cast (by rw [symm_coe]) (g _ (f (h.symm a)))
  invFun f a := (g _).symm (f (h a))
  leftInv := by
    intro f
    ext x; dsimp
    apply (g _).inj
    rw [symm_coe]
    apply cast_eq_of_heq
    rw [coe_symm]
  rightInv := by
    intro f
    ext x; dsimp
    apply cast_eq_of_heq
    rw [(g _).symm_coe, symm_coe]

def congrFunction {α₀ α₁ β₀ β₁: Sort*} (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ -> β₀) ≃ (α₁ -> β₁) :=
  congrPi h (fun _ => g)

def subtype_equiv_psigma {α: Sort*} (P: α -> Prop) : Subtype P ≃ Σ'x, P x where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv x := by rfl
  rightInv x := by rfl

def liftSubtype {α β: Sort*} {P: α -> Prop} {Q: β -> Prop}: ((Σ'x, P x) ≃ Σ'x, Q x) ≃ (Subtype P ≃ Subtype Q) :=
  (congrEquiv (subtype_equiv_psigma _) (subtype_equiv_psigma _)).symm

def congrSubtype { α β: Sort _ } {P: α -> Prop} {Q: β -> Prop} (h: α ≃ β) (iff: ∀{x}, P x ↔ Q (h.toFun x)) : Subtype P ≃ Subtype Q :=
  liftSubtype (congrPSigma h (fun _ => equivIff.symm iff))

def fin {n m: Nat} (h: n = m) : Fin n ≃ Fin m where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  leftInv x := by rfl
  rightInv x := by rfl

def fin_equiv_nat_subtype : Fin n ≃ { x: Nat // x < n } where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv x := by rfl
  rightInv x := by rfl

def array_equiv_list (α: Type*) : Array α ≃ List α where
  toFun a := a.toList
  invFun a := ⟨a⟩
  leftInv x := by rfl
  rightInv x := by rfl

def empty [IsEmpty α] [IsEmpty β] : α ≃ β where
  toFun := elim_empty
  invFun := elim_empty
  leftInv x := elim_empty x
  rightInv x := elim_empty x

def unique (α β: Sort*) [Subsingleton α] [Subsingleton β] [Inhabited α] [Inhabited β] : α ≃ β where
  toFun _ := default
  invFun _ := default
  leftInv _ := Subsingleton.allEq _ _
  rightInv _ := Subsingleton.allEq _ _

def embed_equiv_subtype (α β: Sort*) : (α ↪ β) ≃ { f: α -> β // f.Injective } where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  leftInv x := by rfl
  rightInv x := by rfl

def liftEmbed {α₀ α₁ β₀ β₁} :
  ({ f: α₀ -> β₀ // Function.Injective f } ≃ { f: α₁ -> β₁ // Function.Injective f }) ≃
  ((α₀ ↪ β₀) ≃ (α₁ ↪ β₁)) :=
  (congrEquiv (embed_equiv_subtype _ _) (embed_equiv_subtype _ _)).symm

def congrEmbed {α₀ α₁ β₀ β₁} (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ↪ β₀) ≃ (α₁ ↪ β₁) := by
  apply liftEmbed (congrSubtype (congrFunction h g) ?_)
  intro f
  unfold congrFunction congrPi
  dsimp
  show _ ↔ Function.Injective (g ∘ f ∘ _)
  apply Iff.trans _ (Function.Injective.of_comp_iff g.inj _).symm
  apply Iff.intro
  intro finj
  apply Function.Injective.comp
  assumption
  apply h.symm.inj
  intro i x y eq
  rw [←coe_symm h x, ←coe_symm h y] at eq
  exact h.inj (i eq)

def eqv_equiv_subtype (α β: Type*) : (α ≃ β) ≃ { fg: (α -> β) × (β -> α) // Function.IsRightInverse fg.1 fg.2 ∧ Function.IsLeftInverse fg.1 fg.2 } where
  toFun x := ⟨⟨x.1, x.2⟩, x.3, x.4⟩
  invFun x := ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩
  leftInv x := by rfl
  rightInv x := by rfl

def fin_equiv_option (n: Nat) : Fin (n + 1) ≃ Option (Fin n) where
  toFun x := if h:x.val = n then .none else .some ⟨x.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ x.isLt) h⟩
  invFun
  | .some x => x.castSucc
  | .none => Fin.last _
  leftInv := by
    intro x
    dsimp
    cases x using Fin.lastCases
    dsimp; rw [dif_pos _root_.rfl]
    rw [dif_neg]
    rfl
    rename_i x
    intro h
    replace h : x.val = n := h
    exact Nat.lt_irrefl _ (h ▸ x.isLt)
  rightInv := by
    intro x
    cases x
    simp
    simp
    rename_i x
    intro h
    replace h : x.val = n := h
    exact Nat.lt_irrefl _ (h ▸ x.isLt)

def option_equiv_unit_sum (α: Type*) : Option α ≃ Unit ⊕ α where
  toFun
  | .some a => .inr a
  | .none => .inl ()
  invFun
  | .inr x => .some x
  | .inl () => .none
  leftInv := by
    intro x
    cases x <;> rfl
  rightInv := by
    intro x
    cases x <;> rfl

def empty_not_equiv_nonempty (α β: Sort*) [IsEmpty α] [g: Nonempty β] : α ≃ β -> False := by
  intro h
  obtain ⟨b⟩ := g
  exact elim_empty (h.symm b)

-- maps a = b, and preserves as much of the other structure as possible
def set (h: α ≃ β) (a: α) (b: β) [∀x, Decidable (x = a)] [∀x, Decidable (x = b)] : α ≃ β where
  toFun x :=
    if x = a then b
    else if h x = b then
      h a
    else
      h x
  invFun x :=
    if x = b then a
    else if h.symm x = a then
      h.symm b
    else
      h.symm x
  leftInv := by
    intro x
    dsimp
    by_cases h₀:x = a
    rw [if_pos h₀, if_pos _root_.rfl, h₀]
    rw [if_neg h₀]
    by_cases h₁:h x = b
    rw [if_pos h₁, if_neg, if_pos, ←h₁, coe_symm]
    rw [coe_symm]
    rw [←h₁, Function.Injective.eq_iff h.inj]
    apply Ne.symm; assumption
    rw [if_neg h₁, if_neg h₁, if_neg, coe_symm]
    rw [coe_symm]; assumption
  rightInv := by
    intro x
    dsimp
    by_cases h₀:x = b
    rw [if_pos h₀, if_pos _root_.rfl, h₀]
    rw [if_neg h₀]
    by_cases h₁:h.symm x = a
    rw [if_pos h₁, if_neg, if_pos, ←h₁, symm_coe]
    rw [symm_coe]
    rw [←h₁, Function.Injective.eq_iff h.symm.inj]
    apply Ne.symm; assumption
    rw [if_neg h₁, if_neg h₁, if_neg, symm_coe]
    rw [symm_coe]; assumption

def swap (a b: α) [∀x, Decidable (x = a)] [∀x, Decidable (x = b)] : α ≃ α :=
  Equiv.set Equiv.rfl a b

def swap_symm [DecidableEq α] (a b: α) :
  (Equiv.swap a b).symm = Equiv.swap b a := by
  simp only [swap, symm, set]
  ext x
  simp [DFunLike.coe, Equiv.refl]
  rfl

def apply_set {x a: α} {b: β} [∀x, Decidable (x = a)] [∀x, Decidable (x = b)]  (h: α ≃ β) :
  h.set a b x = if x = a then b else if h x = b then  h a else h x := by rfl
def apply_set_symm {a: α} {x b: β} [∀x, Decidable (x = a)] [∀x, Decidable (x = b)]  (h: α ≃ β) :
  (h.set a b).symm x = if x = b then a else if h.symm x = a then  h.symm b else h.symm x := by rfl
def set_symm {a: α} {b: β} [∀x, Decidable (x = a)] [∀x, Decidable (x = b)]  (h: α ≃ β) :
  (h.set a b).symm = h.symm.set b a := by rfl

def set_spec (h: α ≃ β) (a: α) (b: β) [∀x, Decidable (x = a)] [∀x, Decidable (x = b)] :
  h.set a b a = b := by
  show (h.set a b).toFun a = b
  unfold set
  simp

def symm_set_spec (h: α ≃ β) (a: α) (b: β) [∀x, Decidable (x = a)] [∀x, Decidable (x = b)] :
  (h.set a b).symm b = a := by
  symm; apply eq_coe_of_symm_eq
  rw [symm_symm, set_spec]

def swap_spec (a b: α) [∀x, Decidable (x = a)] [∀x, Decidable (x = b)]:
  Equiv.swap a b a = b := Equiv.set_spec _ _ _

def swap_comm [DecidableEq α] (a b: α) : swap a b = swap b a := by
  ext x
  unfold swap set
  simp
  split <;> split
  subst a b; rfl
  subst a; rw [if_pos]; rfl
  rfl
  rw [if_pos]; rfl
  assumption
  rw [if_neg, if_neg]
  assumption
  assumption

private instance : ∀(x: Option α), Decidable (x = .none)
| .none => .isTrue _root_.rfl
| .some _ => .isFalse Option.noConfusion

def of_equiv_option_option {α β: Type*} (h: Option α ≃ Option β) : α ≃ β :=
  let h := h.set .none .none
  {
  toFun x := (h x).get (by
    apply Decidable.byContradiction
    intro g
    have := (Option.not_isSome_iff_eq_none.mp g)
    have := eq_symm_of_coe_eq _ this
    rw [symm_set_spec] at this
    contradiction)
  invFun x := (h.symm x).get (by
    apply Decidable.byContradiction
    intro g
    have := (Option.not_isSome_iff_eq_none.mp g)
    have := eq_coe_of_symm_eq _ this
    rw [set_spec] at this
    contradiction)
  leftInv _ := by simp
  rightInv _ := by simp
  }

-- booleans are classically equivalent to Prop
open Classical in noncomputable def bool_equiv_prop : Bool ≃ Prop where
  toFun p := p
  invFun p := decide p
  leftInv x := by
    dsimp
    rw [Bool.decide_coe]
  rightInv x := by
    dsimp
    exact decide_eq_true_eq

def bind_subtype (P Q: α -> Prop) : {x:Subtype P // Q x} ≃ {x: α // P x ∧ Q x} where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.left⟩, x.property.right⟩
  leftInv _ := by rfl
  rightInv _ := by rfl

def subtype_quot_equiv_quot_subtype (p₁ : α → Prop) {s₁ : Setoid α} {s₂ : Setoid (Subtype p₁)}
    (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ (Quotient.mk _ a))
    (h : ∀ x y : Subtype p₁, s₂.r x y ↔ s₁.r x y) : {x // p₂ x} ≃ Quotient s₂ where
    toFun | ⟨val, hval⟩ => val.hrecOn (motive := fun x => p₂ x -> _) (by
      intro x hx
      apply Quotient.mk _ ⟨x, (hp₂ _).mpr hx⟩) (by
        intro a b eqv
        dsimp
        apply Function.hfunext
        rw [Quotient.sound eqv]
        intro pa pb peq
        apply heq_of_eq
        apply Quotient.sound
        simp [HasEquiv.Equiv]
        apply (h _ _).mpr
        assumption) hval
    invFun := Quotient.lift (fun ⟨x, hx⟩ => ⟨Quotient.mk _ x, (hp₂ _).mp hx⟩) (by
        intro a b eq
        dsimp
        congr  1
        apply Quotient.sound
        apply (h _ _).mp
        assumption)
    leftInv := by
      intro ⟨x, hx⟩
      dsimp
      cases x using Quotient.ind
      rfl
    rightInv := by
      intro x
      dsimp
      cases x using Quotient.ind
      rfl

def option_sigma_equiv_sum_sigma {β: Option α -> Type*} : (Σx: Option α, β x) ≃ β .none ⊕ Σx: α, β x where
  toFun
  | ⟨.none, b⟩ => .inl b
  | ⟨.some a, b⟩ => .inr ⟨a, b⟩
  invFun
  | .inl b => ⟨.none, b⟩
  | .inr ⟨a, b⟩ => ⟨.some a, b⟩
  leftInv x := by
    rcases x with ⟨a, b⟩
    cases a <;> rfl
  rightInv x := by cases x <;> rfl

def option_pi_equiv_prod_pi {β: Option α -> Type*} : (∀x: Option α, β x) ≃ β .none × ∀x: α, β x where
  toFun f := ⟨f _, fun _ => f _⟩
  invFun f x := match x with
     | .none => f.1
     | .some x => f.2 x
  leftInv f := by
    dsimp
    ext x
    cases x <;> rfl
  rightInv x := by cases x <;> rfl

def option_prod_equiv_sum_prod {β: Type*} : ((Option α) × β) ≃ β ⊕ α × β :=
  Equiv.trans (prod_equiv_sigma _ _) (Equiv.trans Equiv.option_sigma_equiv_sum_sigma (congrSum .rfl (prod_equiv_sigma _ _).symm))

def option_perm_equiv_prod_perm [DecidableEq α] : (Option α ≃ Option α) ≃ Option α × (α ≃ α) where
  toFun f := (f .none, Equiv.of_equiv_option_option f)
  invFun | ⟨x, f⟩ => (Equiv.congrOption f).set .none x
  leftInv := by
    intro f
    simp
    ext a b
    cases a
    rw [Equiv.set_spec]
    rename_i a
    simp [Equiv.apply_set, Equiv.of_equiv_option_option, Equiv.congrOption]
    apply Iff.intro
    intro ⟨⟨h₀, h₁⟩, h₂⟩
    rw [if_neg h₀] at h₂
    assumption
    intro h
    iterate 2 apply And.intro
    intro g; rw [g] at h
    contradiction
    intro g
    have := f.inj g
    contradiction
    rw [if_neg]
    assumption
    intro g; rw [g] at h
    contradiction
  rightInv := by
    intro (a, f)
    simp [Equiv.apply_set]
    ext x
    simp [f.apply_set, Equiv.of_equiv_option_option]
    apply Option.some.inj
    rw [Option.some_get]
    rw [Equiv.apply_set, if_neg]
    split <;> rename_i h
    rw [Equiv.set_spec]
    rw [Equiv.apply_set, if_neg] at h
    split at h
    rename_i g
    rw [←g]; rfl
    contradiction
    intro; contradiction
    rw [Equiv.apply_set, if_neg]
    split
    · rename_i g
      rw [Equiv.apply_set, if_neg, if_pos g] at h
      contradiction
      intro; contradiction
    rfl
    intro; contradiction
    intro; contradiction

def empty_emb_equiv_unit [_root_.IsEmpty α] : (α ↪ β) ≃ Unit where
  toFun _ := ()
  invFun _ := Embedding.empty
  rightInv _ := _root_.rfl
  leftInv _ := by
    ext x
    exact elim_empty x

def empty_sum_eqv [_root_.IsEmpty α] : α ⊕ β ≃ β where
  toFun
  | .inl x => elim_empty x
  | .inr x => x
  invFun x := .inr x
  leftInv x := by
    cases x <;> rename_i x
    exact elim_empty x
    rfl
  rightInv x := _root_.rfl

def sum_empty_eqv [_root_.IsEmpty β] : α ⊕ β ≃ α :=
  (commSum _ _).trans empty_sum_eqv

def sum_assoc (α β γ: Type*) : α ⊕ β ⊕ γ ≃ (α ⊕ β) ⊕ γ where
  toFun
  | .inl x => .inl (.inl x)
  | .inr (.inl x) => .inl (.inr x)
  | .inr (.inr x) => .inr x
  invFun
  | .inl (.inl x) => .inl x
  | .inl (.inr x) => .inr (.inl x)
  | .inr x => .inr (.inr x)
  leftInv x := by rcases x with x | x | x <;> rfl
  rightInv x := by rcases x with (x | x) | x <;> rfl

def option_sum_eqv : Option α ⊕ β ≃ Option (α ⊕ β) := by
  apply Equiv.trans
  exact congrSum (option_equiv_unit_sum _) .rfl
  apply flip Equiv.trans
  exact (option_equiv_unit_sum _).symm
  symm; apply sum_assoc

def remove {α: Type*} (a: α) [∀x: α, Decidable (x = a)] : α ≃ Option { x: α // x ≠ a } where
  toFun x :=
    if h:x = a then
      .none
    else
      .some ⟨_ ,h⟩
  invFun
  | .none => a
  | .some x => x.val
  leftInv x := by
    simp
    by_cases h:x = a
    rw [dif_pos h]; exact h.symm
    rw [dif_neg h]
  rightInv x := by
    match x with
    | .none => simp
    | .some ⟨x, hx⟩ => simp [hx]

def fin_rev : Fin n ≃ Fin n where
  toFun := Fin.rev
  invFun := Fin.rev
  leftInv x := by rw [Fin.rev_rev]
  rightInv x := by rw [Fin.rev_rev]

def subsing_prod_left [Subsingleton α] [Inhabited α] : α × β ≃ β where
  toFun x := x.2
  invFun x := ⟨default, x⟩
  leftInv := by
    intro x
    simp
    congr; apply Subsingleton.allEq
  rightInv := by
    intro x
    rfl

def subsing_prod_right [Subsingleton β] [Inhabited β] : α × β ≃ α where
  toFun x := x.1
  invFun x := ⟨x, default⟩
  leftInv := by
    intro x
    simp
    congr; apply Subsingleton.allEq
  rightInv := by
    intro x
    rfl

-- rotates all elements in the range i <= x <= j by k
def splitRange (i j k: Nat): Fin (i + j + k) ≃ Fin i ⊕ Fin j ⊕ Fin k where
  toFun x :=
    if hi:x.val < i then
      .inl ⟨x.val, hi⟩
    else if hj:x.val < i + j then
      .inr <| .inl ⟨x.val - i, by omega⟩
    else
      .inr <| .inr ⟨x.val - i - j, by omega⟩
  invFun
  | .inl x => ⟨x.val, by omega⟩
  | .inr (.inl x) => ⟨x.val + i, by omega⟩
  | .inr (.inr x) => ⟨x.val + i + j, by omega⟩
  leftInv x := by
    simp
    by_cases hi:x.val < i
    simp [hi]
    by_cases hj:x.val < i + j
    simp [hi, hj]
    congr; omega
    simp [hi, hj]
    congr; omega
  rightInv x := by
    cases x
    simp
    rename_i x
    cases x
    simp; rw [dif_neg, dif_pos]
    omega
    omega
    simp; rw [dif_neg, dif_neg]
    simp; congr
    omega
    omega
    omega

def apply_splitRange_eq₁ {i j k: Nat} (x: Fin (i + j + k)) (h: x.val < i) :
  splitRange i j k x = .inl ⟨x.val, h⟩ := by simp [splitRange, h]
def apply_splitRange_eq₂ {i j k: Nat} (x: Fin (i + j + k)) (h₀: i ≤ x.val) (h₁: x < i + j):
  splitRange i j k x = .inr (.inl ⟨x.val - i, by omega⟩) := by simp [splitRange, Nat.not_lt_of_le h₀, h₁]
def apply_splitRange_eq₃ {i j k: Nat} (x: Fin (i + j + k)) (h₀: i + j ≤ x.val):
  splitRange i j k x = .inr (.inr ⟨x.val - i - j, by omega⟩) := by
    simp [splitRange]
    rw [dif_neg, dif_neg]
    omega
    omega

def rotate (n k: Nat) : Fin n ≃ Fin n where
  toFun x := ⟨(x + k) % n, Nat.mod_lt _ x.pos⟩
  invFun x := ⟨(x + n - k % n) % n, Nat.mod_lt _ x.pos⟩
  leftInv x := by
    simp; congr
    rw [Nat.add_sub_assoc, Nat.add_mod, Nat.mod_mod, ←Nat.add_mod,
      Nat.add_assoc, Nat.add_mod, ←Nat.add_sub_assoc,
        Nat.add_comm k, Nat.add_sub_assoc, Nat.add_mod n,
        Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    rw (occs := [1]) [←Nat.div_add_mod k n]
    rw [Nat.add_sub_cancel, Nat.mul_mod_right, Nat.add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt]
    omega
    apply Nat.mod_le
    repeat
      apply Nat.le_of_lt
      apply Nat.mod_lt
      exact x.pos
  rightInv x := by
    simp; congr
    rw [Nat.add_comm, ←Nat.add_sub_assoc, Nat.add_comm k,
      Nat.add_sub_assoc, Nat.add_mod, Nat.add_mod_right]
    rw (occs := [1]) [←Nat.div_add_mod k n]
    rw [Nat.add_sub_cancel, Nat.mul_mod_right, Nat.add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt]
    omega
    apply Nat.mod_le
    apply Nat.le_trans
    apply Nat.le_of_lt
    apply Nat.mod_lt
    exact x.pos
    apply Nat.le_add_left

-- rotates all elements in the range i <= x <= j by k
def rotateRange (i j: Fin n) (offset: Nat) : Fin n ≃ Fin n := by
  exact go (min i.val j.val) (max i.val j.val) (by omega) (by omega)
  where
  go a c (h: a ≤ c) (g: c < n) := by
    let i' := a
    let j' := c - a + 1
    let k' := n - c - 1
    have : n = i' + j' + k' := by omega
    apply (Equiv.congrEquiv' (fin this).symm (fin this).symm)
    apply (Equiv.congrEquiv' (splitRange _ _ _).symm (splitRange _ _ _).symm)
    apply Equiv.congrSum .rfl
    apply Equiv.congrSum _ .rfl
    apply rotate _ offset

def rotateRange_comm (i j: Fin n) (offset: Nat) :
  rotateRange i j offset = rotateRange j i offset := by
  unfold rotateRange
  congr 1
  rw [Nat.min_comm]
  rw [Nat.max_comm]

def rotateRange_of_le (i j: Fin n) (offset: Nat) (x: Fin n)
  (h: i ≤ j) (hx: x < i) : rotateRange i j offset x = x := by
  unfold rotateRange
  conv => {
    lhs; arg 1
    conv => { arg 2; rw [Nat.min_eq_left h] }
    conv => { arg 3; rw [Nat.max_eq_right h]  }
  }
  unfold rotateRange.go
  simp [congrEquiv', apply_congrEquiv]

  sorry

end Equiv

def Fin.embedNat : Fin n ↪ Nat :=
  Equiv.fin_equiv_nat_subtype.toEmbedding.trans Embedding.subtypeVal

def Fin.embedFin (h: n ≤ m) : Fin n ↪ Fin m where
  toFun x := ⟨x, Nat.lt_of_lt_of_le x.isLt h⟩
  inj' x y eq := by cases x; cases y; cases eq; rfl

def Nat.not_between_succ (n m: Nat) : n < m -> m < n + 1 -> False := by
  intro h g
  replace g := Nat.le_of_lt_succ g
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h g)

def Fin.le_of_emebd (h: Fin n ↪ Fin m) : n ≤ m := by
  induction n generalizing m with
  | zero => apply Nat.zero_le
  | succ n ih =>
    cases m with
    | zero => exact (h 0).elim0
    | succ m =>
      apply Nat.succ_le_succ
      apply ih
      apply Embedding.of_option_embed_option
      apply Equiv.congrEmbed _ _ h
      apply Equiv.fin_equiv_option
      apply Equiv.fin_equiv_option

def Fin.eqOfEquiv (h: Fin n ≃ Fin m) : n = m := by
  apply Nat.le_antisymm
  apply Fin.le_of_emebd
  apply h.toEmbedding
  apply Fin.le_of_emebd
  apply h.symm.toEmbedding

def Subtype.val_inj {P: α -> Prop} : Function.Injective (Subtype.val (p := P)) := Embedding.subtypeVal.inj

instance [Subsingleton α] : Subsingleton (α ≃ β) where
  allEq := by
    intro a b
    ext x
    apply a.symm.inj
    apply Subsingleton.allEq

instance [Subsingleton β] : Subsingleton (α ≃ β) where
  allEq := by
    intro a b
    ext x
    apply Subsingleton.allEq

def Embedding.option_emb_equiv_prod_emb [_root_.DecidableEq α] [_root_.DecidableEq β] : (Option α ↪ Option β) ≃ Option β × (α ↪ β) where
  toFun f := (f .none, Embedding.of_option_embed_option f)
  invFun | ⟨x, f⟩ => {
    toFun
    | .some a =>
      if f a = x then
        .none
      else
        f a
    | .none => x
    inj' := by
      intro a b eq
      cases a <;> cases b <;> dsimp at eq
      rfl
      iterate 2
        split at eq
        subst x
        contradiction
        subst x
        contradiction
      split at eq
      subst x
      split at eq
      rename_i h
      congr; symm
      exact f.inj (Option.some.inj h)
      contradiction
      split at eq
      subst x
      contradiction
      congr
      rename_i h
      exact f.inj (Option.some.inj eq)
  }
  leftInv := by
    intro f
    simp
    ext a b
    cases a <;> simp [Embedding.of_option_embed_option]
    rename_i a
    split <;> rename_i b' h
    apply Iff.intro
    rintro ⟨h, rfl⟩
    assumption
    intro g
    apply And.intro
    intro g'
    have := f.inj (h.trans g')
    contradiction
    rw [h] at g
    exact Option.some.inj g
    simp
    rw [h]; exact nofun
  rightInv := by
    intro (b, f)
    unfold Embedding.of_option_embed_option
    ext a
    simp
    dsimp
    rw [Embedding.mk_apply _ _ a]
    simp
    split <;> rename_i h
    simp [Embedding.mk_apply] at h
    exact h.right.symm
    simp at h
    apply Option.some.inj
    rw [Option.some_get]; symm; assumption
