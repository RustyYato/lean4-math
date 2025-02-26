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

-- it's not possible to embed functions from α to some non-trival type into α
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

def congrULift {α β: Type*} (h: α ≃ β) : ULift α ≃ ULift β :=
  (ulift α).trans (h.trans (ulift β).symm)

def congrPLift {α β: Sort*} (h: α ≃ β) : PLift α ≃ PLift β :=
  (plift α).trans (h.trans (plift β).symm)

def prod_equiv_pprod (α β: Type*) : α × β ≃ α ×' β where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv _ := by rfl
  rightInv _ := by rfl

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
  trans (prod_equiv_pprod _ _) (trans (congrPProd a b) (prod_equiv_pprod _ _).symm)

def commPProd (α β: Sort*) : α ×' β ≃ β ×' α where
  toFun x := ⟨x.2, x.1⟩
  invFun x := ⟨x.2, x.1⟩
  leftInv x := by rfl
  rightInv x := by rfl

def commProd (α β: Type*) : α × β ≃ β × α :=
  trans (prod_equiv_pprod _ _) (trans (commPProd _ _) (prod_equiv_pprod _ _).symm)

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

def congrSum {α₀ α₁ β₀ β₁: Type*} (a: α₀ ≃ α₁) (b: β₀ ≃ β₁) : α₀ ⊕ β₀ ≃ α₁ ⊕ β₁ :=
  trans (sum_equiv_psum _ _) (trans (congrPSum a b) (sum_equiv_psum _ _).symm)

def commPSum (α β: Sort*) : α ⊕' β ≃ β ⊕' α where
  toFun
  | .inl x => .inr x
  | .inr x => .inl x
  invFun
  | .inl x => .inr x
  | .inr x => .inl x
  leftInv x := by cases x <;> rfl
  rightInv x := by cases x <;> rfl

def commSum (α β: Type*) : α ⊕ β ≃ β ⊕ α :=
  trans (sum_equiv_psum _ _) (trans (commPSum _ _) (sum_equiv_psum _ _).symm)

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

def congrSigma {α₀ α₁: Type*} {β₀: α₀ -> Type*} {β₁: α₁ -> Type*} (h: α₀ ≃ α₁) (g: ∀a: α₀, β₀ a ≃ β₁ (h a)) : (Σa: α₀, β₀ a) ≃ (Σa: α₁, β₁ a) :=
  trans (sigma_equiv_psigma _) (trans (congrPSigma h g) (sigma_equiv_psigma _).symm)

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

def congrSubtype { α β: Sort _ } {P: α -> Prop} {Q: β -> Prop}
  (h: α ≃ β)
  (iff: ∀{x}, P x ↔ Q (h.toFun x)) : Subtype P ≃ Subtype Q :=
  trans (subtype_equiv_psigma _) (trans (congrPSigma h (fun _ => equivIff.symm iff)) (subtype_equiv_psigma _).symm)

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

def congrEmbed {α₀ α₁ β₀ β₁} (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ↪ β₀) ≃ (α₁ ↪ β₁) := by
  refine trans (embed_equiv_subtype _ _) (trans (congrSubtype (congrFunction h g) ?_) (embed_equiv_subtype _ _).symm)
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
  leftInv := by
    intro x
    simp
    conv => { lhs; lhs; rw [coe_symm] }
    rfl
  rightInv := by
    intro x
    simp
    conv => { lhs; lhs; rw [symm_coe] }
    rfl
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

def Fin.eqOfEquiv (h: Fin n ≃ Fin m) : n = m := by
  induction n generalizing m with
  | zero =>
    cases m
    rfl
    have := Equiv.empty_not_equiv_nonempty _ _ h
    contradiction
  | succ n ih =>
    cases m with
    | zero =>
      have := Equiv.empty_not_equiv_nonempty _ _ h.symm
      contradiction
    | succ m =>
      replace h := (Equiv.fin_equiv_option n).symm.trans <| h.trans (Equiv.fin_equiv_option m)
      rw [ih (Equiv.of_equiv_option_option h)]

def Subtype.val_inj {P: α -> Prop} : Function.Injective (Subtype.val (p := P)) := Embedding.subtypeVal.inj
