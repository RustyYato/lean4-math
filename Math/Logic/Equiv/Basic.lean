import Math.Logic.Equiv.Defs
import Math.Logic.Basic
import Math.Logic.IsEmpty

namespace Equiv

def ulift (α: Type*) : α ≃ ULift α where
  toFun := ULift.up
  invFun := ULift.down
  leftInv _ := by rfl
  rightInv _ := by rfl

def plift (α: Sort*) : α ≃ PLift α where
  toFun := PLift.up
  invFun := PLift.down
  leftInv _ := by rfl
  rightInv _ := by rfl

def congrULift {α β: Type*} (h: α ≃ β) : ULift α ≃ ULift β :=
  (ulift α).symm.trans (h.trans (ulift β))

def congrPLift {α β: Sort*} (h: α ≃ β) : PLift α ≃ PLift β :=
  (plift α).symm.trans (h.trans (plift β))

def prod_equiv_pprod (α β: Type*) : α × β ≃ α ×' β where
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

def optionCongr {α β: Type*} (h: α ≃ β) : Option α ≃ Option β where
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

def psigma_equiv_sigma {α: Type*} (β: α -> Type*) : (Σa: α, β a) ≃ (Σ'a: α, β a) where
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
  trans (psigma_equiv_sigma _) (trans (congrPSigma h g) (psigma_equiv_sigma _).symm)

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

def isempty [IsEmpty α] [IsEmpty β] : α ≃ β where
  toFun := elim_empty
  invFun := elim_empty
  leftInv x := elim_empty x
  rightInv x := elim_empty x

def unique (α β: Sort*) [Subsingleton α] [Subsingleton β] [Inhabited α] [Inhabited β] : α ≃ β where
  toFun _ := default
  invFun _ := default
  leftInv _ := Subsingleton.allEq _ _
  rightInv _ := Subsingleton.allEq _ _

end Equiv

namespace Embedding

def optionSome (α: Type*) : α ↪ Option α where
  toFun := .some
  inj' _ _ := Option.some.inj

def DecidableEq (emb: α ↪ β) [DecidableEq β] : DecidableEq α :=
  fun a b =>
  match inferInstanceAs (Decidable (emb a = emb b)) with
  | .isTrue h => .isTrue (emb.inj h)
  | .isFalse h => .isFalse fun g => h (g ▸ _root_.rfl)

end Embedding
