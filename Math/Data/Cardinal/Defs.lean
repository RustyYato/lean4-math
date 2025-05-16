import Math.Tactics.PPWithUniv
import Math.Data.Nat.Pairing
import Math.Data.Trunc
import Math.Logic.Equiv.Basic

def type_setoid : Setoid (Type u) where
  r a b := Nonempty (a ≃ b)
  iseqv := ⟨fun _ => ⟨Equiv.rfl⟩, fun ⟨a⟩ => ⟨a.symm⟩, fun ⟨a⟩ ⟨b⟩ => ⟨a.trans b ⟩⟩

attribute [local refl] Setoid.refl
attribute [local symm] Setoid.symm

@[pp_with_univ]
def Cardinal := Quotient type_setoid

namespace Cardinal

def mk : Type u -> Cardinal.{u} := Quotient.mk _
prefix:max "#" => Cardinal.mk
scoped notation "⟦" x "⟧" => Cardinal.mk x
@[cases_eliminator]
def ind {motive: Cardinal -> Prop} : (mk: ∀a, motive ⟦a⟧) -> ∀a, motive a := Quotient.ind
@[cases_eliminator]
def ind₂ {motive: Cardinal -> Cardinal -> Prop} : (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) -> ∀a b, motive a b := Quotient.ind₂
@[cases_eliminator]
def ind₃ {motive: Cardinal -> Cardinal -> Cardinal -> Prop} : (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro h a b c
  cases a, b
  cases c
  apply h
@[cases_eliminator]
def ind₄ {motive: Cardinal -> Cardinal -> Cardinal -> Cardinal -> Prop} : (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) -> ∀a b c d, motive a b c d := by
  intro h a b c d
  cases a, b
  cases c, d
  apply h
def sound {a b: Type u} : a ≃ b -> ⟦a⟧ = ⟦b⟧ := Quotient.sound ∘ Nonempty.intro
def exact {a b: Type u} : ⟦a⟧ = ⟦b⟧ -> Nonempty (a ≃ b) := Quotient.exact

def type (c: Cardinal.{u}) : Type u := Classical.choose (Quotient.exists_rep c)
def type_spec (c: Cardinal.{u}) : #c.type = c := Classical.choose_spec (Quotient.exists_rep c)
noncomputable def type_eqv_of_eq (a b: Cardinal.{u}) : a = b -> a.type ≃ b.type := by
  intro h
  apply Classical.choice
  apply exact
  rw [type_spec, type_spec, h]
noncomputable def mk_type_eqv (α: Type u) : (#α).type ≃ α := by
  apply Classical.choice
  apply exact
  rw [type_spec]

@[pp_with_univ]
def ulift : Cardinal.{u} -> Cardinal.{max u v} := by
  apply Quotient.lift (mk ∘ ULift)
  intro a b ⟨eq⟩
  apply sound
  apply (Equiv.ulift _).trans
  apply Equiv.trans _ (Equiv.ulift _).symm
  assumption

noncomputable def type_eqv_of_ulift_eq (a: Cardinal.{u}) (b: Cardinal.{v}) : ulift.{u, max u v} a = ulift.{v, max u v} b -> a.type ≃ b.type := by
  intro h
  apply Equiv.congrEquiv (Equiv.ulift.{_, max u v} _) (Equiv.ulift.{_, max u v} _) _
  apply Classical.choice
  apply exact
  show ulift ⟦_⟧ = ulift ⟦_⟧
  rw [type_spec, type_spec, h]
noncomputable def ulift_type (a: Cardinal.{u}) : (ulift.{u, v} a).type ≃ ULift a.type := by
  apply Classical.choice
  apply exact
  rw [type_spec]
  show _ = ulift ⟦_⟧
  rw [type_spec]

def ulift_eq_self (a: Cardinal) : ulift a = a := by
  cases a; apply sound
  apply Equiv.ulift

def ofNat (n: Nat) : Cardinal :=  ⟦Fin n⟧

instance : NatCast Cardinal where
  natCast n := (ofNat n).ulift
instance : OfNat Cardinal n := ⟨n⟩

def add : Cardinal -> Cardinal -> Cardinal := by
  apply Quotient.lift₂ (fun _ _ => ⟦_⟧) _
  intro a b
  exact a ⊕ b
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound
  apply Equiv.congrSum <;> assumption

def mul : Cardinal -> Cardinal -> Cardinal := by
  apply Quotient.lift₂ (fun _ _ => ⟦_⟧) _
  intro a b
  exact a × b
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound
  apply Equiv.congrProd <;> assumption

def pow : Cardinal -> Cardinal -> Cardinal := by
  apply Quotient.lift₂ (fun _ _ => ⟦_⟧) _
  intro a b
  exact b -> a
  intro a b c d ⟨ac⟩ ⟨bd⟩
  apply sound
  apply Equiv.congrFunction <;> assumption

def sum {ι: Type v} (f: ι -> Cardinal.{u}) : Cardinal.{max u v} := ⟦Σi: ι, (f i).type⟧

def prod {ι: Type v} (f: ι -> Cardinal.{u}) : Cardinal.{max u v} := ⟦∀i: ι, (f i).type⟧

instance : Add Cardinal := ⟨add⟩
instance : Mul Cardinal := ⟨mul⟩
instance : HPow Cardinal.{u} Cardinal.{v} Cardinal.{max u v} := ⟨pow⟩

instance : Pow Cardinal.{u} ℕ where
  pow x n := x ^ (n: Cardinal)

@[simp]
def lift_add (a: Cardinal.{u}) (b: Cardinal.{v}) : a.ulift.add b = (a.add b).ulift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrSum
  apply Equiv.ulift
  rfl

@[simp]
def add_lift (a: Cardinal.{u}) (b: Cardinal.{v}) : a.add b.ulift = (a.add b).ulift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrSum
  rfl
  apply Equiv.ulift

@[simp]
def lift_mul (a: Cardinal.{u}) (b: Cardinal.{v}) : a.ulift.mul b = (a.mul b).ulift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrProd
  apply Equiv.ulift
  rfl

@[simp]
def mul_lift (a: Cardinal.{u}) (b: Cardinal.{v}) : a.mul b.ulift = (a.mul b).ulift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrProd
  rfl
  apply Equiv.ulift

@[simp]
def lift_pow (a: Cardinal.{u}) (b: Cardinal.{v}) : a.ulift.pow b = (a.pow b).ulift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrFunction
  rfl
  apply Equiv.ulift

@[simp]
def pow_lift (a: Cardinal.{u}) (b: Cardinal.{v}) : a.pow b.ulift = (a.pow b).ulift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrFunction
  apply Equiv.ulift
  rfl

def sum_lift (f: ι -> Cardinal.{u}) : sum (ulift.{u, v} ∘ f) = ulift.{u, max u v} (sum f) := by
  apply sound
  simp
  apply flip Equiv.trans
  apply (Equiv.ulift _).symm
  apply Equiv.congrSigma .rfl
  intro i
  apply type_eqv_of_ulift_eq
  simp
  rw [ulift_eq_self]
  generalize f i = c
  cases c
  apply sound
  apply Equiv.congrEquiv (Equiv.ulift _).symm (Equiv.ulift _).symm _
  rfl

def prod_lift (f: ι -> Cardinal.{u}) : prod (ulift.{u, v} ∘ f) = ulift.{u, max u v} (prod f) := by
  apply sound
  simp
  apply flip Equiv.trans
  apply (Equiv.ulift _).symm
  apply Equiv.congrPi .rfl
  intro i
  apply type_eqv_of_ulift_eq
  simp
  rw [ulift_eq_self]
  generalize f i = c
  cases c
  apply sound
  apply Equiv.congrEquiv (Equiv.ulift _).symm (Equiv.ulift _).symm _
  rfl

def sum_const (c: Cardinal) : sum (fun _: ι => c) = #ι * c := by
  cases c with | mk α =>
  apply sound
  simp
  symm; apply flip Equiv.trans
  apply Equiv.prod_equiv_sigma
  apply Equiv.congrProd
  rfl
  exact (mk_type_eqv α).symm

def prod_const (c: Cardinal) : prod (fun _: ι => c) = c ^ #ι := by
  cases c with | mk α =>
  apply sound
  simp
  apply Equiv.congrFunction
  rfl
  exact (mk_type_eqv α)

@[simp]
def lift_lift (a: Cardinal.{u}) : (ulift.{max u v, w} (ulift.{u, v} a)) = ulift.{u, max v w} a := by
  cases a with | mk a =>
  apply sound
  apply Equiv.trans
  apply Equiv.ulift
  apply Equiv.trans
  apply Equiv.ulift
  apply flip Equiv.trans
  symm; apply Equiv.ulift
  rfl

def ofNat_add (n m: Nat) : ofNat (n + m) = ofNat n + ofNat m := by
  apply sound
  exact Equiv.finSum.symm

def aleph0 : Cardinal := ⟦ℕ⟧
def aleph0' : Cardinal := ulift ⟦ℕ⟧
notation "ℵ₀" => aleph0'

end Cardinal
