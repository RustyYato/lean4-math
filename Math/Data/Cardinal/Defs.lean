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

def ulift : Cardinal.{u} -> Cardinal.{max u v} := by
  apply Quotient.lift (mk ∘ ULift)
  intro a b ⟨eq⟩
  apply sound
  apply (Equiv.ulift _).trans
  apply Equiv.trans _ (Equiv.ulift _).symm
  assumption

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
notation "ℵ₀" => aleph0

def aleph0_add_fin (n: Nat) : ℵ₀ + n = ℵ₀ := by
  apply sound
  apply Equiv.mk _ _ _ _
  intro x
  match x with
  | .inl x => exact x + n
  | .inr x => exact x.down.val
  intro x
  if h:x < n then
    exact .inr ⟨⟨x, h⟩⟩
  else
    exact .inl (x - n)
  intro x
  simp
  cases x
  dsimp
  rw [dif_neg, Nat.add_sub_cancel]
  apply Nat.not_lt_of_le
  apply Nat.le_add_left
  dsimp
  rw [if_pos]
  rename_i x
  exact x.down.isLt
  intro x
  dsimp
  by_cases h:x < n
  rw [dif_pos h]
  rw [dif_neg h]
  dsimp
  rw [Nat.sub_add_cancel]
  apply Nat.le_of_not_lt
  assumption

def aleph0_add_aleph0 : ℵ₀ + ℵ₀ = ℵ₀ := by
  apply sound
  exact Equiv.nat_equiv_nat_sum_nat.symm

def aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀ := by
  apply sound
  exact Equiv.nat_equiv_nat_prod_nat.symm

end Cardinal
