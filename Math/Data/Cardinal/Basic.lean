import Math.Tactics.PPWithUniv
import Math.Algebra.Ring
import Math.Data.Fin.Basic
import Math.Data.Nat.Pairing
import Math.Data.Fintype.Card
import Math.Order.Linear

def type_setoid : Setoid (Type u) where
  r a b := Nonempty (a ≃ b)
  iseqv := ⟨fun _ => ⟨Equiv.rfl⟩, fun ⟨a⟩ => ⟨a.symm⟩, fun ⟨a⟩ ⟨b⟩ => ⟨a.trans b ⟩⟩

attribute [local refl] Setoid.refl
attribute [local symm] Setoid.symm

@[pp_with_univ]
def Cardinal := Quotient type_setoid

namespace Cardinal

def mk : Type u -> Cardinal.{u} := Quotient.mk _
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

def lift : Cardinal.{u} -> Cardinal.{max u v} := by
  apply Quotient.lift (mk ∘ ULift)
  intro a b ⟨eq⟩
  apply sound
  apply (Equiv.ulift _).trans
  apply Equiv.trans _ (Equiv.ulift _).symm
  assumption

def ofNat (n: Nat) : Cardinal :=  ⟦Fin n⟧

instance : OfNat Cardinal n := ⟨(ofNat n).lift⟩

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

instance : SMul ℕ Cardinal where
  smul n x := (ofNat n).lift * x
instance : Pow Cardinal.{u} ℕ where
  pow x n := x ^ (ofNat n).lift

instance : NatCast Cardinal where
  natCast n := OfNat.ofNat n

@[simp]
def lift_add (a: Cardinal.{u}) (b: Cardinal.{v}) : a.lift.add b = (a.add b).lift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrSum
  apply Equiv.ulift
  rfl

@[simp]
def add_lift (a: Cardinal.{u}) (b: Cardinal.{v}) : a.add b.lift = (a.add b).lift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrSum
  rfl
  apply Equiv.ulift

@[simp]
def lift_mul (a: Cardinal.{u}) (b: Cardinal.{v}) : a.lift.mul b = (a.mul b).lift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrProd
  apply Equiv.ulift
  rfl

@[simp]
def mul_lift (a: Cardinal.{u}) (b: Cardinal.{v}) : a.mul b.lift = (a.mul b).lift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrProd
  rfl
  apply Equiv.ulift

@[simp]
def lift_pow (a: Cardinal.{u}) (b: Cardinal.{v}) : a.lift.pow b = (a.pow b).lift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrFunction
  rfl
  apply Equiv.ulift

@[simp]
def pow_lift (a: Cardinal.{u}) (b: Cardinal.{v}) : a.pow b.lift = (a.pow b).lift := by
  cases a, b with | mk a b =>
  apply sound
  apply Equiv.trans _
  symm; apply Equiv.ulift
  apply Equiv.congrFunction
  apply Equiv.ulift
  rfl

@[simp]
def lift_lift (a: Cardinal.{u}) : (Cardinal.lift.{max u v, w} (Cardinal.lift.{u, v} a)) = Cardinal.lift.{u, max v w} a := by
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
  exact (Fin.equivAdd _ _).symm

def OfNat_add (n m: Nat) : (OfNat.ofNat (n + m): Cardinal) = OfNat.ofNat n + OfNat.ofNat m := by
  show lift _ = (lift _).add (lift _)
  simp
  apply sound
  apply Equiv.trans
  apply Equiv.ulift
  apply flip Equiv.trans; symm
  apply Equiv.ulift
  exact (Fin.equivAdd _ _).symm

def ofNat_mul (n m: Nat) : ofNat (n * m) = ofNat n * ofNat m := by
  apply sound
  exact (Fin.equivMul _ _).symm

def OfNat_mul (n m: Nat) : (OfNat.ofNat (n * m): Cardinal) = OfNat.ofNat n * OfNat.ofNat m := by
  show lift _ = (lift _).mul (lift _)
  simp
  apply sound
  apply Equiv.trans
  apply Equiv.ulift
  apply flip Equiv.trans; symm
  apply Equiv.ulift
  exact (Fin.equivMul _ _).symm

def Fin.equivPow (n m: Nat) : Trunc ((Fin m -> Fin n) ≃ Fin (n ^ m)) := by
  apply Fintype.equivOfCardEq
  simp [Fintype.card_function, Fintype.card_fin]

-- def ofNat_pow (n m: Nat) : ofNat (n ^ m) = ofNat n ^ ofNat m := by
--   apply sound
--   exact (Fin.equivPow _ _).symm

def OfNat_pow (n m: Nat) : (OfNat.ofNat (n ^ m): Cardinal) = OfNat.ofNat n ^ OfNat.ofNat m := by
  show lift _ = (lift _).pow (lift _)
  simp
  induction Fin.equivPow n m with | mk h =>
  apply sound
  apply Equiv.trans
  apply Equiv.ulift
  apply flip Equiv.trans; symm
  apply Equiv.ulift
  exact h.symm

instance : IsAddCommMagma Cardinal where
  add_comm (a b: Cardinal) := by
    cases a, b with | mk a b =>
    apply sound
    apply Equiv.commSum

instance : IsCommMagma Cardinal where
  mul_comm (a b: Cardinal) := by
    cases a, b with | mk a b =>
    apply sound
    apply Equiv.commProd

instance : IsAddZeroClass Cardinal := by
  apply IsAddZeroClass.ofAddCommMagma
  intro a
  cases a with | mk a =>
  show (lift _).add _ = _
  rw [lift_add]
  apply sound
  apply Equiv.trans
  apply Equiv.ulift
  apply Equiv.mk _ _ _ _
  intro h
  match h with
  | .inl h => exact h.elim0
  | .inr h => exact h
  exact .inr
  intro h
  cases h <;> rename_i h
  exact h.elim0
  rfl
  intro
  rfl

instance : IsMulZeroClass Cardinal := by
  apply IsMulZeroClass.ofCommMagma
  intro a
  cases a with | mk a =>
  show (lift _).mul _ = _
  rw [lift_mul]
  apply sound
  apply flip Equiv.trans; symm
  apply Equiv.ulift
  apply Equiv.mk _ _ _ _
  intro ⟨h, _⟩
  exact h
  intro h
  exact h.elim0
  intro ⟨h, _⟩
  exact h.elim0
  intro h
  exact h.elim0

instance : IsMulOneClass Cardinal := by
  apply IsMulOneClass.ofCommMagma
  intro a
  cases a with | mk a =>
  show (lift _).mul _ = _
  rw [lift_mul]
  apply sound
  apply Equiv.mk _ _ _ _
  intro ⟨_, x⟩
  exact x
  intro x
  exact ⟨0, x⟩
  intro ⟨_, x⟩
  dsimp
  congr
  apply Subsingleton.allEq
  intro
  rfl

instance : IsLeftDistrib Cardinal where
  left_distrib k a b := by
    cases a, b, k with | mk A B K =>
    apply sound
    apply Equiv.mk _ _ _ _
    intro ⟨k, x⟩
    match x with
    | .inl x => exact .inl ⟨k, x⟩
    | .inr x => exact .inr ⟨k, x⟩
    intro x
    match x with
    | .inl ⟨k, x⟩ => exact ⟨k, .inl x⟩
    | .inr ⟨k, x⟩ => exact ⟨k, .inr x⟩
    intro ⟨k, x⟩
    cases x <;> rfl
    intro x
    cases x <;> rfl

instance : IsAddMonoid Cardinal where
  add_assoc a b c := by
    cases a, b, c with | mk A B C =>
    apply sound
    apply Equiv.mk _ _ _ _
    intro h
    match h with
    | .inl (.inl x) => exact .inl x
    | .inl (.inr x) => exact .inr <| .inl x
    | .inr x => exact .inr <| .inr x
    intro h
    match h with
    | .inl x => exact .inl <| .inl x
    | .inr (.inl x) => exact .inl <| .inr x
    | .inr (.inr x) => exact .inr x
    intro x
    rcases x with (_ | _) | _ <;> rfl
    intro x
    rcases x with _ | _ | _ <;> rfl
  zero_nsmul := by
    intro x
    show 0 * _ = 0
    rw [zero_mul x]
  succ_nsmul n a := by
    show OfNat.ofNat _ * _ = _
    erw [OfNat_add, add_mul, one_mul]
    rfl

instance : IsMonoid Cardinal where
  mul_assoc a b c := by
    cases a, b, c with | mk A B C =>
    apply sound
    apply Equiv.mk _ _ _ _
    intro ⟨⟨a, b⟩, c⟩
    exact ⟨a, b, c⟩
    intro ⟨a, b, c⟩
    exact ⟨⟨a, b⟩, c⟩
    intro ⟨⟨a, b⟩, c⟩
    rfl
    intro ⟨a, b, c⟩
    rfl
  npow_zero a := by
    cases a with | mk A =>
    apply sound
    apply Equiv.mk _ _ _ _
    intro h
    exact ⟨0⟩
    intro x y
    exact y.down.elim0
    intro x
    apply Subsingleton.allEq
    intro x
    apply Subsingleton.allEq
  npow_succ n a := by
    cases a with | mk A =>
    apply sound
    apply Equiv.trans
    apply Equiv.congrFunction
    apply Equiv.ulift
    rfl
    apply flip Equiv.trans; symm
    apply Equiv.congrProd
    apply Equiv.congrFunction (Equiv.ulift _) (by rfl)
    rfl
    apply Equiv.mk _ _ _ _
    intro f
    constructor
    intro x
    exact f x.succ
    exact f 0
    intro ⟨f, a⟩ x
    if h:x = 0 then
      exact a
    else
      exact f (x.pred h)
    intro f
    funext x
    dsimp
    split <;> rename_i h
    rw [h]
    rw [Fin.succ_pred]
    intro ⟨f, a⟩
    congr

instance : IsAddMonoidWithOne Cardinal where
  natCast_zero := rfl
  natCast_succ x := OfNat_add x 1
  ofNat_eq_natCast _ := rfl

instance : IsSemiring Cardinal where
  npow_succ := npow_succ
  npow_zero := npow_zero

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
