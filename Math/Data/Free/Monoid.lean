import Math.Algebra.Monoid.Hom
import Math.Logic.IsEmpty
import Math.Logic.Equiv.Defs

def FreeMonoid (α: Type*) : Type _ := List α

namespace FreeMonoid

def toList : FreeMonoid α -> List α := id
def ofList : List α -> FreeMonoid α := id

instance : One (FreeMonoid α) where
  one := .ofList []

instance : Inhabited (FreeMonoid α) where
  default := 1

instance : Mul (FreeMonoid α) where
  mul a b := .ofList (a.toList ++ b.toList)

instance : Pow (FreeMonoid α) ℕ := instNPowrec

instance : IsMonoid (FreeMonoid α) where
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

instance : IsMulCancel (FreeMonoid α) where
  mul_left_cancel := List.append_cancel_left
  mul_right_cancel := List.append_cancel_right

def ι : α ↪ FreeMonoid α where
  toFun a := .ofList [a]
  inj' := by
    intro x y h
    exact (List.cons.inj h).left

@[simp] def one_toList : toList (1: FreeMonoid α) = [] := rfl
@[simp] def ι_toList (a: α) : toList (.ι a) = [a] := rfl
@[simp] def mul_toList (a b: FreeMonoid α) : toList (a * b) = a.toList ++ b.toList := rfl

@[simp] def one_ofList : ofList ([]: List α) = 1 := rfl
@[simp] def ι_ofList (a: α) : ofList [a] = .ι a := rfl
@[simp] def mul_ofList (a b: List α) : ofList (a ++ b) = ofList a * ofList b := rfl

def reverse (a: FreeMonoid α) : FreeMonoid α := .ofList a.toList.reverse

def reverseEquiv : FreeMonoid α ≃* (FreeMonoid α)ᵐᵒᵖ where
  toFun a := .mk (reverse a)
  invFun a := reverse a.get
  leftInv := by apply List.reverse_reverse
  rightInv := by apply List.reverse_reverse
  map_one := rfl
  map_mul := by
    intro x y
    apply List.reverse_append

@[simp] def reverse_one : (reverse 1: FreeMonoid α) = 1 := rfl
@[simp] def reverse_ι : reverse (ι a) = ι a := rfl
def reverseEquiv_ι : reverseEquiv (ι a) = ι a := rfl

def reverse_mul {a b : FreeMonoid α} : reverse (a * b) = reverse b * reverse a := by
  apply List.reverse_append

@[induction_eliminator]
def induction {motive: FreeMonoid α -> Prop}
  (one: motive 1)
  (ι_mul: ∀a b, motive b -> motive (.ι a * b)) :
  ∀a, motive a := by
  intro a
  induction a with
  | nil => apply one
  | cons a as ih =>
    apply ι_mul
    assumption

@[cases_eliminator]
def cases {motive: FreeMonoid α -> Prop}
  (one: motive 1)
  (ι_mul: ∀a b, motive (.ι a * b)) :
  ∀a, motive a := by
  intro a
  cases a with
  | nil => apply one
  | cons a as =>
    apply ι_mul

def map (a: FreeMonoid α) (f: α -> β) : FreeMonoid β :=
  .ofList (a.toList.map f)

@[simp]
def ι_map (a: α) (f: α -> β) : map (.ι a) f  = .ι (f a) := rfl

@[simp]
def mul_map (a b: FreeMonoid α) (f: α -> β) : (a * b).map f = (a.map f) * (b.map f) :=
  List.map_append

def length (a: FreeMonoid α) : Nat :=
  a.toList.length

@[simp] def one_length : length (1: FreeMonoid α) = 0 := rfl
@[simp] def ι_length : length (ι a) = 1 := rfl
@[simp] def mul_length : length (a * b) = a.length + b.length := List.length_append

-- lift any assignment ι variables to a monoid into a group homomorphism from the
-- free monoid to the given monoid
def lift [MonoidOps M] [IsMonoid M] : (α -> M) ≃ (FreeMonoid α →* M) where
  toFun f := {
    toFun a := a.toList.foldr (fun a m => f a * m) 1
    map_one := rfl
    map_mul := by
      intro x y
      simp
      generalize x.toList=x'
      generalize y.toList=y'
      clear x y
      induction x' with
      | nil => simp
      | cons x xs ih => simp [ih, mul_assoc]
  }
  invFun f a := f (.ι a)
  leftInv := by
    intro  f
    simp
    ext a
    apply mul_one
  rightInv := by
    intro f
    ext a
    simp
    show List.foldr _ _ a.toList = f a
    induction a with
    | one => rw [map_one]; rfl
    | ι_mul a as ih =>
      show List.foldr _ _ (a :: as.toList) = _
      rw [List.foldr_cons, ih, map_mul]

@[simp] def lift_ι [MonoidOps M] [IsMonoid M] (f: α -> M) (a: α) : lift f (.ι a) = f a := by
  apply mul_one

def one_ne_ι (a: α) : 1 ≠ ι a := nofun

instance : Nonempty (FreeMonoid α) := inferInstance
instance [IsEmpty α] : Subsingleton (FreeMonoid α) where
  allEq a b := by
    cases a
    cases b
    rfl
    rename_i a _
    exact elim_empty a
    rename_i a _
    exact elim_empty a
instance [h: Nonempty α] : IsNontrivial (FreeMonoid α) where
  exists_ne := by
    obtain ⟨a⟩ := h
    exists 1
    exists .ι a
    apply one_ne_ι

def lift_ι' (a : FreeMonoid α) : lift ι a = a := by
  induction a with
  | one => simp [map_one]
  | ι_mul => rw [map_mul, lift_ι]; congr

def lift_assoc {x: FreeMonoid α} (f: α -> FreeMonoid β) (g: β -> FreeMonoid γ) :
  (lift g) ((lift f) x) = (lift fun x => (lift g) (f x)) x := by
  show lift _ (lift _ _) = lift (fun x => lift _ _) _
  induction x with
    | one => simp [map_one]
    | ι_mul => simp [map_mul]; congr

instance : Monad FreeMonoid where
  pure := ι
  bind a b := lift b a

instance : LawfulMonad FreeMonoid := by
  apply LawfulMonad.mk'
  case id_map =>
    apply lift_ι'
  case pure_bind =>
    intro α β x f
    apply lift_ι
  case bind_assoc =>
    intro α β γ x f g
    apply lift_assoc
  all_goals intro α β x y; rfl

end FreeMonoid

def Equiv.congrFreeMonoid (h: α ≃ β) : FreeMonoid α ≃ FreeMonoid β where
  toFun a := FreeMonoid.lift (fun a => .ι (h a)) a
  invFun a := FreeMonoid.lift (fun a => .ι (h.symm a)) a
  leftInv a := by
    simp
    rw [FreeMonoid.lift_assoc]
    simp
    apply FreeMonoid.lift_ι'
  rightInv a := by
    simp
    rw [FreeMonoid.lift_assoc]
    simp
    apply FreeMonoid.lift_ι'

def MonoidEquiv.congrFreeMonoid (h: α ≃ β) : FreeMonoid α ≃* FreeMonoid β where
  toEquiv := Equiv.congrFreeMonoid h
  map_one := by simp [Equiv.congrFreeMonoid, map_one]
  map_mul := by simp [Equiv.congrFreeMonoid, map_mul]
