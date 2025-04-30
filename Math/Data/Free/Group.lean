import Math.Data.Free.Monoid
import Math.Algebra.GroupQuot
import Math.Algebra.Group.Hom

inductive FreeGroup.Rel (α: Type*) : FreeMonoid (Bool × α) -> FreeMonoid (Bool × α) -> Prop where
| inv_mul_cancel : Rel α (.of (!x, a) * .of (x, a)) 1

def FreeGroup (α: Type*) := GroupQuot (FreeGroup.Rel α)

def FreeAddGroup (α: Type*) := AddOfMul (FreeGroup α)

namespace FreeGroup

instance : MonoidOps (FreeGroup α) := inferInstanceAs (MonoidOps (GroupQuot _))
instance : IsMonoid (FreeGroup α) := inferInstanceAs (IsMonoid (GroupQuot _))

private def flip : FreeMonoid (Bool × α) →* FreeMonoid (Bool × α) where
  toFun a := a.map (fun x => (!x.1, x.2))
  map_one := rfl
  map_mul {x y} := by simp

private def inv : FreeGroup α →* (FreeGroup α)ᵐᵒᵖ := by
  refine GroupQuot.lift ⟨?_, ?_⟩
  apply GroupHom.comp ?_ FreeMonoid.reverseEquiv.toHom
  apply GroupHom.congrMulOpp _
  apply (GroupQuot.mk _).comp
  apply FreeGroup.flip
  intro x y h
  simp [GroupHom.apply_comp, GroupHom.apply_congrMulOpp]
  congr 1
  show GroupQuot.mk _ (flip x.reverse) = GroupQuot.mk _ (flip y.reverse)
  cases h
  simp [FreeMonoid.reverse_mul]
  apply GroupQuot.mk_rel
  rename_i x a
  rw (occs := [1]) [←Bool.not_not x]
  apply FreeGroup.Rel.inv_mul_cancel

@[simp]
private def inv_mk (a: FreeMonoid (Bool × α)) : (inv (GroupQuot.mk _ a)).get = GroupQuot.mk _ (flip a.reverse) := by
  erw [GroupQuot.lift_mk_apply]; rfl

@[simp]
def flip_one : flip (1: FreeMonoid (Bool × α)) = 1 := rfl

@[simp]
def flip_of_mul_of : GroupQuot.mk (FreeGroup.Rel _) (flip (.of a) * .of a) = 1 := by
  rw [←map_one (GroupQuot.mk _)]
  apply GroupQuot.mk_rel
  apply Rel.inv_mul_cancel

instance : Inv (FreeGroup α) where
  inv := FreeGroup.inv

instance : Div (FreeGroup α) where
  div a b := a * b⁻¹

instance : Pow (FreeGroup α) ℤ where
  pow a n :=
    match n with
    | .ofNat n => a ^ n
    | .negSucc n => (a ^ (n + 1))⁻¹

instance : IsGroup (FreeGroup α) where
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl
  inv_mul_cancel a := by
    show (FreeGroup.inv a).get * a = 1
    induction a using GroupQuot.ind with | mk a =>
    simp
    rw [←map_mul (GroupQuot.mk _), ←map_one (GroupQuot.mk _)]
    induction a with
    | one => simp
    | of_mul a as ih =>
      simp [FreeMonoid.reverse_mul]
      iterate 4 rw [map_mul]
      rw [mul_assoc]; rw (occs := [2]) [←mul_assoc]
      rw [←map_mul]
      simp
      rw [←map_mul]
      assumption

def of (a: α) : FreeGroup α := GroupQuot.mk _ (FreeMonoid.of (false, a))

private def of_inv (a: α) : (of a)⁻¹ = GroupQuot.mk _ (FreeMonoid.of (true, a)) := by
  show inv _ = _
  apply GroupQuot.lift_mk_apply

private def preLift [GroupOps G] [IsGroup G] (f: α -> G) : FreeGroup α →* G := by
  apply GroupQuot.lift ⟨?_, ?_⟩
  apply FreeMonoid.lift (M := G) (fun
    | (false, a) => f a
    | (true, a) => (f a)⁻¹)
  intro a b h
  cases h
  simp [map_one, map_mul]
  rename_i x a
  cases x <;> simp

def lift [GroupOps G] [IsGroup G] : (α -> G) ≃ (FreeGroup α →* G) where
  toFun := preLift
  invFun f a := f (.of a)
  leftInv f := by
    ext a
    simp
    unfold FreeGroup.preLift of
    erw [GroupQuot.lift_mk_apply]
    apply mul_one
  rightInv f := by
    ext a
    induction a using GroupQuot.ind with | mk a =>
    erw [GroupQuot.lift_mk_apply]
    induction a with
    | one => simp [map_one]
    | of_mul a as ih =>
      simp [map_mul, ih]; clear ih
      obtain ⟨b, a⟩ := a
      cases b <;> simp
      rfl
      rw [←of_inv, ←map_inv]

def lift_log [AddGroupOps G] [IsAddGroup G] : (α -> G) ≃ (FreeGroup α →ₘ+ G) :=
  Equiv.trans (lift (G := MulOfAdd G)) Equiv.log_hom_equiv_group_hom.symm

@[simp]
def lift_of [GroupOps G] [IsGroup G] (f: α -> G) : lift f (of a) = f a := by
  erw [GroupQuot.lift_mk_apply, FreeMonoid.lift_of]

@[simp]
def lift_log_of [AddGroupOps G] [IsAddGroup G] (f: α -> G) : lift_log f (of a) = f a := by
  erw [GroupQuot.lift_mk_apply, FreeMonoid.lift_of]

private def Indicator := Bool

private instance : DecidableEq Indicator := inferInstanceAs (DecidableEq Bool)
private instance {P: Indicator -> Prop} [DecidablePred P] : Decidable (∃x, P x) := inferInstanceAs (Decidable (∃x: Bool, P x))
private instance {P: Indicator -> Prop} [DecidablePred P] : Decidable (∀x, P x) := inferInstanceAs (Decidable (∀x: Bool, P x))

private instance : One Indicator := ⟨false⟩
private instance : Mul Indicator := ⟨xor⟩
private instance : Inv Indicator := ⟨id⟩

private instance : MonoidOps Indicator where
  npow := _root_.flip npowRec
private instance : GroupOps Indicator where
  zpow := _root_.flip zpowRec

private instance : IsGroup Indicator where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  div_eq_mul_inv := by decide
  inv_mul_cancel := by decide
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl

def of_inj : Function.Injective (of (α := α)) := by
  intro a b h
  classical
  let f := lift (G := Indicator) (fun x => if x = b then false else true)
  have : f (of b) = false := by rw [lift_of, if_pos rfl]
  have : f (of a) = false := by rw [h, this]
  simpa [f] using this

def one_ne_of (a: α) : 1 ≠ of a := by
  intro h
  classical
  let f := lift (G := Indicator) (fun x => if x = a then true else false)
  have : f (of a) = true := by rw [lift_of, if_pos rfl]
  have : f 1 = true := by rw [h, this]
  simp [f, map_one] at this

@[induction_eliminator]
def induction {motive: FreeGroup α -> Prop}
  (one: motive 1)
  (of: ∀a, motive (.of a))
  (inv: ∀a, motive (.of a) -> motive (.of a)⁻¹)
  (mul: ∀a b, motive a -> motive b -> motive (a * b)) :
  ∀a, motive a := by
  intro a
  induction a using GroupQuot.ind with | mk a =>
  induction a with
  | one => rwa [map_one]
  | of_mul a as ih =>
    rw [map_mul]
    apply mul _ _ _ ih
    obtain ⟨b, a⟩ := a
    cases b
    apply of
    rw [←of_inv]
    apply inv
    apply of

instance : Inhabited (FreeGroup α) := ⟨1⟩
instance : Nonempty (FreeGroup α) := inferInstance
instance [IsEmpty α] : Subsingleton (FreeGroup α) where
  allEq a b := by
    induction a using GroupQuot.ind with | mk a =>
    induction b using GroupQuot.ind with | mk b =>
    congr
    apply Subsingleton.allEq
instance [h: Nonempty α] : IsNontrivial (FreeGroup α) where
  exists_ne := by
    obtain ⟨a⟩ := h
    exists 1
    exists .of a
    apply one_ne_of

attribute [irreducible] FreeGroup of lift instMonoidOps instInv instDiv instPowInt

def lift_of' (a : FreeGroup α) : lift of a = a := by
  induction a with
  | one | of | inv => simp [map_one, map_inv]
  | mul => rw [map_mul]; congr

def lift_assoc {x: FreeGroup α} (f: α -> FreeGroup β) (g: β -> FreeGroup γ) :
  (lift g) ((lift f) x) = (lift fun x => (lift g) (f x)) x := by
  show lift _ (lift _ _) = lift (fun x => lift _ _) _
  induction x with
  | one => simp [map_one]
  | of => simp
  | inv => simp [map_inv]
  | mul => simp [map_mul]; congr

instance : Monad FreeGroup where
  pure := of
  bind a b := lift b a

instance : LawfulMonad FreeGroup := by
  apply LawfulMonad.mk'
  case id_map =>
    apply lift_of'
  case pure_bind =>
    intro α β x f
    apply lift_of
  case bind_assoc =>
    intro α β γ x f g
    apply lift_assoc
  all_goals intro α β x y; rfl

end FreeGroup

namespace FreeAddGroup

instance : AddGroupOps (FreeAddGroup α) := inferInstanceAs (AddGroupOps (AddOfMul _))
instance : IsAddGroup (FreeAddGroup α) := inferInstanceAs (IsAddGroup (AddOfMul _))

def of (a: α) : FreeAddGroup α := AddOfMul.mk (FreeGroup.of a)

def lift [AddGroupOps G] [IsAddGroup G] : (α -> G) ≃ (FreeAddGroup α →+ G) :=
  Equiv.trans (FreeGroup.lift (G := MulOfAdd G)) <|
    Equiv.congrGroupHomToAddGroupHom (LogEquiv.AddOfMul _) (LogEquiv.MulOfAdd _)

def lift_exp [GroupOps G] [IsGroup G] : (α -> G) ≃ (FreeAddGroup α →ₐ* G) :=
  Equiv.trans (lift (G := AddOfMul G)) Equiv.exp_hom_equiv_addgroup_hom.symm

@[simp]
def lift_of [AddGroupOps G] [IsAddGroup G] (f: α -> G) : lift f (of a) = f a := by
  apply FreeGroup.lift_of (G := MulOfAdd G)

@[simp]
def lift_exp_of [GroupOps G] [IsGroup G] (f: α -> G) : lift_exp f (of a) = f a := by
  apply FreeGroup.lift_of (G := G)

def of_inj : Function.Injective (of (α := α)) :=
  FreeGroup.of_inj

def zero_ne_of (a: α) : 0 ≠ of a :=
  FreeGroup.one_ne_of _

@[induction_eliminator]
def induction {motive: FreeAddGroup α -> Prop}
  (zero: motive 0)
  (of: ∀a, motive (.of a))
  (neg: ∀a, motive (.of a) -> motive (-.of a))
  (add: ∀a b, motive a -> motive b -> motive (a + b)) :
  ∀a, motive a := FreeGroup.induction zero of neg add

instance : Inhabited (FreeAddGroup α) := ⟨0⟩
instance : Nonempty (FreeAddGroup α) := inferInstance
instance [IsEmpty α] : Subsingleton (FreeAddGroup α) where
  allEq := Subsingleton.allEq (α := FreeGroup α)
instance [h: Nonempty α] : IsNontrivial (FreeAddGroup α) where
  exists_ne := by
    obtain ⟨a⟩ := h
    exists 0
    exists .of a
    apply zero_ne_of

attribute [irreducible] FreeAddGroup of lift instAddGroupOps

def lift_of' (a : FreeAddGroup α) : lift of a = a := by
  induction a with
  | zero | of | neg => simp [map_zero, map_neg]
  | add => rw [map_add]; congr

def lift_assoc {x: FreeAddGroup α} (f: α -> FreeAddGroup β) (g: β -> FreeAddGroup γ) :
  (lift g) ((lift f) x) = (lift fun x => (lift g) (f x)) x := by
  show lift _ (lift _ _) = lift (fun x => lift _ _) _
  induction x with
  | zero => simp [map_zero]
  | of => simp
  | neg => simp [map_neg]
  | add => simp [map_add]; congr

instance : Monad FreeAddGroup where
  pure := of
  bind a b := lift b a

instance : LawfulMonad FreeAddGroup := by
  apply LawfulMonad.mk'
  case id_map =>
    apply lift_of'
  case pure_bind =>
    intro α β x f
    apply lift_of
  case bind_assoc =>
    intro α β γ x f g
    apply lift_assoc
  all_goals intro α β x y; rfl

end FreeAddGroup

def Equiv.congrFreeGroup (h: α ≃ β) : FreeGroup α ≃ FreeGroup β where
  toFun a := FreeGroup.lift (fun a => .of (h a)) a
  invFun a := FreeGroup.lift (fun a => .of (h.symm a)) a
  leftInv a := by
    simp
    rw [FreeGroup.lift_assoc]
    simp
    apply FreeGroup.lift_of'
  rightInv a := by
    simp
    rw [FreeGroup.lift_assoc]
    simp
    apply FreeGroup.lift_of'

def GroupEquiv.congrFreeGroup (f: α ≃ β) : FreeGroup α ≃* FreeGroup β where
  toEquiv := Equiv.congrFreeGroup f
  map_one := by simp [Equiv.congrFreeGroup, map_one]
  map_mul := by simp [Equiv.congrFreeGroup, map_mul]

def Equiv.congrFreeAddGroup (h: α ≃ β) : FreeAddGroup α ≃ FreeAddGroup β where
  toFun a := FreeAddGroup.lift (fun a => .of (h a)) a
  invFun a := FreeAddGroup.lift (fun a => .of (h.symm a)) a
  leftInv a := by
    simp
    rw [FreeAddGroup.lift_assoc]
    simp
    apply FreeAddGroup.lift_of'
  rightInv a := by
    simp
    rw [FreeAddGroup.lift_assoc]
    simp
    apply FreeAddGroup.lift_of'

def AddGroupEquiv.congrFreeAddGroup (f: α ≃ β) : FreeAddGroup α ≃+ FreeAddGroup β where
  toEquiv := Equiv.congrFreeAddGroup f
  map_zero := by simp [Equiv.congrFreeAddGroup, map_zero]
  map_add := by simp [Equiv.congrFreeAddGroup, map_add]

def Equiv.FreeGroup_eqv_FreeAddGroup (h: α ≃ β) : FreeGroup α ≃ FreeAddGroup β where
  toFun a := FreeGroup.lift_log (fun a => .of (h a)) a
  invFun a := FreeAddGroup.lift_exp (fun a => .of (h.symm a)) a
  leftInv a := by
    induction a with
    | of => simp
    | one => dsimp; rw [map_one_to_zero, map_zero_to_one]
    | inv => simp [map_inv_to_neg, map_neg_to_inv]
    | mul a b iha ihb => simp [map_add_to_mul, map_mul_to_add, iha, ihb]
  rightInv a := by
    induction a with
    | of => simp
    | zero => dsimp; rw [map_zero_to_one, map_one_to_zero]
    | neg => simp [map_inv_to_neg, map_neg_to_inv]
    | add a b iha ihb => simp [map_add_to_mul, map_mul_to_add, iha, ihb]

def LogEquiv.FreeGroup_eqv_FreeAddGroup (h: α ≃ β) : FreeGroup α ≃ₘ+ FreeAddGroup β where
  toEquiv := Equiv.FreeGroup_eqv_FreeAddGroup h
  map_mul_to_add {a b} := by simp [Equiv.FreeGroup_eqv_FreeAddGroup, map_mul_to_add]
  map_one_to_zero := by simp [Equiv.FreeGroup_eqv_FreeAddGroup, map_one_to_zero]

def ExpEquiv.FreeGroup_eqv_FreeAddGroup (h: α ≃ β) : FreeAddGroup α ≃ₐ* FreeGroup β :=
  (LogEquiv.FreeGroup_eqv_FreeAddGroup h.symm).symm
