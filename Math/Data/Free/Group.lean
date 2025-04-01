import Math.Data.Free.Monoid
import Math.Algebra.GroupQuot.Defs

inductive FreeGroup.Rel (α: Type*) : FreeMonoid (Bool × α) -> FreeMonoid (Bool × α) -> Prop where
| inv_mul_cancel : Rel α (.of (!x, a) * .of (x, a)) 1

def FreeGroup (α: Type*) := GroupQuot (FreeGroup.Rel α)

instance : MonoidOps (FreeGroup α) := inferInstanceAs (MonoidOps (GroupQuot _))
instance : IsMonoid (FreeGroup α) := inferInstanceAs (IsMonoid (GroupQuot _))

private def FreeGroup.flip : FreeMonoid (Bool × α) →* FreeMonoid (Bool × α) where
  toFun a := a.map (fun x => (!x.1, x.2))
  map_one := rfl
  map_mul {x y} := by simp

private def FreeGroup.inv : FreeGroup α →* (FreeGroup α)ᵐᵒᵖ := by
  refine GroupQuot.lift ⟨?_, ?_⟩
  apply GroupHom.comp ?_ FreeMonoid.reverseEquiv.toHom
  apply GroupHom.congrMulOpp _
  apply (IsMulCon.mkQuot _).comp
  apply FreeGroup.flip
  intro x y h
  simp [GroupHom.apply_comp, GroupHom.apply_congrMulOpp]
  congr 1
  rw [GroupQuot.mkQuot_eq_mk]
  show GroupQuot.mk _ (flip x.reverse) = GroupQuot.mk _ (flip y.reverse)
  cases h
  simp [FreeMonoid.reverse_mul]
  apply GroupQuot.mk_rel
  rename_i x a
  rw (occs := [1]) [←Bool.not_not x]
  apply FreeGroup.Rel.inv_mul_cancel

@[simp]
private def FreeGroup.inv_mk (a: FreeMonoid (Bool × α)) : (inv (GroupQuot.mk _ a)).get = GroupQuot.mk _ (flip a.reverse) := by
  unfold FreeGroup.inv
  erw [GroupQuot.lift_mk_apply]
  rw [GroupQuot.mkQuot_eq_mk]
  rfl

@[simp]
def FreeGroup.flip_one : flip (1: FreeMonoid (Bool × α)) = 1 := rfl

@[simp]
def FreeGroup.flip_of_mul_of : GroupQuot.mk (FreeGroup.Rel _) (flip (.of a) * .of a) = 1 := by
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
