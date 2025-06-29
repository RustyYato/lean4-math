import Math.Algebra.Group.Con

def GroupQuot.Con [Mul α] (r: α -> α -> Prop) : MulCon α := MulCon.generate r
def AddGroupQuot.Con [Add α] (r: α -> α -> Prop) : AddCon α := AddCon.generate r

def GroupQuot [Mul α] (r: α -> α -> Prop) : Type _ := AlgQuotient (GroupQuot.Con r)
def AddGroupQuot [Add α] (r: α -> α -> Prop) : Type _ := AlgQuotient (AddGroupQuot.Con r)

namespace GroupQuot

section

variable {r: α -> α -> Prop}

instance instMonoidOps [MonoidOps α] [IsMonoid α] : MonoidOps (GroupQuot r) :=
  AlgQuotient.instMonoidOps _
instance instIsMonoid [MonoidOps α] [IsMonoid α] : IsMonoid (GroupQuot r) :=
  AlgQuotient.instIsMonoid _

instance instGroupOps [GroupOps α] [IsGroup α] : GroupOps (GroupQuot r) :=
  AlgQuotient.instGroupOps _
instance instIsGroup [GroupOps α] [IsGroup α] : IsGroup (GroupQuot r) :=
  AlgQuotient.instIsGroup _

instance instIsCommMagma [MonoidOps α] [IsMonoid α] [IsCommMagma α] : IsCommMagma (GroupQuot r) :=
  AlgQuotient.instIsCommMagma _

end

variable {r: G -> G -> Prop}

def mk [MonoidOps G] [IsMonoid G] (r: G -> G -> Prop) : G ↠* GroupQuot r :=
  MulCon.mkQuot _

@[induction_eliminator]
def ind [MonoidOps G] [IsMonoid G] {motive: GroupQuot r -> Prop} (mk: ∀x, motive (mk r x)) : ∀q, motive q := by
  intro q
  obtain ⟨_, rfl⟩ := (GroupQuot.mk r).surj q
  apply mk

def mk_rel [MonoidOps G] [IsMonoid G] (w: r x y) : mk r x = mk r y := Quot.sound (MulCon.Generator.of w)

private def preLift [MonoidOps G] [IsMonoid G] [MonoidOps T] [IsMonoid T] {r : G → G → Prop} {f : G →* T} (h : ∀ ⦃x y⦄, r x y → f x = f y) : GroupQuot r →* T where
  toFun := by
    refine  Quotient.lift f ?_
    intro a b g
    induction g with
    | of =>
      apply h
      assumption
    | refl => rfl
    | symm => symm; assumption
    | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
    | mul =>
      rw [map_mul, map_mul]
      congr
  map_one := map_one f
  map_mul := by
    intro a b
    induction a; induction b
    apply map_mul

def lift [MonoidOps G] [IsMonoid G] [MonoidOps T] [IsMonoid T]: {f: G →* T // ∀ ⦃x y⦄, r x y → f x = f y } ≃ (GroupQuot r →* T) where
  toFun f := preLift f.property
  invFun f := {
    val := f.comp (mk r)
    property := by
      intro x y h
      show f (mk r x) = f (mk r y)
      congr 1; apply mk_rel
      assumption
  }
  leftInv _ := rfl
  rightInv f := by
    ext x; induction x
    rfl

def lift_log [MonoidOps G] [IsMonoid G] [AddMonoidOps T] [IsAddMonoid T]: {f: G →ₘ+ T // ∀ ⦃x y⦄, r x y → f x = f y } ≃ (GroupQuot r →ₘ+ T) := by
  apply Equiv.congrEquiv _ _ (lift (G := G) (T := MulOfAdd T) (r := r))
  refine Equiv.congrSubtype ?_ ?_
  exact Equiv.log_hom_equiv_group_hom.symm
  rfl
  exact Equiv.log_hom_equiv_group_hom.symm

@[simp]
def lift_mk_apply [MonoidOps G] [IsMonoid G] [MonoidOps T] [IsMonoid T] (f : G →* T) {r : G → G → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
    lift ⟨f, w⟩ (mk r x) = f x := rfl

@[simp]
def symm_lift_mk_apply [MonoidOps G] [IsMonoid G] [MonoidOps T] [IsMonoid T] {r: G -> G -> Prop} (f : GroupQuot r →* T) (x: G) :
    (lift.symm f).val x = f (mk r x) := rfl

@[simp]
def lift_log_mk_apply [MonoidOps G] [IsMonoid G] [AddMonoidOps T] [IsAddMonoid T] (f : G →ₘ+ T) {r : G → G → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
    lift_log ⟨f, w⟩ (mk r x) = f x := rfl

@[simp]
def symm_lift_log_mk_apply [MonoidOps G] [IsMonoid G] [AddMonoidOps T] [IsAddMonoid T] {r: G -> G -> Prop} (f : GroupQuot r →ₘ+ T) (x: G) :
    (lift_log.symm f).val x = f (mk r x) := rfl

def mkQuot_eq_mk [MonoidOps G] [IsMonoid G] : MulCon.mkQuot (GroupQuot.Con r) = GroupQuot.mk r := rfl

attribute [irreducible] mk lift

end GroupQuot

namespace AddGroupQuot

section

variable {r: α -> α -> Prop}

instance instAddMonoidOps [AddMonoidOps α] [IsAddMonoid α] : AddMonoidOps (AddGroupQuot r) :=
  AlgQuotient.instAddMonoidOps _
instance instIsSemiring [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid (AddGroupQuot r) :=
  AlgQuotient.instIsAddMonoid _

instance instAddGroupOps [AddGroupOps α] [IsAddGroup α] : AddGroupOps (AddGroupQuot r) :=
  AlgQuotient.instAddGroupOps _
instance instIsAddGroup [AddGroupOps α] [IsAddGroup α] : IsAddGroup (AddGroupQuot r) :=
  AlgQuotient.instIsAddGroup _

instance instIsAddCommMagma [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] : IsAddCommMagma (AddGroupQuot r) :=
  AlgQuotient.instIsAddCommMagma _

end

variable {r: G -> G -> Prop}

def mk [AddMonoidOps G] [IsAddMonoid G] (r: G -> G -> Prop) : G ↠+ AddGroupQuot r :=
  AddCon.mkQuot _

@[induction_eliminator]
def ind [AddMonoidOps G] [IsAddMonoid G] {motive: AddGroupQuot r -> Prop} (mk: ∀x, motive (mk r x)) : ∀q, motive q := by
  intro q
  obtain ⟨_, rfl⟩ := (AddGroupQuot.mk r).surj q
  apply mk

def mk_rel [AddMonoidOps G] [IsAddMonoid G] (w: r x y) : mk r x = mk r y := Quot.sound (AddCon.Generator.of w)

private def preLift [AddMonoidOps G] [IsAddMonoid G] [AddMonoidOps T] [IsAddMonoid T] {r : G → G → Prop} {f : G →+ T} (h : ∀ ⦃x y⦄, r x y → f x = f y) : AddGroupQuot r →+ T where
  toFun := by
    refine  Quotient.lift f ?_
    intro a b g
    induction g with
    | of =>
      apply h
      assumption
    | refl => rfl
    | symm => symm; assumption
    | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
    | add =>
      rw [map_add, map_add]
      congr
  map_zero := map_zero f
  map_add := by
    intro a b
    induction a; induction b
    apply map_add

def lift [AddMonoidOps G] [IsAddMonoid G] [AddMonoidOps T] [IsAddMonoid T]: {f: G →+ T // ∀ ⦃x y⦄, r x y → f x = f y } ≃ (AddGroupQuot r →+ T) where
  toFun f := preLift f.property
  invFun f := {
    val := f.comp (mk r)
    property := by
      intro x y h
      show f (mk r x) = f (mk r y)
      congr 1; apply mk_rel
      assumption
  }
  leftInv _ := rfl
  rightInv f := by
    ext x; induction x
    rfl

def lift_exp [AddMonoidOps G] [IsAddMonoid G] [MonoidOps T] [IsMonoid T]: {f: G →ₐ* T // ∀ ⦃x y⦄, r x y → f x = f y } ≃ (AddGroupQuot r →ₐ* T) := by
  apply Equiv.congrEquiv _ _ (lift (G := G) (T := AddOfMul T) (r := r))
  refine Equiv.congrSubtype ?_ ?_
  exact Equiv.exp_hom_equiv_addgroup_hom.symm
  rfl
  exact Equiv.exp_hom_equiv_addgroup_hom.symm

@[simp]
def lift_mk_apply [AddMonoidOps G] [IsAddMonoid G] [AddMonoidOps T] [IsAddMonoid T] (f : G →+ T) {r : G → G → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
    lift ⟨f, w⟩ (mk r x) = f x := rfl

@[simp]
def symm_lift_mk_apply [AddMonoidOps G] [IsAddMonoid G] [AddMonoidOps T] [IsAddMonoid T] {r: G -> G -> Prop} (f : AddGroupQuot r →+ T) (x: G) :
    (lift.symm f).val x = f (mk r x) := rfl

@[simp]
def lift_exp_mk_apply [AddMonoidOps G] [IsAddMonoid G] [MonoidOps T] [IsMonoid T] (f : G →ₐ* T) {r : G → G → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
    lift_exp ⟨f, w⟩ (mk r x) = f x := rfl

@[simp]
def symm_lift_exp_mk_apply [AddMonoidOps G] [IsAddMonoid G] [MonoidOps T] [IsMonoid T] {r: G -> G -> Prop} (f : AddGroupQuot r →ₐ* T) (x: G) :
    (lift_exp.symm f).val x = f (mk r x) := rfl

def mkQuot_eq_mk [AddMonoidOps G] [IsAddMonoid G] : AddCon.mkQuot (AddGroupQuot.Con r) = AddGroupQuot.mk r := rfl

attribute [irreducible] GroupQuot mk lift

end AddGroupQuot
