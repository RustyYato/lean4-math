import Math.Algebra.Group.SetLike.Defs
import Math.Algebra.Monoid.SetLike.Basic
import Math.Algebra.Group.Defs
import Math.Algebra.Group.Hom

variable [SetLike S α]

instance [AddGroupOps α] [IsAddGroup α] : Bot (AddSubgroup α) where
  bot := {
    carrier := {0}
    mem_zero := rfl
    mem_add := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
    mem_neg := by
      rintro _ rfl
      rw [neg_zero]; rfl
  }

instance [GroupOps α] [IsGroup α] : Bot (Subgroup α) where
  bot := {
    carrier := {1}
    mem_one := rfl
    mem_mul := by
      rintro _ _ rfl rfl
      rw [mul_one]; rfl
    mem_inv := by
      rintro _ rfl
      rw [inv_one]; rfl
  }

instance [GroupOps α] [IsGroup α] : Top (Subgroup α) where
  top := {
    carrier := ⊤
    mem_one := True.intro
    mem_mul _ _ := True.intro
    mem_inv _ := True.intro
  }

instance [AddGroupOps α] [IsAddGroup α] : Top (AddSubgroup α) where
  top := {
    carrier := ⊤
    mem_zero := True.intro
    mem_add _ _ := True.intro
    mem_neg _ := True.intro
  }

def mem_div
  [SetLike S α] [GroupOps α] [IsSubgroup S] [IsGroup α]
  (s: S) {a b: α} (ha: a ∈ s) (hb: b ∈ s) : a / b ∈ s := by
  rw [div_eq_mul_inv]
  apply mem_mul
  assumption
  apply mem_inv
  assumption

def mem_zpow
  [SetLike S α] [GroupOps α] [IsSubgroup S] [IsGroup α]
  (s: S) {a: α} (n: ℤ) (ha: a ∈ s) : a ^ n ∈ s := by
  cases n using Int.coe_cases
  rw [zpow_ofNat]
  apply mem_npow
  assumption
  rw [zpow_negSucc]
  apply mem_inv
  apply mem_npow
  assumption

def mem_sub
  [SetLike S α] [AddGroupOps α] [IsAddSubgroup S] [IsAddGroup α]
  (s: S) {a b: α} (ha: a ∈ s) (hb: b ∈ s) : a - b ∈ s :=
  mem_div (S := MulOfAdd S) s ha hb

def mem_zsmul
  [SetLike S α] [AddGroupOps α] [IsAddSubgroup S] [IsAddGroup α]
  (s: S) {a: α} (n: ℤ) (ha: a ∈ s) : n • a ∈ s :=
  mem_zpow (S := MulOfAdd S) s n ha

section

variable [Mul α] [One α] [Inv α] [IsSubgroup S] [Add α] [Zero α] [Neg α] [IsAddSubgroup S] (s: S)

instance : Inv s where
  inv a := ⟨a.val⁻¹, mem_inv _ a.property⟩

instance : Neg s where
  neg a := ⟨-a.val, mem_neg _ a.property⟩

instance [IsInvolutiveInv α] : IsInvolutiveInv s where
  inv_inv a := by
    apply Subtype.val_inj
    apply inv_inv

instance [IsInvolutiveNeg α] : IsInvolutiveNeg s where
  neg_neg a := by
    apply Subtype.val_inj
    apply neg_neg

instance [IsInvOneClass α] : IsInvOneClass s where
  inv_one := by
    apply Subtype.val_inj
    apply inv_one

instance [IsNegZeroClass α] : IsNegZeroClass s where
  neg_zero := by
    apply Subtype.val_inj
    apply neg_zero

end

variable [GroupOps α] [IsGroup α] [IsSubgroup S] [AddGroupOps α] [IsAddGroup α] [IsAddSubgroup S] (s: S)

instance : Div s where
  div a b := ⟨a.val / b.val, mem_div _ a.property b.property⟩

instance : Sub s where
  sub a b := ⟨a.val - b.val, mem_sub _ a.property b.property⟩

instance : Pow s ℤ where
  pow a n := ⟨a.val ^ n, mem_zpow _ _ a.property⟩

instance : SMul ℤ s where
  smul n a := ⟨n • a.val, mem_zsmul _ _ a.property⟩

instance : IsGroup s where
  div_eq_mul_inv _ _ := by
    apply Subtype.val_inj
    apply div_eq_mul_inv
  inv_mul_cancel _ := by
    apply Subtype.val_inj
    apply inv_mul_cancel
  zpow_ofNat _ _ := by
    apply Subtype.val_inj
    apply zpow_ofNat
  zpow_negSucc _ _ := by
    apply Subtype.val_inj
    apply zpow_negSucc

instance : IsAddGroup s where
  sub_eq_add_neg _ _ := by
    apply Subtype.val_inj
    apply sub_eq_add_neg
  neg_add_cancel _ := by
    apply Subtype.val_inj
    apply neg_add_cancel
  zsmul_ofNat _ _ := by
    apply Subtype.val_inj
    apply zsmul_ofNat
  zsmul_negSucc _ _ := by
    apply Subtype.val_inj
    apply zsmul_negSucc

instance (s: Subgroup α) : IsGroup s := inferInstance
instance (s: AddSubgroup α) : IsAddGroup s := inferInstance

def Subgroup.preimage [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β] (f: α →* β) (s: Subgroup β) : Subgroup α where
  carrier := Set.preimage s f
  mem_one := by
    rw [Set.mem_preimage, map_one]
    apply mem_one s
  mem_inv := by
    intro _ ha
    rw [Set.mem_preimage, map_inv]
    apply mem_inv s
    assumption
  mem_mul := by
    intro a b ha hb
    rw [Set.mem_preimage, map_mul]
    apply mem_mul s
    assumption
    assumption

def AddSubgroup.preimage [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β] (f: α →+ β) (s: AddSubgroup β) : AddSubgroup α where
  carrier := Set.preimage s f
  mem_zero := by
    rw [Set.mem_preimage, map_zero]
    apply mem_zero s
  mem_neg := by
    intro _ ha
    rw [Set.mem_preimage, map_neg]
    apply mem_neg s
    assumption
  mem_add := by
    intro a b ha hb
    rw [Set.mem_preimage, map_add]
    apply mem_add s
    assumption
    assumption

def Subgroup.image [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β] (f: α →* β) (s: Subgroup α) : Subgroup β where
  carrier := Set.image f s
  mem_one := by
    rw [←map_one f]
    apply Set.mem_image'
    apply mem_one s
  mem_inv := by
    rintro _ ⟨a, ha, rfl⟩
    rw [←map_inv]
    apply Set.mem_image'
    apply mem_inv s
    assumption
  mem_mul := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [←map_mul]
    apply Set.mem_image'
    apply mem_mul s
    assumption
    assumption

def AddSubgroup.image [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β] (f: α →+ β) (s: AddSubgroup α) : AddSubgroup β where
  carrier := Set.image f s
  mem_zero := by
    rw [←map_zero f]
    apply Set.mem_image'
    apply mem_zero s
  mem_neg := by
    rintro _ ⟨a, ha, rfl⟩
    rw [←map_neg]
    apply Set.mem_image'
    apply mem_neg s
    assumption
  mem_add := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [←map_add]
    apply Set.mem_image'
    apply mem_add s
    assumption
    assumption

def Subgroup.range [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β] (f: α →* β) : Subgroup β where
  carrier := Set.range f
  mem_one := by
    rw [←map_one f]
    apply Set.mem_range'
  mem_inv := by
    rintro _ ⟨a, ha, rfl⟩
    rw [←map_inv]
    apply Set.mem_range'
  mem_mul := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [←map_mul]
    apply Set.mem_range'

def AddSubgroup.range [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β] (f: α →+ β) : AddSubgroup β where
  carrier := Set.range f
  mem_zero := by
    rw [←map_zero f]
    apply Set.mem_range'
  mem_neg := by
    rintro _ ⟨a, ha, rfl⟩
    rw [←map_neg]
    apply Set.mem_range'
  mem_add := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [←map_add]
    apply Set.mem_range'

def Subgroup.kernel [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β] (f: α →* β) : Subgroup α := preimage f ⊥
def AddSubgroup.kernel [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β] (f: α →+ β) : AddSubgroup α  := preimage f ⊥

def Subgroup.embed (S: Subgroup α) : S ↪* α where
  toFun x := x.val
  inj' := Subtype.val_inj
  map_one := rfl
  map_mul := rfl

def AddSubgroup.embed (S: AddSubgroup α) : S ↪+ α where
  toFun x := x.val
  inj' := Subtype.val_inj
  map_zero := rfl
  map_add := rfl

def Subgroup.of_hom [GroupOps β] [IsGroup β] (h: α →* β) : Subgroup β where
  carrier := Set.range h
  mem_one := by
    apply Set.mem_range.mpr
    exists 1; rw [map_one]
  mem_mul := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    apply Set.mem_range.mpr
    exists a * b
    rw [map_mul]
  mem_inv := by
    rintro _ ⟨a, rfl⟩
    apply Set.mem_range.mpr
    exists a⁻¹
    rw [map_inv]

def AddSubgroup.of_hom [AddGroupOps β] [IsAddGroup β] (h: α →+ β) : AddSubgroup β where
  carrier := Set.range h
  mem_zero := by
    apply Set.mem_range.mpr
    exists 0; rw [map_zero]
  mem_add := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    apply Set.mem_range.mpr
    exists a + b
    rw [map_add]
  mem_neg := by
    rintro _ ⟨a, rfl⟩
    apply Set.mem_range.mpr
    exists -a
    rw [map_neg]

noncomputable
def Subgroup.equiv_of_embed [GroupOps β] [IsGroup β] (h: α ↪* β) : α ≃* Subgroup.of_hom (toGroupHom h) where
  toFun a := ⟨h a, Set.mem_range'⟩
  invFun x := Classical.choose x.property
  leftInv := by
    intro x
    dsimp
    apply h.inj
    have : h x ∈ Set.range h := Set.mem_range'
    exact (Classical.choose_spec this).symm
  rightInv := by
    intro x
    dsimp
    congr
    exact (Classical.choose_spec x.property).symm
  map_one := by
    congr
    rw [map_one]
  map_mul := by
    intro a b
    congr
    rw [map_mul]

noncomputable
def AddSubgroup.equiv_of_embed [AddGroupOps β] [IsAddGroup β] (h: α ↪+ β) : α ≃+ AddSubgroup.of_hom (toAddGroupHom h) where
  toFun a := ⟨h a, Set.mem_range'⟩
  invFun x := Classical.choose x.property
  leftInv := by
    intro x
    dsimp
    apply h.inj
    have : h x ∈ Set.range h := Set.mem_range'
    exact (Classical.choose_spec this).symm
  rightInv := by
    intro x
    dsimp
    congr
    exact (Classical.choose_spec x.property).symm
  map_zero := by
    congr
    rw [map_zero]
  map_add := by
    intro a b
    congr
    rw [map_add]

@[simp]
def neg_val (a: s) : (-a).val = -a.val := rfl

@[simp]
def inv_val (a: s) : (a⁻¹).val = a.val⁻¹ := rfl

@[simp]
def sub_val (a b: s) : (a - b).val = a.val - b.val := rfl

@[simp]
def div_val (a b: s) : (a / b).val = a.val / b.val := rfl

@[simp]
def zsmul_val (n: ℤ) (a: s) : (n • a).val = n • a.val := rfl

@[simp]
def zpow_val (n: ℤ) (a: s) : (a ^ n).val = a.val ^ n := rfl
