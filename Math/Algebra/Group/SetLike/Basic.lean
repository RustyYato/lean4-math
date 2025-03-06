import Math.Algebra.Group.SetLike.Defs
import Math.Algebra.Monoid.SetLike.Basic
import Math.Algebra.Group.Defs
import Math.Algebra.Group.Hom

variable [SetLike S α]

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

def Subgroup.kernel [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β] (f: α →* β) : Subgroup α where
  carrier := Set.preimage {1} f
  mem_one' := resp_one _
  mem_inv' := by
    intro _ ha
    rw [Set.mem_preimage, resp_inv, ha, inv_one]; rfl
  mem_mul' := by
    intro a b ha hb
    rw [Set.mem_preimage, resp_mul, ha, hb, one_mul]; rfl

def AddSubgroup.kernel [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β] (f: α →+ β) : AddSubgroup α where
  carrier := Set.preimage {0} f
  mem_zero' := resp_zero _
  mem_neg' := by
    intro _ ha
    rw [Set.mem_preimage, resp_neg, ha, neg_zero]; rfl
  mem_add' := by
    intro a b ha hb
    rw [Set.mem_preimage, resp_add, ha, hb, zero_add]; rfl

def Subgroup.embed (S: Subgroup α) : S ↪* α where
  toFun x := x.val
  inj' := Subtype.val_inj
  resp_one := rfl
  resp_mul := rfl

def AddSubgroup.embed (S: AddSubgroup α) : S ↪+ α where
  toFun x := x.val
  inj' := Subtype.val_inj
  resp_zero := rfl
  resp_add := rfl

def Subgroup.of_hom [GroupOps β] [IsGroup β] (h: α →* β) : Subgroup β where
  carrier := Set.range h
  mem_one' := by
    apply Set.mem_range.mpr
    exists 1; rw [resp_one]
  mem_mul' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    apply Set.mem_range.mpr
    exists a * b
    rw [resp_mul]
  mem_inv' := by
    rintro _ ⟨a, rfl⟩
    apply Set.mem_range.mpr
    exists a⁻¹
    rw [resp_inv]

def AddSubgroup.of_hom [AddGroupOps β] [IsAddGroup β] (h: α →+ β) : AddSubgroup β where
  carrier := Set.range h
  mem_zero' := by
    apply Set.mem_range.mpr
    exists 0; rw [resp_zero]
  mem_add' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    apply Set.mem_range.mpr
    exists a + b
    rw [resp_add]
  mem_neg' := by
    rintro _ ⟨a, rfl⟩
    apply Set.mem_range.mpr
    exists -a
    rw [resp_neg]

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
  resp_one := by
    dsimp; congr
    rw [resp_one]
  resp_mul := by
    intro a b
    dsimp; congr
    rw [resp_mul]

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
  resp_zero := by
    dsimp; congr
    rw [resp_zero]
  resp_add := by
    intro a b
    dsimp; congr
    rw [resp_add]
