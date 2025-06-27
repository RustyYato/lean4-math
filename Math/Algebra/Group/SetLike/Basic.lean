import Math.Algebra.Group.SetLike.Defs
import Math.Algebra.Monoid.SetLike.Basic
import Math.Data.Set.Equiv
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

def mem_npow_natAbs_of_mem_zpow
  [SetLike S α] [GroupOps α] [IsSubgroup S] [IsGroup α]
  (s: S) {a: α} (n: ℤ) : a ^ n ∈ s -> a ^ n.natAbs ∈ s := by
  intro h
  rw [←zpow_ofNat]
  rcases Int.natAbs_eq n with g | g
  rwa [←g]
  rw [←Int.neg_neg (Nat.cast _), zpow_neg, ←g]
  apply mem_inv
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

variable [FunLike F α β]

namespace SubNeg

variable [AddGroupOps α] [AddGroupOps β]
  [IsAddGroup α] [IsSubtractionMonoid β]
  [IsZeroHom F α β] [IsAddHom F α β]

def image (s: SubNeg α) (f: F) : SubNeg β where
  carrier := s.carrier.image f
  mem_neg | ⟨a, ha, _⟩ => ⟨-a, by
    apply And.intro
    apply mem_neg s
    assumption
    rw [map_neg]; congr⟩

def preimage (s: SubNeg β) (f: F) : SubNeg α where
  carrier := s.carrier.preimage f
  mem_neg {a} ha := by show f _ ∈ s; rw [map_neg]; apply mem_neg <;> assumption

def range (f: F) : SubNeg β := (image .univ f).copy (Set.range f) (by symm; apply Set.range_eq_image)

end SubNeg

namespace SubInv

variable [GroupOps α] [GroupOps β]
  [IsGroup α] [IsDivisionMonoid β]
  [IsOneHom F α β] [IsMulHom F α β]

def image (s: SubInv α) (f: F) : SubInv β where
  carrier := s.carrier.image f
  mem_inv | ⟨a, ha, _⟩ => ⟨a⁻¹, by
    apply And.intro
    apply mem_inv s
    assumption
    rw [map_inv]; congr⟩

def preimage (s: SubInv β) (f: F) : SubInv α where
  carrier := s.carrier.preimage f
  mem_inv {a} ha := by show f _ ∈ s; rw [map_inv]; apply mem_inv <;> assumption

def range (f: F) : SubInv β := (image .univ f).copy (Set.range f) (by symm; apply Set.range_eq_image)

end SubInv

section

variable [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β] [IsSubgroup S]
  [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β] [IsAddSubgroup S] (s: S)

instance : Div s where
  div a b := ⟨a.val / b.val, mem_div _ a.property b.property⟩

instance : Sub s where
  sub a b := ⟨a.val - b.val, mem_sub _ a.property b.property⟩

instance : Pow s ℤ where
  pow a n := ⟨a.val ^ n, mem_zpow _ _ a.property⟩

instance : SMul ℤ s where
  smul n a := ⟨n • a.val, mem_zsmul _ _ a.property⟩

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

variable [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β]

def Subgroup.preimage (f: F) (s: Subgroup β) : Subgroup α := {
  s.toSubmonoid.preimage f, s.toSubInv.preimage f with
}

def AddSubgroup.preimage (f: F) (s: AddSubgroup β) : AddSubgroup α := {
  s.toAddSubmonoid.preimage f, s.toSubNeg.preimage f with
}

def Subgroup.image (f: F) (s: Subgroup α) : Subgroup β := {
  s.toSubmonoid.image f, s.toSubInv.image f with
}

def AddSubgroup.image (f: F) (s: AddSubgroup α) : AddSubgroup β := {
  s.toAddSubmonoid.image f, s.toSubNeg.image f with
}

def Subgroup.range (f: F) : Subgroup β := {
  Submonoid.range f, SubInv.range f with
}

def AddSubgroup.range (f: F) : AddSubgroup β := {
  AddSubmonoid.range f, SubNeg.range f with
}

def Subgroup.kernel (f: F) : Subgroup α := preimage f ⊥
def AddSubgroup.kernel (f: F) : AddSubgroup α  := preimage f ⊥

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

def Subgroup.bij_of_embed (f: α ↪* β) : α ⇔* Subgroup.range f where
  toBijection := Bijection.range f.toEmbedding
  map_one := by
    apply Subtype.val_inj
    apply map_one f
  map_mul {x y} := by
    apply Subtype.val_inj
    apply map_mul f

def AddSubgroup.bij_of_embed (f: α ↪+ β) : α ⇔+ AddSubgroup.range f where
  toBijection := Bijection.range f.toEmbedding
  map_zero := by
    apply Subtype.val_inj
    apply map_zero f
  map_add {x y} := by
    apply Subtype.val_inj
    apply map_add f

noncomputable
def Subgroup.equiv_of_embed (f: α ↪* β) : α ≃* Subgroup.range f := {
  Bijection.toEquiv (bij_of_embed f).toBijection, (bij_of_embed f) with
}

noncomputable
def AddSubgroup.equiv_of_embed (f: α ↪+ β) : α ≃+ AddSubgroup.range f := {
  Bijection.toEquiv (bij_of_embed f).toBijection, (bij_of_embed f) with
}

end
