import Math.Algebra.Con.Defs
import Math.Order.OrderIso
import Math.Relation.Order

namespace AddCon

variable [Add α]

instance : LE (AddCon α) where
  le a b := ∀x y, a x y -> b x y
instance : LT (AddCon α) where
  lt a b := a.r < b.r

instance : IsLawfulLT (AddCon α) where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := α -> α -> Prop)

def orderEmbed : AddCon α ↪o (α -> α -> Prop) where
  toFun a := a.r
  inj' a b h := by
    rcases a with ⟨⟨a, _⟩, _⟩
    rcases b with ⟨⟨b, _⟩, _⟩
    congr
  map_le _ _ := Iff.rfl

instance : IsPartialOrder (AddCon α) :=
  orderEmbed.instIsPartialOrder'

def ofGenerate [Add α] [RelLike C α] [IsAddCon C] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate r a b -> c a b := by
  intro a b g
  induction g
  apply h; assumption
  apply (IsCon.toEquivalence c).refl
  apply (IsCon.toEquivalence c).symm
  assumption
  apply (IsCon.toEquivalence c).trans
  assumption
  assumption
  apply IsAddCon.resp_add
  assumption
  assumption

def le_generate [Add α] (r: α -> α -> Prop) : r ≤ generate r := by
  intro x y h
  apply Generator.of
  assumption
end AddCon

namespace MulCon

variable [Mul α]

instance : LE (MulCon α) where
  le a b := ∀x y, a x y -> b x y
instance : LT (MulCon α) where
  lt a b := a.r < b.r

instance : IsLawfulLT (MulCon α) where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := α -> α -> Prop)

def orderEmbed : MulCon α ↪o (α -> α -> Prop) where
  toFun a := a.r
  inj' a b h := by
    rcases a with ⟨⟨a, _⟩, _⟩
    rcases b with ⟨⟨b, _⟩, _⟩
    congr
  map_le _ _ := Iff.rfl

instance : IsPartialOrder (MulCon α) :=
  orderEmbed.instIsPartialOrder'

def ofGenerate [Mul α] [RelLike C α] [IsMulCon C] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate r a b -> c a b := by
  intro a b g
  induction g
  apply h; assumption
  apply (IsCon.toEquivalence c).refl
  apply (IsCon.toEquivalence c).symm
  assumption
  apply (IsCon.toEquivalence c).trans
  assumption
  assumption
  apply IsMulCon.resp_mul
  assumption
  assumption

def le_generate [Mul α] (r: α -> α -> Prop) : r ≤ generate r := by
  intro x y h
  apply Generator.of
  assumption

end MulCon

namespace SMulCon

variable [SMul R α]

instance : LE (SMulCon R α) where
  le a b := ∀x y, a x y -> b x y
instance : LT (SMulCon R α) where
  lt a b := a.r < b.r

instance : IsLawfulLT (SMulCon R α) where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := α -> α -> Prop)

def orderEmbed : SMulCon R α ↪o (α -> α -> Prop) where
  toFun a := a.r
  inj' a b h := by
    rcases a with ⟨⟨a, _⟩, _⟩
    rcases b with ⟨⟨b, _⟩, _⟩
    congr
  map_le _ _ := Iff.rfl

instance : IsPartialOrder (SMulCon R α) :=
  orderEmbed.instIsPartialOrder'

variable (R: Type*) [SMul R α]

def ofGenerate [SMul R α] [RelLike C α] [IsSMulCon C R] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate R r a b -> c a b := by
  intro a b g
  induction g
  apply h; assumption
  apply (IsCon.toEquivalence c).refl
  apply (IsCon.toEquivalence c).symm
  assumption
  apply (IsCon.toEquivalence c).trans
  assumption
  assumption
  apply IsSMulCon.resp_smul
  assumption

def le_generate [SMul R α] (r: α -> α -> Prop) : r ≤ generate R r := by
  intro x y h
  apply Generator.of
  assumption

end SMulCon

namespace RingCon

variable [Add α] [Mul α]

instance : LE (RingCon α) where
  le a b := ∀x y, a x y -> b x y
instance : LT (RingCon α) where
  lt a b := a.r < b.r

instance : IsLawfulLT (RingCon α) where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := α -> α -> Prop)

def orderEmbed : RingCon α ↪o (α -> α -> Prop) where
  toFun a := a.r
  inj' a b h := by
    rcases a with ⟨⟨⟨a, _⟩, _⟩, _⟩
    rcases b with ⟨⟨⟨b, _⟩, _⟩, _⟩
    congr
  map_le _ _ := Iff.rfl

instance : IsPartialOrder (RingCon α) :=
  orderEmbed.instIsPartialOrder'

def ofGenerate [Add α] [Mul α] [RelLike C α] [IsAddCon C] [IsMulCon C] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate r a b -> c a b := by
  intro a b g
  induction g
  apply h; assumption
  apply (IsCon.toEquivalence c).refl
  apply (IsCon.toEquivalence c).symm
  assumption
  apply (IsCon.toEquivalence c).trans
  assumption
  assumption
  apply IsAddCon.resp_add
  assumption
  assumption
  apply IsMulCon.resp_mul
  assumption
  assumption

def le_generate [Add α] [Mul α] (r: α -> α -> Prop) : r ≤ generate r := by
  intro x y h
  apply Generator.of
  assumption

end RingCon

namespace LinearCon

variable [Add α] [SMul R α]

instance : LE (LinearCon R α) where
  le a b := ∀x y, a x y -> b x y
instance : LT (LinearCon R α) where
  lt a b := a.r < b.r

instance : IsLawfulLT (LinearCon R α) where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := α -> α -> Prop)

def orderEmbed : LinearCon R α ↪o (α -> α -> Prop) where
  toFun a := a.r
  inj' a b h := by
    rcases a with ⟨⟨⟨a, _⟩, _⟩, _⟩
    rcases b with ⟨⟨⟨b, _⟩, _⟩, _⟩
    congr
  map_le _ _ := Iff.rfl

instance : IsPartialOrder (LinearCon R α) :=
  orderEmbed.instIsPartialOrder'

variable (R: Type*) [SMul R α]

def ofGenerate [Add α] [SMul R α] [RelLike C α] [IsAddCon C] [IsSMulCon C R] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate R r a b -> c a b := by
  intro a b g
  induction g
  apply h; assumption
  apply (IsCon.toEquivalence c).refl
  apply (IsCon.toEquivalence c).symm
  assumption
  apply (IsCon.toEquivalence c).trans
  assumption
  assumption
  apply IsAddCon.resp_add
  assumption
  assumption
  apply IsSMulCon.resp_smul
  assumption

def le_generate [Add α] [SMul R α] (r: α -> α -> Prop) : r ≤ generate R r := by
  intro x y h
  apply Generator.of
  assumption

end LinearCon
