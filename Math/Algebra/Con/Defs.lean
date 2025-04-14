import Math.Data.Like.Func
import Math.Relation.Basic
import Math.Algebra.Notation
import Math.Algebra.AddMul
import Math.Order.OrderIso
import Math.Relation.Order

section Algebra

class IsCon (C: Sort*) {α: Type*} [RelLike C α]: Prop where
  protected toEquivalence (c: C): Equivalence c := by intro c; exact c.iseqv

class IsAddCon (C: Sort*) {α: Type*} [RelLike C α] [Add α]: Prop extends IsCon C where
  protected resp_add (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w + x) (y + z) := by intro c; exact c.resp_add

class IsMulCon (C: Sort*) {α: Type*} [RelLike C α] [Mul α]: Prop extends IsCon C where
  protected resp_mul (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w * x) (y * z) := by intro c; exact c.resp_mul

class IsSMulCon (C: Sort*) (R: Type*) {α: Type*} [RelLike C α] [SMul R α]: Prop extends IsCon C where
  protected resp_smul (c: C): ∀(r: R) {x y: α}, c x y -> c (r • x) (r • y) := by intro c; exact c.resp_smul

class IsRingCon (F: Sort*) {α: Type*} [RelLike F α] [Add α] [Mul α]: Prop extends IsAddCon F, IsMulCon F where

instance [Add α] [Mul α] [RelLike F α] [IsMulCon F] [IsAddCon F] : IsRingCon F := {
  inferInstanceAs (IsMulCon F), inferInstanceAs (IsAddCon F) with
}

def resp_add [RelLike C α] [Add α] [IsAddCon C] (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w + x) (y + z) := IsAddCon.resp_add _
def resp_mul [RelLike C α] [Mul α] [IsMulCon C] (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w * x) (y * z) := IsMulCon.resp_mul _
def resp_smul [RelLike C α] [SMul R α] [IsSMulCon C R] (c: C): ∀(r: R) {x y: α}, c x y -> c (r • x) (r • y) := IsSMulCon.resp_smul _
def IsCon.toSetoid [RelLike C α] [IsCon C] (c: C) : Setoid α where
  r := c
  iseqv := IsCon.toEquivalence c

instance : RelLike (Setoid α) α where
  coe s := s.r

structure AddCon (α: Type*) [Add α] extends Setoid α where
  protected resp_add: ∀{a b c d: α}, r a c -> r b d -> r (a + b) (c + d)

instance [Add α] : RelLike (AddCon α) α where
  coe f := f.r

instance [Add α] : IsAddCon (AddCon α) where

structure SMulCon (R α: Type*) [SMul R α] extends Setoid α where
  protected resp_smul: ∀(s: R) {x y: α}, r x y -> r (s • x) (s • y)

instance [SMul R α] : RelLike (SMulCon R α) α where
  coe f := f.r

instance [SMul R α] : IsSMulCon (SMulCon R α) R where

structure MulCon (α: Type*) [Mul α] extends Setoid α where
  protected resp_mul: ∀{a b c d: α}, r a c -> r b d -> r (a * b) (c * d)

instance [Mul α] : RelLike (MulCon α) α where
  coe f := f.r

instance [Mul α] : IsMulCon (MulCon α) where

structure RingCon (α: Type*) [Add α] [Mul α] extends AddCon α, MulCon α where

instance [Add α] [Mul α] : RelLike (RingCon α) α where
  coe f := f.r

instance [Add α] [Mul α] : IsAddCon (RingCon α) where
instance [Add α] [Mul α] : IsMulCon (RingCon α) where

structure LinearCon (R α: Type*) [Add α] [SMul R α] extends AddCon α, SMulCon R α where

instance [Add α] [SMul R α] : RelLike (LinearCon R α) α where
  coe f := f.r

instance [Add α] [SMul R α] : IsAddCon (LinearCon R α) where
instance [Add α] [SMul R α] : IsSMulCon (LinearCon R α) R where

end Algebra

section Order

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

end LinearCon

end Order

section Generator

variable (R: Type*) (r: α -> α -> Prop)

inductive AddCon.Generator [Add α] : α -> α -> Prop where
| of {a b: α} : r a b -> Generator a b
| refl (a: α) : Generator a a
| symm {a b: α} : Generator a b -> Generator b a
| trans {a b c: α} : Generator a b -> Generator b c -> Generator a c
| add {a b c d: α} : Generator a c -> Generator b d -> Generator (a + b) (c + d)

inductive MulCon.Generator [Mul α] : α -> α -> Prop where
| of {a b: α} : r a b -> Generator a b
| refl (a: α) : Generator a a
| symm {a b: α} : Generator a b -> Generator b a
| trans {a b c: α} : Generator a b -> Generator b c -> Generator a c
| mul {a b c d: α} : Generator a c -> Generator b d -> Generator (a * b) (c * d)

inductive SMulCon.Generator [SMul R α] : α -> α -> Prop where
| of {a b: α} : r a b -> Generator a b
| refl (a: α) : Generator a a
| symm {a b: α} : Generator a b -> Generator b a
| trans {a b c: α} : Generator a b -> Generator b c -> Generator a c
| smul (r: R) {a b: α} : Generator a b -> Generator (r • a) (r • b)

inductive RingCon.Generator [Add α] [Mul α] : α -> α -> Prop where
| of {a b: α} : r a b -> Generator a b
| refl (a: α) : Generator a a
| symm {a b: α} : Generator a b -> Generator b a
| trans {a b c: α} : Generator a b -> Generator b c -> Generator a c
| add {a b c d: α} : Generator a c -> Generator b d -> Generator (a + b) (c + d)
| mul {a b c d: α} : Generator a c -> Generator b d -> Generator (a * b) (c * d)

inductive LinearCon.Generator [Add α] [SMul R α] : α -> α -> Prop where
| of {a b: α} : r a b -> Generator a b
| refl (a: α) : Generator a a
| symm {a b: α} : Generator a b -> Generator b a
| trans {a b c: α} : Generator a b -> Generator b c -> Generator a c
| add {a b c d: α} : Generator a c -> Generator b d -> Generator (a + b) (c + d)
| smul (r: R) {a b: α} : Generator a b -> Generator (r • a) (r • b)

def AddCon.generate [Add α] (r: α -> α -> Prop) : AddCon α where
  r := Generator r
  iseqv := {
    refl := Generator.refl
    symm := Generator.symm
    trans := Generator.trans
  }
  resp_add := Generator.add

def MulCon.generate [Mul α] (r: α -> α -> Prop) : MulCon α where
  r := Generator r
  iseqv := {
    refl := Generator.refl
    symm := Generator.symm
    trans := Generator.trans
  }
  resp_mul := Generator.mul

def SMulCon.generate (R: Type*) [SMul R α] (r: α -> α -> Prop) : SMulCon R α where
  r := Generator R r
  iseqv := {
    refl := Generator.refl
    symm := Generator.symm
    trans := Generator.trans
  }
  resp_smul := Generator.smul

def RingCon.generate [Add α] [Mul α] (r: α -> α -> Prop) : RingCon α where
  r := Generator r
  iseqv := {
    refl := Generator.refl
    symm := Generator.symm
    trans := Generator.trans
  }
  resp_add := Generator.add
  resp_mul := Generator.mul

def LinearCon.generate (R: Type*) [Add α] [SMul R α] (r: α -> α -> Prop) : LinearCon R α where
  r := Generator R r
  iseqv := {
    refl := Generator.refl
    symm := Generator.symm
    trans := Generator.trans
  }
  resp_add := Generator.add
  resp_smul := Generator.smul

def AddCon.ofGenerate [Add α] [RelLike C α] [IsAddCon C] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate r a b -> c a b := by
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

def AddCon.le_generate [Add α] (r: α -> α -> Prop) : r ≤ generate r := by
  intro x y h
  apply Generator.of
  assumption

def MulCon.ofGenerate [Mul α] [RelLike C α] [IsMulCon C] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate r a b -> c a b := by
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

def MulCon.le_generate [Mul α] (r: α -> α -> Prop) : r ≤ generate r := by
  intro x y h
  apply Generator.of
  assumption

def SMulCon.ofGenerate [SMul R α] [RelLike C α] [IsSMulCon C R] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate R r a b -> c a b := by
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

def SMulCon.le_generate [SMul R α] (r: α -> α -> Prop) : r ≤ generate R r := by
  intro x y h
  apply Generator.of
  assumption

def RingCon.ofGenerate [Add α] [Mul α] [RelLike C α] [IsRingCon C] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate r a b -> c a b := by
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

def RingCon.le_generate [Add α] [Mul α] (r: α -> α -> Prop) : r ≤ generate r := by
  intro x y h
  apply Generator.of
  assumption

def LinearCon.ofGenerate  [Add α] [SMul R α] [RelLike C α] [IsAddCon C] [IsSMulCon C R] (r: α -> α -> Prop) (c: C) (h: r ≤ c) : ∀a b, generate R r a b -> c a b := by
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

def LinearCon.le_generate [Add α] [SMul R α] (r: α -> α -> Prop) : r ≤ generate R r := by
  intro x y h
  apply Generator.of
  assumption

def AddCon.copy [Add α] [RelLike C α] [IsAddCon C] (c: C) (r: α -> α -> Prop) (h: r = c) : AddCon α where
  r := r
  iseqv := by rw [h]; exact IsCon.toEquivalence c
  resp_add {_ _ _ _} := by simp [h]; exact IsAddCon.resp_add c

def MulCon.copy [Mul α] [RelLike C α] [IsMulCon C] (c: C) (r: α -> α -> Prop) (h: r = c) : MulCon α where
  r := r
  iseqv := by rw [h]; exact IsCon.toEquivalence c
  resp_mul {_ _ _ _} := by simp [h]; exact IsMulCon.resp_mul c

def SMulCon.copy [SMul R α] [RelLike C α] [IsSMulCon C R] (c: C) (r: α -> α -> Prop) (h: r = c) : SMulCon R α where
  r := r
  iseqv := by rw [h]; exact IsCon.toEquivalence c
  resp_smul {_ _ _} := by simp [h]; apply IsSMulCon.resp_smul c

def RingCon.copy [Add α] [Mul α] [RelLike C α] [IsRingCon C] (c: C) (r: α -> α -> Prop) (h: r = c) : RingCon α where
  r := r
  iseqv := by rw [h]; exact IsCon.toEquivalence c
  resp_add {_ _ _ _} := by simp [h]; exact IsAddCon.resp_add c
  resp_mul {_ _ _ _} := by simp [h]; exact IsMulCon.resp_mul c

def LinearCon.copy [Add α] [SMul R α] [RelLike C α] [IsAddCon C] [IsSMulCon C R] (c: C) (r: α -> α -> Prop) (h: r = c) : LinearCon R α where
  r := r
  iseqv := by rw [h]; exact IsCon.toEquivalence c
  resp_add {_ _ _ _} := by simp [h]; exact IsAddCon.resp_add c
  resp_smul {_ _ _} := by simp [h]; apply IsSMulCon.resp_smul c

end Generator

section Quotient

variable {C α: Type*} [RelLike C α]

instance : RelLike (MulOfAdd C) (MulOfAdd α) := inferInstanceAs (RelLike C α)
instance : RelLike (AddOfMul C) (AddOfMul α) := inferInstanceAs (RelLike C α)
instance : RelLike (Cᵃᵒᵖ) (αᵃᵒᵖ) := inferInstanceAs (RelLike C α)
instance : RelLike (Cᵐᵒᵖ) (αᵐᵒᵖ) := inferInstanceAs (RelLike C α)

instance [Add α] [IsAddCon C] : IsMulCon (MulOfAdd C) where
  resp_mul := resp_add (C := C)
  toEquivalence := IsCon.toEquivalence (C := C)
instance [Mul α] [IsMulCon C] : IsAddCon (AddOfMul C) where
  resp_add := resp_mul (C := C)
  toEquivalence := IsCon.toEquivalence (C := C)

instance [IsCon C] : IsCon (Cᵃᵒᵖ) := inferInstanceAs (IsCon C)
instance [IsCon C] : IsCon (Cᵐᵒᵖ) := inferInstanceAs (IsCon C)

instance [Add α] [IsAddCon C] : IsAddCon (Cᵃᵒᵖ) where
  resp_add := by
    intro c w x y z h g
    apply resp_add (C := C)
    assumption
    assumption
instance [Add α] [IsAddCon C] : IsAddCon (Cᵐᵒᵖ) := inferInstanceAs (IsAddCon C)

instance [Mul α] [IsMulCon C] : IsMulCon (Cᵃᵒᵖ) := inferInstanceAs (IsMulCon C)
instance [Mul α] [IsMulCon C] : IsMulCon (Cᵐᵒᵖ) where
  resp_mul := by
    intro c w x y z h g
    apply resp_mul (C := C)
    assumption
    assumption

instance [Add α] [Mul α] [IsRingCon C] : IsRingCon (Cᵃᵒᵖ) := {
  instIsAddConAddOpp, instIsMulConAddOpp with
}

instance [Add α] [Mul α] [IsRingCon C] : IsRingCon (Cᵐᵒᵖ) := {
  instIsAddConMulOpp, instIsMulConMulOpp with
}

protected def IsCon.Quotient [IsCon C] (c: C) : Type _ := Quotient (IsCon.toSetoid c)

def IsCon.mkQuot [IsCon C] (c: C) : α -> IsCon.Quotient c := Quotient.mk _

@[induction_eliminator]
def IsCon.Quotient.ind [IsCon C] {c: C}
  {motive: IsCon.Quotient c -> Prop}
  (mk: ∀x, motive (IsCon.mkQuot c x))
  (a: IsCon.Quotient c) : motive a := _root_.Quotient.ind mk a

instance [Add α] [IsAddCon C] (c: C) : Add (IsCon.Quotient c) where
  add := by
    apply Quotient.lift₂ (fun a b => IsCon.mkQuot c (a + b))
    intro w x y z wy xz
    apply Quotient.sound
    apply IsAddCon.resp_add
    assumption
    assumption

instance [Mul α] [IsMulCon C] (c: C) : Mul (IsCon.Quotient c) where
  mul := by
    apply Quotient.lift₂ (fun a b => IsCon.mkQuot c (a * b))
    intro w x y z wy xz
    apply Quotient.sound
    apply IsMulCon.resp_mul
    assumption
    assumption

instance [SMul R α] [IsSMulCon C R] (c: C) : SMul R (IsCon.Quotient c) where
  smul r := by
    apply Quotient.lift (fun a => IsCon.mkQuot c (r • a))
    intro x y h
    apply Quotient.sound
    apply IsSMulCon.resp_smul
    assumption

variable [IsCon C] (c: C)

instance : Relation.IsRefl c where
  refl := (IsCon.toEquivalence c).refl
instance : Relation.IsSymmetric c where
  symm := (IsCon.toEquivalence c).symm
instance : Relation.IsTrans c where
  trans := (IsCon.toEquivalence c).trans

instance [Zero α] : Zero (IsCon.Quotient c) where
  zero := IsCon.mkQuot _ 0
instance [One α] : One (IsCon.Quotient c) where
  one := IsCon.mkQuot _ 1
instance [NatCast α] : NatCast (IsCon.Quotient c) where
  natCast n := IsCon.mkQuot _ n
instance [IntCast α] : IntCast (IsCon.Quotient c) where
  intCast n := IsCon.mkQuot _ n

end Quotient
