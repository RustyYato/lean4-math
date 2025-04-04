import Math.Data.Like.Func
import Math.Relation.Basic
import Math.Algebra.Notation
import Math.Algebra.AddMul

section Algebra

class IsCon (C: Sort*) {α: Type*} [RelLike C α]: Prop where
  protected toEquivalence (c: C): Equivalence c

class IsAddCon (C: Sort*) {α: Type*} [RelLike C α] [Add α]: Prop extends IsCon C where
  protected resp_add (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w + x) (y + z)

class IsMulCon (C: Sort*) {α: Type*} [RelLike C α] [Mul α]: Prop extends IsCon C where
  protected resp_mul (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w * x) (y * z)

class IsRingCon (F: Sort*) {α: Type*} [RelLike F α] [Add α] [Mul α]: Prop extends IsAddCon F, IsMulCon F where

instance [Add α] [Mul α] [RelLike F α] [IsMulCon F] [IsAddCon F] : IsRingCon F := {
  inferInstanceAs (IsMulCon F), inferInstanceAs (IsAddCon F) with
}

def resp_add [RelLike C α] [Add α] [IsAddCon C] (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w + x) (y + z) := IsAddCon.resp_add _
def resp_mul [RelLike C α] [Mul α] [IsMulCon C] (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w * x) (y * z) := IsMulCon.resp_mul _
def IsCon.toSetoid [RelLike C α] [IsCon C] (c: C) : Setoid α where
  r := c
  iseqv := IsCon.toEquivalence c

instance : RelLike (Setoid α) α where
  coe s := s.r
  coe_inj := by
    intro x y h
    cases x; congr

structure AddCon (α: Type*) [Add α] extends Setoid α where
  protected resp_add: ∀{a b c d: α}, r a c -> r b d -> r (a + b) (c + d)

instance [Add α] : RelLike (AddCon α) α where
  coe f := f.r
  coe_inj := by
    intro x y h
    cases x; congr
    apply DFunLike.coe_inj
    assumption

instance [Add α] : IsAddCon (AddCon α) where
  resp_add f := f.resp_add
  toEquivalence f := f.iseqv

structure MulCon (α: Type*) [Mul α] extends Setoid α where
  protected resp_mul: ∀{a b c d: α}, r a c -> r b d -> r (a * b) (c * d)

instance [Mul α] : RelLike (MulCon α) α where
  coe f := f.r
  coe_inj := by
    intro x y h
    cases x; congr
    apply DFunLike.coe_inj
    assumption

instance [Mul α] : IsMulCon (MulCon α) where
  resp_mul f := f.resp_mul
  toEquivalence f := f.iseqv

structure RingCon (α: Type*) [Add α] [Mul α] extends AddCon α, MulCon α where

instance [Add α] [Mul α] : RelLike (RingCon α) α where
  coe f := f.r
  coe_inj := by
    intro x y h
    cases x; congr
    apply DFunLike.coe_inj
    assumption

instance [Add α] [Mul α] : IsAddCon (RingCon α) where
  resp_add f := f.resp_add
  toEquivalence f := f.iseqv

instance [Add α] [Mul α] : IsMulCon (RingCon α) where
  resp_mul f := f.resp_mul
  toEquivalence f := f.iseqv

end Algebra

section Generator

variable (r: α -> α -> Prop)

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

inductive RingCon.Generator [Add α] [Mul α] : α -> α -> Prop where
| of {a b: α} : r a b -> Generator a b
| refl (a: α) : Generator a a
| symm {a b: α} : Generator a b -> Generator b a
| trans {a b c: α} : Generator a b -> Generator b c -> Generator a c
| add {a b c d: α} : Generator a c -> Generator b d -> Generator (a + b) (c + d)
| mul {a b c d: α} : Generator a c -> Generator b d -> Generator (a * b) (c * d)

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

def RingCon.generate [Add α] [Mul α] (r: α -> α -> Prop) : RingCon α where
  r := Generator r
  iseqv := {
    refl := Generator.refl
    symm := Generator.symm
    trans := Generator.trans
  }
  resp_add := Generator.add
  resp_mul := Generator.mul

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

instance [Mul α] [IsMulCon C] (c: C) : Mul (IsCon.Quotient c) where
  mul := by
    apply Quotient.lift₂ (fun a b => IsCon.mkQuot c (a * b))
    intro w x y z wy xz
    apply Quotient.sound
    apply IsMulCon.resp_mul
    assumption
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
