import Math.Data.Like.Func
import Math.Relation.Defs
import Math.Algebra.AddMul

section Algebra

class IsCon (C: Sort*) {α: Type*} [RelLike C α]: Prop where
  protected toEquivalence (c: C): Equivalence c := by intro c; exact c.iseqv

class IsAddCon (C: Sort*) {α: Type*} [RelLike C α] [Add α]: Prop extends IsCon C where
  protected resp_add (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w + x) (y + z) := by intro c; exact c.resp_add

class IsMulCon (C: Sort*) {α: Type*} [RelLike C α] [Mul α]: Prop extends IsCon C where
  protected resp_mul (c: C): ∀{w x y z: α}, c w y -> c x z -> c (w * x) (y * z) := by intro c; exact c.resp_mul

class IsSMulCon (C: Sort*) (R: Type*) {α: Type*} [RelLike C α] [SMul R α]: Prop extends IsCon C where
  protected resp_smul (c: C): ∀(r: R) {x y: α}, c x y -> c (r • x) (r • y) := by intro c; exact c.resp_smul

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

def RingCon.copy [Add α] [Mul α] [RelLike C α] [IsAddCon C] [IsMulCon C] (c: C) (r: α -> α -> Prop) (h: r = c) : RingCon α where
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

section Impls

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

end Impls

section Quotient

variable {C α: Type*} [RelLike C α]

def AlgQuotient [IsCon C] (c: C) : Type _ := Quotient (IsCon.toSetoid c)

def IsCon.mkQuot [IsCon C] (c: C) : α -> AlgQuotient c := Quotient.mk _

@[induction_eliminator]
def AlgQuotient.ind [IsCon C] {c: C}
  {motive: AlgQuotient c -> Prop}
  (mk: ∀x, motive (IsCon.mkQuot c x))
  (a: AlgQuotient c) : motive a := _root_.Quotient.ind mk a

instance AlgQuotient.instAdd [Add α] [IsAddCon C] (c: C) : Add (AlgQuotient c) where
  add := by
    apply Quotient.lift₂ (fun a b => IsCon.mkQuot c (a + b))
    intro w x y z wy xz
    apply Quotient.sound
    apply resp_add
    assumption
    assumption

instance AlgQuotient.instMul [Mul α] [IsMulCon C] (c: C) : Mul (AlgQuotient c) where
  mul := by
    apply Quotient.lift₂ (fun a b => IsCon.mkQuot c (a * b))
    intro w x y z wy xz
    apply Quotient.sound
    apply resp_mul
    assumption
    assumption

instance AlgQuotient.instSMul [SMul R α] [IsSMulCon C R] (c: C) : SMul R (AlgQuotient c) where
  smul r := by
    apply Quotient.lift (fun a => IsCon.mkQuot c (r • a))
    intro x y h
    apply Quotient.sound
    apply resp_smul
    assumption

variable [IsCon C] (c: C)

instance : Relation.IsEquiv c := { IsCon.toEquivalence c with }

instance AlgQuotient.instZero [Zero α] : Zero (AlgQuotient c) where
  zero := IsCon.mkQuot _ 0
instance AlgQuotient.instOne [One α] : One (AlgQuotient c) where
  one := IsCon.mkQuot _ 1
instance AlgQuotient.instNatCast [NatCast α] : NatCast (AlgQuotient c) where
  natCast n := IsCon.mkQuot _ n
instance AlgQuotient.instIntCast [IntCast α] : IntCast (AlgQuotient c) where
  intCast n := IsCon.mkQuot _ n

end Quotient
