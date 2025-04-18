import Math.Algebra.Hom.Defs
import Math.Algebra.Con.Order
import Math.Data.Setoid.Basic

variable
  [FunLike F α β] [Add α] [Add β] [Mul α] [Mul β] [SMul R α] [SMul R β]
  [IsAddHom F α β] [IsMulHom F α β] [IsSMulHom F R α β]

def AddCon.kernel (f: F) : AddCon α where
  toSetoid := Setoid.kernel f
  resp_add {a b c d} h g := by
    show f (a + b) = f (c + d)
    rw [map_add, map_add, h, g]

def MulCon.kernel (f: F) : MulCon α where
  toSetoid := Setoid.kernel f
  resp_mul {a b c d} h g := by
    show f (a * b) = f (c * d)
    rw [map_mul, map_mul, h, g]

def SMulCon.kernel (f: F) : SMulCon R α where
  toSetoid := Setoid.kernel f
  resp_smul r {a b} h := by
    show f (r • a) = f (r • b)
    rw [map_smul, map_smul, h]

def RingCon.kernel (f: F) : RingCon α := {
  AddCon.kernel f, MulCon.kernel f with
}

def LinearCon.kernel (f: F) : LinearCon R α := {
  AddCon.kernel f, SMulCon.kernel f with
}

def AddCon.lift (f: F) {c: AddCon α} (resp: c ≤ kernel f) : AlgQuotient c -> β := Quotient.lift f resp
def MulCon.lift (f: F) {c: MulCon α} (resp: c ≤ kernel f) : AlgQuotient c -> β := Quotient.lift f resp
def SMulCon.lift (f: F) {c: SMulCon R α} (resp: c ≤ kernel f) : AlgQuotient c -> β := Quotient.lift f resp
def RingCon.lift (f: F) {c: RingCon α} (resp: c ≤ kernel f) : AlgQuotient c -> β := Quotient.lift f resp
def LinearCon.lift (f: F) {c: LinearCon R α} (resp: c ≤ kernel f) : AlgQuotient c -> β := Quotient.lift f resp

def AddCon.comap (f: F) (c: AddCon β) : AddCon α := {
  Setoid.comap f c.toSetoid with
  resp_add := by
    intro w x y z h g
    show c _ _
    rw [map_add, map_add f]
    apply resp_add
    assumption
    assumption
}
def MulCon.comap (f: F) (c: MulCon β) : MulCon α := {
  Setoid.comap f c.toSetoid with
  resp_mul := by
    intro w x y z h g
    show c _ _
    rw [map_mul, map_mul f]
    apply resp_mul
    assumption
    assumption
}
def SMulCon.comap (f: F) (c: SMulCon R β) : SMulCon R α := {
  Setoid.comap f c.toSetoid with
  resp_smul := by
    intro r x y h
    show c _ _
    rw [map_smul, map_smul f]
    apply resp_smul
    assumption
}
def RingCon.comap (f: F) (c: RingCon β) : RingCon α := {
  c.toAddCon.comap f, c.toMulCon.comap f with
}
def LinearCon.comap (f: F) (c: LinearCon R β) : LinearCon R α := {
  c.toAddCon.comap f, c.toSMulCon.comap f with
}

variable [Zero α] [One α] [RelLike C α]

def AddCon.mkQuot [IsAddCon C] (c: C) : α →+ AlgQuotient c where
  toFun a := IsCon.mkQuot c a
  map_zero := rfl
  map_add := rfl
def MulCon.mkQuot [IsMulCon C] (c: C) : α →* AlgQuotient c where
  toFun a := IsCon.mkQuot c a
  map_one := rfl
  map_mul := rfl
def SMulCon.mkQuot [IsSMulCon C R] (c: C) : SMulHom R α (AlgQuotient c) where
  toFun a := IsCon.mkQuot c a
  map_smul := rfl
def LinearCon.mkQuot [IsAddCon C] [IsSMulCon C R] (c: C) : α →ₗ[R] (AlgQuotient c) where
  toFun a := IsCon.mkQuot c a
  map_add := rfl
  map_smul := rfl
def RingCon.mkQuot [IsAddCon C] [IsMulCon C] (c: C) : α →+* (AlgQuotient c) where
  toFun a := IsCon.mkQuot c a
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

def AddCon.mkQuot_kernel (c: AddCon α) : AddCon.kernel (AddCon.mkQuot c) = c := by
  apply le_antisymm
  · intro x y h
    exact Quotient.exact h
  · intro x y h
    exact Quotient.sound h
def MulCon.mkQuot_kernel (c: MulCon α) : MulCon.kernel (MulCon.mkQuot c) = c := by
  apply le_antisymm
  · intro x y h
    exact Quotient.exact h
  · intro x y h
    exact Quotient.sound h
def SMulCon.mkQuot_kernel (c: SMulCon R α) : SMulCon.kernel (SMulCon.mkQuot (R := R) c) = c := by
  apply le_antisymm
  · intro x y h
    exact Quotient.exact h
  · intro x y h
    exact Quotient.sound h
def LinearCon.mkQuot_kernel (c: LinearCon R α) : LinearCon.kernel (LinearCon.mkQuot (R := R) c) = c := by
  apply le_antisymm
  · intro x y h
    exact Quotient.exact h
  · intro x y h
    exact Quotient.sound h
def RingCon.mkQuot_kernel (c: RingCon α) : RingCon.kernel (RingCon.mkQuot c) = c := by
  apply le_antisymm
  · intro x y h
    exact Quotient.exact h
  · intro x y h
    exact Quotient.sound h

def AddCon.mkQuot_surj [IsAddCon C] (c: C) : Function.Surjective (AddCon.mkQuot c) := Quotient.mkSurj
def MulCon.mkQuot_surj [IsMulCon C] (c: C) : Function.Surjective (MulCon.mkQuot c) := Quotient.mkSurj
def SMulCon.mkQuot_surj [IsSMulCon C R] (c: C) : Function.Surjective (SMulCon.mkQuot (R := R) c) := Quotient.mkSurj
def LinearCon.mkQuot_surj [IsAddCon C] [IsSMulCon C R] (c: C) : Function.Surjective (LinearCon.mkQuot (R := R) c) := Quotient.mkSurj
def RingCon.mkQuot_surj [IsAddCon C] [IsMulCon C] (c: C) : Function.Surjective (RingCon.mkQuot c) := Quotient.mkSurj
