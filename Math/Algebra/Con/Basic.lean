import Math.Algebra.Hom.Defs
import Math.Algebra.Con.Defs
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
