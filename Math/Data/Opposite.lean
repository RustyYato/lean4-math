import Math.Type.Notation

def Opposite (α: Sort*) := α

postfix:max "ᵒᵖ" => Opposite

def Opposite.mk : α -> αᵒᵖ := id
def Opposite.get : αᵒᵖ -> α := id

instance [LE α] : LE (Opposite α) where
  le a b := b.get ≤ a.get
instance [LT α] : LT (Opposite α) where
  lt a b := b.get < a.get
