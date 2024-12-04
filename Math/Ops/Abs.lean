import Math.Type.Notation

class AbsoluteValue (α β: Type*) where
  abs: α -> β

notation " ‖ " a " ‖ " => AbsoluteValue.abs a
