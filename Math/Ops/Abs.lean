import Math.Type.Notation

class AbsoluteValue (α: Type*) (β: outParam (Type*)) where
  abs: α -> β

notation "‖" a "‖" => AbsoluteValue.abs a
