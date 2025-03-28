import Math.Type.Notation

class AbsoluteValue (α: Type*) (β: outParam (Type*)) where
  abs: α -> β

abbrev abs [AbsoluteValue α β] : α -> β := AbsoluteValue.abs

macro:max atomic("|" noWs) a:term noWs "|" : term => `(AbsoluteValue.abs $a)

instance : AbsoluteValue Int Nat where
  abs := Int.natAbs

@[app_unexpander AbsoluteValue.abs]
def abs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()
