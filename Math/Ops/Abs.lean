import Math.Type.Notation

class Norm (α: Type*) (β: outParam (Type*)) where
  norm: α -> β

notation "‖" x "‖" => Norm.norm x

instance : Norm Int Nat where
  norm := Int.natAbs

def abs [Neg α] [Max α] (a: α) := max a (-a)

macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)

@[app_unexpander abs]
def abs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()
