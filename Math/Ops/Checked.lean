          import Lean

class CheckedInvert (α: Sort u) (P: outParam (α -> Prop)) where
  checked_invert: ∀a: α, P a -> α

class CheckedDiv (α: Sort u) (P: outParam (α -> Prop)) where
  checked_div: α -> ∀den: α, P den -> α

class CheckedMod (α: Sort u) (P: outParam (α -> Prop)) where
  checked_mod: α -> ∀den: α, P den -> α

syntax "invert_tactic" : tactic
syntax "invert_tactic_trivial" : tactic

-- prioritize assumption, so if the user proves this manually, that proof will be used
macro_rules | `(tactic|invert_tactic) => `(tactic|first|assumption|invert_tactic_trivial)
macro_rules | `(tactic|invert_tactic_trivial) => `(tactic|trivial)
macro_rules | `(tactic|invert_tactic_trivial) => `(tactic|left; invert_tactic_trivial)
macro_rules | `(tactic|invert_tactic_trivial) => `(tactic|right; invert_tactic_trivial)
macro_rules | `(tactic|invert_tactic_trivial) => `(tactic|constructor <;> invert_tactic_trivial)

syntax:max term noWs "⁻¹" : term
macro_rules | `($x⁻¹) => `(CheckedInvert.checked_invert $x (by invert_tactic))

syntax:70 term:70 " /? " term:71 : term
macro_rules | `($x /? $y) => `(CheckedDiv.checked_div $x $y (by invert_tactic))

syntax:70 term:70 " %? " term:71 : term
macro_rules | `($x %? $y) => `(CheckedMod.checked_mod $x $y (by invert_tactic))

syntax:max term noWs "⁻¹" "~(" term ")" : term
macro_rules | `($x⁻¹ ~($prf)) => `(CheckedInvert.checked_invert $x $prf)

syntax:70 term:70 " /? " term:71 "~(" term ")" : term
macro_rules | `($x /? $y ~($prf)) => `(CheckedDiv.checked_div $x $y $prf)

syntax:70 term:70 " %? " term:71 "~(" term ")" : term
macro_rules | `($x %? $y ~($prf)) => `(CheckedMod.checked_mod $x $y $prf)

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.CheckedDiv.checked_div]
def delab_checked_div : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, y, _] := expr.getAppArgs | failure
  let x ← delab x
  let y ← delab y
  `($x /? $y)

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.CheckedMod.checked_mod]
def delab_checked_mod : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, y, _] := expr.getAppArgs | failure
  let x ← delab x
  let y ← delab y
  `($x %? $y)

open Lean Meta PrettyPrinter Delaborator SubExpr in
@[delab app.CheckedInvert.checked_invert]
def delab_checked_invert : Delab := do
  let expr ← getExpr
  let #[_, _, _, x, _] := expr.getAppArgs | failure
  let x ← delab x
  `($x⁻¹)
