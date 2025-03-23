import Math.Ops.Checked
import Math.Order.Defs

def ne_zero_of_zero_lt [Zero α] [LT α] [LE α] [IsPreOrder α] (b: α) (h: 0 < b) : b ≠ 0 := (ne_of_lt h).symm

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply ne_zero_of_zero_lt; trivial)

def ne_zero_of_lt_zero [Zero α] [LT α] [LE α] [IsPreOrder α] (b: α) (h: b < 0) : b ≠ 0 := (ne_of_lt h)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply ne_zero_of_lt_zero; trivial)
