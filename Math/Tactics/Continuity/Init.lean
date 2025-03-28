import Aesop

/-! This doc was taken from Mathlib

# Continuity Rule Set

This module defines the `Continuous` Aesop rule set which is used by the
`continuity` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [Continuous]
