import Math.Tactics.Continuity.Init

attribute [aesop (rule_sets := [Continuous]) unfold norm] Function.comp

/--
The `continuity` attribute used to tag continuity statements for the `continuity` tactic. -/
macro "continuity" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `Continuous):ident]))

/--
The tactic `continuity` solves goals of the form `IsContinuous f` by applying lemmas tagged with the
`continuity` user attribute. -/
macro "continuity" : tactic =>
  `(tactic| aesop (config := { terminal := true })
     (rule_sets := [$(Lean.mkIdent `Continuous):ident]))

/--
The tactic `continuity` solves goals of the form `IsContinuous f` by applying lemmas tagged with the
`continuity` user attribute. -/
macro "continuity?" : tactic =>
  `(tactic| aesop? (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Continuous):ident]))
