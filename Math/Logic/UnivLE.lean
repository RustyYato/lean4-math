import Math.Logic.Small.Basic

-- a universe `u` is smaller than a universe `v` if all values
@[pp_with_univ]
abbrev UnivLE.{u, v} := ∀α: Type u, Small.{v} α

instance : UnivLE.{u, u} := inferInstance
instance : UnivLE.{u, u+1} := inferInstance
instance : UnivLE.{0, u} := inferInstance
