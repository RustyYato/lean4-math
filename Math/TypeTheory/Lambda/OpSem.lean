import Math.TypeTheory.Lambda.Basic
import Math.Relation.Basic

inductive ReduceTo : LamTerm -> LamTerm -> Prop where
| Subst : LamTerm.IsValue arg -> body.NoCommonIntroductions arg -> ReduceTo (.App (.Lambda name argty body) arg) (body.subst arg name)
| Panic : ReduceTo body body' -> ReduceTo (.Panic body ty) (.Panic body' ty)
| AppFunc : ReduceTo func func' -> ReduceTo (.App func arg) (.App func' arg)
| AppArg : LamTerm.IsValue func -> ReduceTo arg arg' -> ReduceTo (.App func arg) (.App func arg')

infix:100 " ~> " => ReduceTo
def NormalizeTo := Relation.ReflTransGen (· ~> ·)
infix:100 " ~*> " => NormalizeTo

def ReduceTo.not_value {a b: LamTerm} : a ~> b -> ¬a.IsValue := by
  intro ab h
  cases ab <;> contradiction

def ReduceTo.decide {a b b': LamTerm} : a ~> b -> a ~> b' -> b = b' := by
  intro ab ab'
  induction ab generalizing b' <;> cases ab'
  rfl
  any_goals
    rename_i h
    have := h.not_value
    contradiction
  congr
  rename_i ih _ _ ; apply ih
  assumption
  rename_i h _ _ _
  have := h.not_value
  contradiction
  congr
  rename_i ih _ _
  apply ih
  assumption
  rename_i h _ _ _ _
  have := h.not_value
  contradiction
  rename _ ~> _ => h
  have := h.not_value
  contradiction
  congr
  rename_i ih _ _ _
  apply ih
  assumption

def NormalizeTo.push : a ~> b -> b ~*> c -> a ~*> c := Relation.ReflTransGen.cons

def NormalizeTo.pop {a b c: LamTerm} (h: c.IsValue) :
  b ~> a -> b ~*> c -> a ~*> c := by
  intro ba bc
  cases bc
  have := ba.not_value
  contradiction
  rename_i bc _
  cases ba.decide bc
  assumption

-- any well typed term in the empty context either is either a value or steps to another term
def LamTerm.progress (ty: LamType) (term: LamTerm) : term.IsWellTyped ∅ ty -> term.IsValue ∨ ∃term', term ~> term' := by
  intro wt
  induction term generalizing ty with
  | Lambda =>
    left
    apply LamTerm.IsValue.Lambda
  | Var name =>
    cases wt; rename_i mem _
    have := Map.not_mem_empty name mem
    contradiction
  | Panic body ty ih =>
    right
    cases wt; rename_i wt
    rcases ih _ wt with val | ⟨body', red⟩
    have := wt.NotVoidValue val
    contradiction
    exact ⟨_, .Panic red⟩
  | App func arg fih aih =>
    cases wt; rename_i arg_ty awt fwt
    have fih := fih _ fwt
    have aih := aih _ awt
    right
    rcases fih with fval | ⟨f', fred⟩
    rcases aih with aval | ⟨a', ared⟩
    · cases fval with | Lambda name argty body =>
      refine ⟨_, .Subst aval sorry⟩
    · refine ⟨_, .AppArg fval ared⟩
    · refine ⟨_, .AppFunc fred⟩

def LamTerm.IsWellTyped.reduce :
term ~> term' ->
term.IsWellTyped ctx ty ->
term'.IsWellTyped ctx ty := by
intro red wt
induction red generalizing ctx ty with
| Panic _ ih =>
  cases wt
  apply IsWellTyped.Panic
  apply ih
  assumption
| AppFunc _ ih =>
  cases wt
  apply IsWellTyped.App
  apply ih
  assumption
  assumption
| AppArg _ _ ih =>
  cases wt
  apply IsWellTyped.App
  assumption
  apply ih
  assumption
| Subst _ nocomm =>
  rename_i arg _ _ _ _
  cases wt
  rename_i awt fwt
  cases fwt; rename_i bodywt
  have := IsWellTyped.subst (Map.mem_insert.mpr <| .inr rfl) bodywt (subst := arg)
  rw [Map.erase_insert_cancel, Map.insert_get_elem_head] at this
  dsimp at this
  exact this awt nocomm
  assumption
  assumption
