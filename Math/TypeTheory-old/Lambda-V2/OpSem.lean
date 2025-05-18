import Math.TypeTheory.Lambda.Basic
import Math.Relation.Defs

inductive ReduceTo (ctx: Context) : LamTerm -> LamTerm -> Prop where
| Subst : LamTerm.IsValue arg -> ReduceTo ctx (.App (.Lambda name argty body) arg) (body.subst (arg.relabel body ctx.max_name) name)
| Panic : ReduceTo ctx body body' -> ReduceTo ctx (.Panic body ty) (.Panic body' ty)
| AppFunc : ReduceTo ctx func func' -> ReduceTo ctx (.App func arg) (.App func' arg)
| AppArg : LamTerm.IsValue func -> ReduceTo ctx arg arg' -> ReduceTo ctx (.App func arg) (.App func arg')

variable {ctx: Context}

abbrev NormalizeTo (ctx: Context) := Relation.ReflTransGen (ReduceTo ctx)

def ReduceTo.not_value {a b: LamTerm} : ReduceTo ctx a b -> ¬a.IsValue := by
  intro ab h
  cases ab <;> contradiction

def ReduceTo.decide {a b b': LamTerm} : ReduceTo ctx a b -> ReduceTo ctx a b' -> b = b' := by
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
  rename_i h _ _
  have := h.not_value
  contradiction
  congr
  rename_i ih _ _
  apply ih
  assumption
  rename_i h _ _ _ _
  have := h.not_value
  contradiction
  rename ReduceTo _ _ _ => h
  have := h.not_value
  contradiction
  congr
  rename_i ih _ _ _
  apply ih
  assumption

def NormalizeTo.push :  ReduceTo ctx a b -> NormalizeTo ctx b c -> NormalizeTo ctx a c := Relation.ReflTransGen.cons

def NormalizeTo.pop {a b c: LamTerm} (h: c.IsValue) :
  ReduceTo ctx b a -> NormalizeTo ctx b c -> NormalizeTo ctx a c := by
  intro ba bc
  cases bc
  have := ba.not_value
  contradiction
  rename_i bc _
  cases ba.decide bc
  assumption

-- any well typed term in the empty context either is either a value or steps to another term
def LamTerm.progress (ty: LamType) (term: LamTerm) : term.IsWellTyped ∅ ty -> term.IsValue ∨ ∃term', ReduceTo ctx term term' := by
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
      exact ⟨_, .Subst aval⟩
    · exact ⟨_, .AppArg fval ared⟩
    · exact ⟨_, .AppFunc fred⟩

def LamTerm.IsWellTyped.ReduceTo : ReduceTo ctx term term' -> term.IsWellTyped ctx ty -> term'.IsWellTyped ctx ty := by
intro red wt
induction red generalizing ty with
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
| Subst _ =>
  rename_i arg _ _ body _
  cases wt
  rename_i awt fwt
  cases fwt; rename_i bodywt
  have := IsWellTyped.subst (Map.mem_insert.mpr <| .inr rfl) bodywt (subst := arg.relabel body ctx.max_name)
  rw [Map.erase_insert_cancel, Map.insert_get_elem_head] at this
  dsimp at this
  apply this
  apply IsWellTyped.relabel
  assumption
  apply le_refl
  apply LamTerm.relabel.NoCommonIntroductions
  assumption
  assumption

def LamTerm.IsWellTyped.NormalizeTo : NormalizeTo ctx term term' -> term.IsWellTyped ctx ty -> term'.IsWellTyped ctx ty := by
  intro norm
  induction norm with
  | refl => exact id
  | cons _ _ ih =>
    intro h
    apply ih
    apply ReduceTo
    assumption
    assumption

inductive LamTerm.Halts (ctx: Context) (a: LamTerm) : Prop where
| intro (value: LamTerm) : value.IsValue -> NormalizeTo ctx a value -> Halts ctx a

def LamTerm.Halts.Reduce (a: LamTerm) (h: ReduceTo ctx a b) : Halts ctx a ↔ Halts ctx b := by
  apply Iff.intro
  intro ⟨val, val_spec, red⟩
  refine ⟨val, val_spec, ?_⟩
  apply NormalizeTo.pop
  assumption
  assumption
  assumption
  intro ⟨val, val_spec, red⟩
  refine ⟨val, val_spec, ?_⟩
  apply NormalizeTo.push
  assumption
  assumption

def LamTerm.Halts.Reduction (a: LamTerm) (h: NormalizeTo ctx a b) : Halts ctx a ↔ Halts ctx b := by
  induction h with
  | refl => apply Iff.refl
  | cons r _ ih =>
    apply Iff.trans _ ih
    apply Halts.Reduce
    assumption

def LamTerm.HeredHalts {ctx ty} (a: LamTerm) (wt: a.IsWellTyped ctx ty) : Prop :=
  match ty with
  | .Void => False
  | .Func arg_ty ret_ty =>
    a.Halts ctx ∧ (
      ∀(arg: LamTerm) (h: arg.IsWellTyped ctx arg_ty), HeredHalts _ (.App arg_ty ret_ty a arg wt h)
    )

def Reduce.hered_halts_iff {a: LamTerm} (wt: a.IsWellTyped ctx ty) (red: ReduceTo ctx a b) :
  a.HeredHalts wt ↔ b.HeredHalts (wt.ReduceTo red) := by
  induction ty generalizing ctx a b with
  | Void => apply Iff.intro <;> (intro; contradiction)
  | Func arg_ty ret_ty arg_ih ret_ih =>
    apply Iff.intro
    intro ⟨halts, hered⟩
    apply And.intro
    apply (LamTerm.Halts.Reduce _ _).mp <;> assumption
    intro arg arg_wt
    apply (ret_ih _ _).mp
    apply hered
    assumption
    apply ReduceTo.AppFunc
    assumption
    intro ⟨halts, hered⟩
    apply And.intro
    apply (LamTerm.Halts.Reduce _ _).mpr <;> assumption
    intro arg arg_wt
    apply (ret_ih _ _).mpr
    apply hered
    assumption
    apply ReduceTo.AppFunc
    assumption

def Reduction.hered_halts_iff {a: LamTerm} (wt: a.IsWellTyped ctx ty) (red: NormalizeTo ctx a b) :
  a.HeredHalts wt ↔ b.HeredHalts (wt.NormalizeTo red) := by
  induction red generalizing ty with
  | refl => apply Iff.refl
  | cons r _ ih =>
    apply Iff.trans _ (ih _)
    apply LamTerm.IsWellTyped.ReduceTo
    assumption
    assumption
    apply Reduce.hered_halts_iff
    assumption
