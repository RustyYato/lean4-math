import Math.TypeTheory.Lambda.Defs

section SimplyTyped

inductive SimpleLamType where
| void -- a type with no introduction forms
| func (arg ret: SimpleLamType)

abbrev SimpleLamType.TypeCtx := List SimpleLamType

open SimpleLamType (TypeCtx)

namespace Term

inductive IsSimplyWellTyped : TypeCtx -> Term -> SimpleLamType -> Prop where
| lam (ctx: TypeCtx) (body: Term) (arg_ty ret_ty: SimpleLamType) :
  IsSimplyWellTyped (arg_ty::ctx) body ret_ty ->
  IsSimplyWellTyped ctx (.lam body) (.func arg_ty ret_ty)
| app (ctx: TypeCtx) (func arg: Term) (arg_ty ret_ty: SimpleLamType) :
  IsSimplyWellTyped ctx func (.func arg_ty ret_ty) ->
  IsSimplyWellTyped ctx arg arg_ty ->
  IsSimplyWellTyped ctx (.app func arg) ret_ty
| var (ctx: TypeCtx) (name: ℕ) (ty: SimpleLamType) (h: name < ctx.length) :
  ty = ctx[name] -> IsSimplyWellTyped ctx (.var name) ty

private def erase_mid
  (ctx₀ ctx' ctx: List α) (ty: α)
 : ctx₀ ++ ctx' ++ ctx = (ctx₀ ++ ty :: ctx' ++ ctx).eraseIdx (List.length ctx₀) := by
  rw [List.eraseIdx_append_of_lt_length, List.eraseIdx_append_of_length_le]
  simp
  rfl
  simp

namespace IsSimplyWellTyped

def weaken_at_level {term: Term} (ht: term.IsSimplyWellTyped ctx ty) (level: ℕ) (new_ty: SimpleLamType) : (term.weaken_at_level level).IsSimplyWellTyped (ctx.insertIdx level new_ty) ty := by
  induction ht generalizing level with
  | lam ctx body arg_ty ret_ty body_wt ih =>
    apply IsSimplyWellTyped.lam
    apply ih (level + 1)
  | app ctx func arg arg_ty ret_ty func_wt arg_wt ihf iha =>
    apply IsSimplyWellTyped.app
    apply ihf
    apply iha
  | var ctx name ty h ty_eq =>
    apply IsSimplyWellTyped.var
    rw [List.getElem_insertIdx]
    split
    assumption
    rw [dif_neg]
    split
    subst level
    rename_i h
    simp at h
    simpa
    omega
    rw [List.length_insertIdx]
    split
    split
    omega
    assumption
    split
    apply Nat.succ_lt_succ
    assumption
    omega

def weaken {term: Term} (ht: term.IsSimplyWellTyped ctx ty) (new_ty: SimpleLamType) : term.weaken.IsSimplyWellTyped (new_ty::ctx) ty := by
  apply ht.weaken_at_level 0

def weaken_all {term: Term} (ht: term.IsSimplyWellTyped ctx ty) (ctx': TypeCtx) : (term.weaken_all ctx'.length).IsSimplyWellTyped (ctx' ++ ctx) ty := by
  induction ctx' with
  | nil => assumption
  | cons ty' ctx' ih =>
    apply weaken
    apply ih

def subst_at {term subst: Term} {var: ℕ} (hvar: var < ctx.length) (ht: term.IsSimplyWellTyped ctx ty) (hs: subst.IsSimplyWellTyped (ctx.eraseIdx var) ctx[var]) : (term.subst subst var).IsSimplyWellTyped (ctx.eraseIdx var) ty := by
  induction ht generalizing var subst with
  | lam ctx body arg_ty ret_ty body_wt ih =>
    apply IsSimplyWellTyped.lam
    apply ih (var := var + 1)
    apply Term.IsSimplyWellTyped.weaken
    assumption
    apply Nat.succ_lt_succ
    assumption
  | app ctx func arg arg_ty ret_ty func_wt arg_wt ihf iha =>
    apply IsSimplyWellTyped.app
    apply ihf
    assumption
    apply iha
    assumption
  | var ctx name ty h ty_eq =>
    unfold Term.subst
    split
    subst var
    subst ty
    assumption
    apply IsSimplyWellTyped.var
    · rw [List.getElem_eraseIdx]
      split
      assumption
      split
      omega
      rw [ty_eq]; congr 1
      omega
      split
      rw [List.length_eraseIdx]
      rw [if_pos]
      omega
      assumption
      rw [List.length_eraseIdx]
      rw [if_pos]
      omega
      assumption

def subst {term subst: Term} (ht: term.IsSimplyWellTyped (sty::ctx) ty) (hs: subst.IsSimplyWellTyped ctx sty) : (term.subst subst 0).IsSimplyWellTyped ctx ty := by
  apply subst_at (var := 0) _ ht hs
  apply Nat.zero_lt_succ

def reduce {term term': Term} (ht: term.IsSimplyWellTyped ctx ty) (h: term.Reduce term') : term'.IsSimplyWellTyped ctx ty := by
  induction h generalizing ctx ty with
  | apply =>
    cases ht
    rename_i ht
    cases ht
    rename_i ht
    apply ht.subst
    assumption
  | app_func _ _ _ _ ih =>
    cases ht
    rename_i ht
    apply IsSimplyWellTyped.app
    apply ih
    assumption
    assumption
  | app_arg _ _ _ _ _ ih =>
    cases ht
    rename_i ht
    apply IsSimplyWellTyped.app
    assumption
    apply ih
    assumption

def reduces_to {term term': Term} (ht: term.IsSimplyWellTyped ctx ty) (h: term.ReducesTo term') : term'.IsSimplyWellTyped ctx ty := by
  induction h with
  | refl => assumption
  | cons r rs ih =>
    apply ih
    apply ht.reduce
    assumption

def weaken_at_level_empty_ctx_aux {term: Term} (ht: term.IsSimplyWellTyped ctx ty) (h: ctx.length ≤ level) : term.weaken_at_level level = term := by
  induction ht generalizing level with
  | lam ctx body arg_ty ret_ty wt ih =>
    simp
    rw [ih]
    apply Nat.succ_le_succ
    assumption
  | app ctx func arg arg_ty ret_ty func_wt arg_wt ihf iha =>
    simp
    rw [ihf, iha]
    trivial
    assumption
    assumption
  | var =>
    simp [Term.weaken_at_level]
    omega

def weaken_at_level_empty_ctx {term: Term} (ht: term.IsSimplyWellTyped [] ty) : term.weaken_at_level level = term := by
  apply weaken_at_level_empty_ctx_aux
  assumption
  apply Nat.zero_le

def weaken_empty_ctx {term: Term} (ht: term.IsSimplyWellTyped [] ty) : term.weaken = term := by
  apply weaken_at_level_empty_ctx
  assumption

def weaken_all_empty_ctx {term: Term} (ht: term.IsSimplyWellTyped [] ty) : term.weaken_all n = term := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Term.weaken_all
    rw [weaken_empty_ctx, ih]
    rwa [ih]

def subst_at_empty_ctx_aux {var: ℕ} {term subst: Term} (ht: term.IsSimplyWellTyped ctx ty) (h: ctx.length ≤ var) : term.subst subst var = term := by
  induction ht generalizing var subst with
  | lam ctx body arg_ty ret_ty wt ih =>
    simp
    apply ih
    apply Nat.succ_le_succ
    assumption
  | app ctx func arg arg_ty ret_ty func_wt arg_wt ihf iha =>
    simp
    rw [ihf, iha]
    trivial
    assumption
    assumption
  | var =>
    simp [Term.subst]
    rw [if_neg, if_pos]
    omega
    omega

def subst_at_empty_ctx {var: ℕ} {term subst: Term} (ht: term.IsSimplyWellTyped [] ty) : term.subst subst var = term := by
  apply subst_at_empty_ctx_aux
  assumption
  apply Nat.zero_le

def subst_all_empty_ctx {term: Term} {substs: List Term} (ht: term.IsSimplyWellTyped [] ty) : term.subst_all offset substs = term := by
  induction substs generalizing term with
  | nil => rfl
  | cons subst substs ih =>
    unfold subst_all
    rw [ih]
    rw [subst_at_empty_ctx]
    assumption
    rwa [subst_at_empty_ctx]
    assumption

def expand_ctx_from_empty (term: Term) (ht: term.IsSimplyWellTyped [] ty) :
  term.IsSimplyWellTyped ctx ty := by
  rw [←weaken_all_empty_ctx (term := term), ←List.append_nil ctx]
  apply IsSimplyWellTyped.weaken_all
  assumption
  assumption

inductive SubstAll : TypeCtx -> List Term -> Prop where
| nil : SubstAll [] []
| cons :
  term.IsSimplyWellTyped [] ty ->
  SubstAll ctx terms ->
  SubstAll (ty::ctx) (term::terms)

namespace SubstAll

def length_eq (h: SubstAll ctx terms) : ctx.length = terms.length := by
  induction h with
  | nil => rfl
  | cons wt h ih => simp [ih]

protected def wt (h: SubstAll ctx terms) (hi: i < terms.length) : terms[i].IsSimplyWellTyped [] (ctx[i]'(by rwa [h.length_eq])) := by
  induction h generalizing i with
  | nil => contradiction
  | cons wt h ih =>
    cases i
    assumption
    apply ih

end SubstAll

def subst_all {term: Term}
  (ht: term.IsSimplyWellTyped (ctx₀ ++ ctx' ++ ctx) ty)
  (substs: List Term)
  (h: SubstAll ctx' substs):
  (term.subst_all ctx₀.length substs).IsSimplyWellTyped (ctx₀ ++ ctx) ty := by
  induction h generalizing term with
  | nil => simpa using ht
  | @cons ctx' terms ty subst wt h ih =>
    apply ih
    rw [←weaken_empty_ctx (term := subst)]
    rw [erase_mid ctx₀ ctx' _ ty]
    apply IsSimplyWellTyped.subst_at
    assumption
    simp
    rw [weaken_empty_ctx]
    apply expand_ctx_from_empty
    assumption
    assumption
    simp
    assumption

end IsSimplyWellTyped

def subst_all_var_of_ge
  (substs: List Term)
  (h: IsSimplyWellTyped.SubstAll ctx' substs)
  (hname: name - offset < substs.length)
  (hname': offset ≤ name) :
  (Term.var name).subst_all offset substs = substs[name - offset] := by
  induction substs generalizing name ctx' offset with
  | nil => contradiction
  | cons subst substs ih =>
    cases h with | @cons ctx' ty ty subst subst_wt h =>
    unfold subst_all Term.subst
    split
    rw [IsSimplyWellTyped.subst_all_empty_ctx (term := subst)]
    subst offset
    simp
    assumption
    split
    rename_i h
    rw [←Nat.not_le] at h
    contradiction
    cases name with
    | zero => omega
    | succ name =>
      conv in (name + 1 - offset) => { rw [Nat.succ_sub (by omega)] }
      simp
      rw [ih]
      assumption
      omega

def subst_all_var_of_lt
  (substs: List Term)
  (h: IsSimplyWellTyped.SubstAll ctx' substs)
  (hname': name < offset) :
  (Term.var name).subst_all offset substs = Term.var name := by
  induction substs generalizing name ctx' offset with
  | nil => rfl
  | cons subst substs ih =>
    cases h
    unfold subst_all Term.subst
    rw [if_neg, if_pos hname']
    rw [ih]
    assumption
    assumption
    omega

def susbt_all_app
  (substs: List Term)
  (h: IsSimplyWellTyped.SubstAll ctx' substs)
  (func arg: Term):
  (func.app arg).subst_all offset substs =
  (func.subst_all offset substs).app (arg.subst_all offset substs) := by
  induction h generalizing func arg with
  | nil => rfl
  | @cons ctx' substs ty' s _ _ ih =>
    unfold subst_all
    simp
    rw [ih]

def susbt_all_lam
  (substs: List Term)
  (h: IsSimplyWellTyped.SubstAll ctx' substs)
  (body: Term) :
  body.lam.subst_all offset substs =
  (body.subst_all (offset + 1) substs).lam := by
  induction h generalizing body with
  | nil => rfl
  | @cons ctx' substs ty' s _ _ ih =>
    unfold subst_all
    simp
    rw [ih]
    congr
    rwa [IsSimplyWellTyped.weaken_empty_ctx]

def subst_all_subst_succ
  (term subst: Term) (wt: term.IsSimplyWellTyped (ctx₀ ++ subst_ty::ctx') ty)
  (h: IsSimplyWellTyped.SubstAll (subst_ty::ctx') (subst::substs)) :
  (term.subst_all (ctx₀.length + 1) substs).subst subst ctx₀.length = term.subst_all ctx₀.length (subst::substs) := by
  have subst_wt := h.wt (i := 0) (hi := Nat.zero_lt_succ _)
  simp at subst_wt
  induction term generalizing ctx₀ ty with
  | lam body ih =>
    cases wt
    rename_i arg_ty ret_ty wt
    rw [susbt_all_lam, susbt_all_lam, subst_lam]
    rw [IsSimplyWellTyped.weaken_empty_ctx (term := subst)]
    replace ih := ih (ctx₀ := arg_ty::ctx₀) (ty := ret_ty)
    simp at ih
    rw [ih]
    assumption
    assumption
    assumption
    cases h
    assumption
  | app func arg ihf iha =>
    cases wt
    rw [susbt_all_app, susbt_all_app]
    simp
    rw [ihf, iha]
    apply And.intro <;> rfl
    assumption
    assumption
    assumption
    cases h
    assumption
  | var name =>
    cases wt
    rename_i hn _
    simp at hn

    rcases lt_trichotomy name ctx₀.length with hn' | hn' | hn'
    · rw [subst_all_var_of_lt _ (by assumption) hn', subst_all_var_of_lt _ (by cases h; assumption) (by omega)]
      unfold Term.subst
      simp [hn']
      intro; omega
    · subst name
      rw [subst_all_var_of_lt, subst_all_var_of_ge]
      simp
      unfold Term.subst
      simp
      assumption
      simp
      rfl
      cases h
      assumption
      apply Nat.lt_succ_self
    · cases h
      rename_i h
      rw [subst_all_var_of_ge (hname := by
        rename_i h₀
        rw [←h₀.length_eq]
        omega), subst_all_var_of_ge (hname := (by
        simp
        rename_i h₀
        rw [←h₀.length_eq]
        omega))]
      rw [IsSimplyWellTyped.subst_at_empty_ctx]
      cases name
      contradiction
      simp
      rename_i name _ _
      conv in (name + 1 - _) => { rw [Nat.succ_sub (by omega)] }
      simp
      apply h.wt
      apply IsSimplyWellTyped.SubstAll.cons
      assumption
      assumption
      omega
      assumption
      omega

def reduce_or_value (term: Term) (h: term.IsSimplyWellTyped [] ty) : term.IsValue ∨ ∃term': Term, term.Reduce term' := by
  induction term generalizing ty with
  | lam => left; apply Term.IsValue.lam
  | app func arg ihf iha =>
    right
    cases h; rename_i arg_ty harg hfunc
    rcases ihf hfunc
    rcases iha harg <;> rename_i gfunc garg
    cases gfunc
    rename_i body
    exists body.subst arg 0
    apply Term.Reduce.apply
    assumption
    obtain ⟨arg', h⟩ := garg
    exists func.app arg'
    apply Term.Reduce.app_arg
    assumption
    assumption
    rename_i gfunc
    obtain ⟨func', h⟩ := gfunc
    exists func'.app arg
    apply Term.Reduce.app_func
    assumption
  | var => contradiction

end Term

end SimplyTyped
