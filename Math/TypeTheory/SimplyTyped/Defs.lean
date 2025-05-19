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

end SubstAll

def subst_all {term: Term}
  (ht: term.IsSimplyWellTyped (ctx' ++ ctx) ty)
  (substs: List Term)
  (h: SubstAll ctx' substs):
  (term.subst_all substs).IsSimplyWellTyped ctx ty := by
  induction h generalizing term with
  | nil => assumption
  | @cons ctx terms ty subst wt h ih =>
    apply ih
    rw [←weaken_empty_ctx (term := subst)]
    apply IsSimplyWellTyped.subst
    assumption
    rw [weaken_empty_ctx (term := subst)]
    · rw [←weaken_all_empty_ctx (term := subst) wt]
      rw [←List.append_nil (_ ++ _)]
      apply weaken_all
      assumption
    assumption
    assumption

end IsSimplyWellTyped

end Term

end SimplyTyped
