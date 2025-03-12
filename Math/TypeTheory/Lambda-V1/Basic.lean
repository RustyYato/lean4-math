inductive LamType where
| Void
| Unit
| Func (arg ret: LamType)

inductive LamTerm where
| ConstUnit : LamTerm
| Panic (body: LamTerm) (ty: LamType)
| Lambda (arg_ty: LamType) (body: LamTerm)
| App (func arg: LamTerm)
| Var (idx: Nat)

inductive LamTerm.IsWellTyped : List LamType -> LamType -> LamTerm -> Prop where
| ConstUnit : IsWellTyped ctx .Unit .ConstUnit
| Panic (body: LamTerm) (ty: LamType) :
  IsWellTyped ctx .Void body -> IsWellTyped ctx ty (.Panic body ty)
| Lambda (arg_ty ret_ty: LamType) (body: LamTerm) :
  IsWellTyped (arg_ty::ctx) ret_ty body -> IsWellTyped ctx (.Func arg_ty ret_ty) (.Lambda arg_ty body)
| App (arg_ty ret_ty: LamType) (func arg: LamTerm) :
  IsWellTyped ctx (.Func arg_ty ret_ty) func ->
  IsWellTyped ctx arg_ty arg ->
  IsWellTyped ctx ret_ty (.App func arg)
| Var (idx: Nat) (ty: LamType) (h: idx < ctx.length) :
  ty = ctx[idx] -> IsWellTyped ctx ty (.Var idx)

def LamTerm.unique_typing (ctx: List LamType) (ty₀ ty₁: LamType) (term: LamTerm) :
  term.IsWellTyped ctx ty₀ -> term.IsWellTyped ctx ty₁ -> ty₀ = ty₁ := by
  induction term generalizing ctx ty₀ ty₁ with
  | ConstUnit =>
    intro .ConstUnit .ConstUnit
    rfl
  | Panic body ty ih =>
    intro (.Panic _ _ _) (.Panic _ _ _)
    rfl
  | Lambda arg_ty body ih =>
    intro (.Lambda _ _ _ _) (.Lambda _ _ _ _)
    congr
    apply ih <;> assumption
  | App func arg funcih argih =>
    intro (.App _ _ _ _ fwt₀ awt₀) (.App _ _ _ _ fwt₁ awt₁)
    cases funcih ctx _ _ fwt₀ fwt₁
    rfl
  | Var idx =>
    intro (.Var _ ty h eq₀) (.Var _ ty h eq₁)
    subst eq₀; subst eq₁
    rfl

def LamTerm.weaken_at (pos: Nat) : LamTerm -> LamTerm
| .ConstUnit => .ConstUnit
| .App f a => .App (f.weaken_at pos) (a.weaken_at pos)
| .Lambda arg_ty body => .Lambda arg_ty (body.weaken_at pos.succ)
| .Panic body arg_ty => .Panic (body.weaken_at pos) arg_ty
| .Var idx =>
  .Var <| if idx < pos then
    idx
  else
    idx.succ

def LamTerm.weaken : LamTerm -> LamTerm := LamTerm.weaken_at 0

def LamTerm.IsWellTyped.weaken_at :
  IsWellTyped ctx ty term ->
  ∀pos ty', IsWellTyped (ctx.insertIdx pos ty') ty (term.weaken_at pos) := by
  intro wt
  induction wt with
  | ConstUnit =>
    intro pos ty'
    exact .ConstUnit
  | Panic body ty wt ih =>
    intro pos ty'
    apply IsWellTyped.Panic
    apply ih
  | App _ _ _ _ _ _ funih argih =>
    intro pos ty'
    apply IsWellTyped.App
    apply funih
    apply argih
  | Lambda _ _ _ _ ih  =>
    intro pos ty'
    apply IsWellTyped.Lambda
    apply ih pos.succ
  | Var _ _ h =>
    intro pos ty'
    apply IsWellTyped.Var
    split
    rw [List.getElem_insertIdx_of_lt]
    assumption
    assumption
    rw [List.getElem_insertIdx_of_ge]
    assumption
    apply Nat.succ_le_succ
    apply Nat.le_of_not_lt
    assumption
    rw [List.length_insertIdx]
    split
    split
    apply Nat.lt_trans
    exact h
    apply Nat.lt_succ_self
    assumption
    split
    apply Nat.succ_lt_succ
    assumption
    rename_i g₀ g₁
    have := Nat.lt_of_lt_of_le (Nat.lt_of_not_le g₁) (Nat.le_of_not_lt g₀)
    have := Nat.lt_asymm h this
    contradiction

def LamTerm.IsWellTyped.weaken : IsWellTyped ctx ty term -> ∀ty', IsWellTyped (ty'::ctx) ty term.weaken := (weaken_at · 0)

def LamTerm.subst_at (pos: Nat) (term subst: LamTerm) : LamTerm :=
  match term with
  | .ConstUnit => .ConstUnit
  | .App f a => .App (f.subst_at pos subst) (a.subst_at pos subst)
  | .Lambda arg_ty body => .Lambda arg_ty (body.subst_at pos.succ subst.weaken)
  | .Panic body arg_ty => .Panic (body.subst_at pos subst) arg_ty
  | .Var idx =>
    if idx = pos then
       subst
    else
      .Var <| if idx < pos then
        idx
      else
        idx.pred

def LamTerm.subst (term subst: LamTerm) : LamTerm := term.subst_at 0 subst

def LamTerm.IsWellTyped.subst_at :
  ∀{ctx ty},
  IsWellTyped ctx ty term ->
  ∀pos (h: pos < ctx.length) subst,
  IsWellTyped (ctx.eraseIdx pos) ctx[pos] subst ->
  IsWellTyped (ctx.eraseIdx pos) ty (term.subst_at pos subst) := by
  induction term with
  | ConstUnit =>
    intro _ _ .ConstUnit _ _ _ _
    exact .ConstUnit
  | App f a fih aih =>
    intro _ _ (.App _ _ _ _ _ _) _ _ _ _
    apply IsWellTyped.App
    apply fih <;> assumption
    apply aih <;> assumption
  | Lambda arg_ty body ih =>
    intro _ _ (.Lambda _ _ _ _) pos _ subst _
    apply IsWellTyped.Lambda
    apply ih (ctx := _::_) (pos := pos.succ) (subst := subst.weaken)
    assumption
    apply IsWellTyped.weaken
    assumption
    apply Nat.succ_lt_succ
    assumption
  | Panic body arg_ty ih =>
    intro _ _ (.Panic _ _ _) pos _ subst _
    apply IsWellTyped.Panic
    apply ih <;> assumption
  | Var idx =>
    intro ctx ty (.Var _ _ idx_lt ty_eq) pos ty' subst subst_wt
    subst ty
    unfold LamTerm.subst_at
    split
    subst idx
    exact subst_wt
    apply IsWellTyped.Var
    split
    rw [List.getElem_eraseIdx_of_lt]
    assumption
    rw [List.getElem_eraseIdx_of_ge]
    congr
    rw [Nat.add_one, Nat.succ_pred]
    intro h
    subst h
    cases Nat.lt_or_eq_of_le (Nat.zero_le pos) <;> contradiction
    apply Nat.le_pred_of_lt
    apply Nat.lt_of_le_of_ne
    apply Nat.le_of_not_lt
    assumption
    apply Ne.symm
    assumption
    rw [List.length_eraseIdx]
    split
    apply Nat.lt_of_lt_of_le
    assumption
    apply Nat.le_pred_of_lt
    assumption
    apply Nat.pred_lt_pred
    intro h
    subst h
    cases Nat.lt_or_eq_of_le (Nat.zero_le pos) <;> contradiction
    assumption

def LamTerm.IsWellTyped.subst : ∀{ty' ctx ty}, IsWellTyped (ty'::ctx) ty term -> ∀subst, IsWellTyped ctx ty' subst -> IsWellTyped ctx ty (term.subst subst) :=
  fun wt subst subst_wt => subst_at wt 0 (Nat.zero_lt_succ _) subst subst_wt

inductive LamTerm.IsValue : LamTerm -> Prop where
| ConstUnit : IsValue .ConstUnit
| Lambda (arg_ty: LamType) (body: LamTerm) : IsValue (.Lambda arg_ty body)
