import Math.Data.Multiset.Basic
import Math.Data.Map.Basic
import Math.Order.Linear

def Name := Nat
def Name.ofNat : Nat -> Name := id
def Name.toNat : Name -> Nat := id
instance : DecidableEq Name := inferInstanceAs (DecidableEq Nat)
instance : Repr Name := inferInstanceAs (Repr Nat)
instance : LT Name := inferInstanceAs (LT Nat)
instance : LE Name := inferInstanceAs (LE Nat)
instance : Max Name := inferInstanceAs (Max Nat)
instance : Min Name := inferInstanceAs (Min Nat)
instance : IsDecidableLinearOrder Name := inferInstanceAs (IsDecidableLinearOrder Nat)
instance : Bot Name := inferInstanceAs (Bot Nat)
instance : LawfulBot Name := inferInstanceAs (LawfulBot Nat)
attribute [irreducible] Name

def Name.rename (name source dest: Name) :=
  if name = source then dest else name

inductive LamType where
| Void
| Func (arg ret: LamType)
deriving DecidableEq

inductive LamTerm where
| Panic (body: LamTerm) (ty: LamType)
| Lambda (arg_name: Name) (arg_ty: LamType) (body: LamTerm)
| App (func arg: LamTerm)
| Var (name: Name)

def nodup_keys (data: Multiset (Name × LamType)) := data.Pairwise <| fun x y => x.1 ≠ y.1

abbrev Context := Map Name LamType

inductive LamTerm.IsWellFormed : Context -> LamTerm -> Prop where
| Panic (body: LamTerm) (ty: LamType):
  IsWellFormed ctx body ->
  IsWellFormed ctx (.Panic body ty)
| Lambda (arg_name: Name) (arg_ty: LamType) (body: LamTerm):
  -- lambdas must introduce new names into the context
  arg_name ∉ ctx ->
  IsWellFormed (insert ⟨arg_name, arg_ty⟩ ctx) body ->
  IsWellFormed ctx (.Lambda arg_name arg_ty body)
| App (func arg: LamTerm) :
  IsWellFormed ctx func ->
  IsWellFormed ctx arg ->
  IsWellFormed ctx (.App func arg)
| Var (name: Name) :
  name ∈ ctx ->
  IsWellFormed ctx (.Var name)

inductive LamTerm.IsWellTyped : Context -> LamTerm -> LamType -> Prop where
| Panic (body: LamTerm) (ty: LamType):
  IsWellTyped ctx body .Void ->
  IsWellTyped ctx (.Panic body ty) ty
| Lambda (arg_name: Name) (arg_ty ret_ty: LamType) (body: LamTerm):
  -- lambdas must introduce new names into the context
  arg_name ∉ ctx ->
  IsWellTyped (insert ⟨arg_name, arg_ty⟩ ctx) body ret_ty ->
  IsWellTyped ctx (.Lambda arg_name arg_ty body) (.Func arg_ty ret_ty)
| App (arg_ty ret_ty: LamType) (func arg: LamTerm) :
  IsWellTyped ctx func (.Func arg_ty ret_ty) ->
  IsWellTyped ctx arg arg_ty ->
  IsWellTyped ctx (.App func arg) ret_ty
| Var (name: Name) (ty: LamType) (h: name ∈ ctx) :
  ty = ctx[name] ->
  IsWellTyped ctx (.Var name) ty

def LamTerm.IsWellTyped.IsWellFormed {ctx: Context} {term: LamTerm} {ty: LamType} :
  IsWellTyped ctx term ty -> term.IsWellFormed ctx := by
  intro wt
  induction wt with
  | Panic => apply IsWellFormed.Panic <;> assumption
  | Lambda => apply IsWellFormed.Lambda <;> assumption
  | App => apply IsWellFormed.App <;> assumption
  | Var => apply IsWellFormed.Var <;> assumption

inductive LamTerm.IsValue : LamTerm -> Prop where
| Lambda arg_name arg_ty body : IsValue (.Lambda arg_name arg_ty body)

inductive LamTerm.IsSubTerm : LamTerm -> LamTerm -> Prop where
| AppFunc func arg: IsSubTerm func (.App func arg)
| AppArg func arg: IsSubTerm arg (.App func arg)
| Panic body ty: IsSubTerm body (.Panic body ty)
| LambdaBody n ty body: IsSubTerm body (.Lambda n ty body)

inductive LamTerm.Introduces (name: Name) : LamTerm -> Prop where
| AppFunc func arg: Introduces name func -> Introduces name (.App func arg)
| AppArg func arg: Introduces name arg -> Introduces name (.App func arg)
| Panic body ty: Introduces name body -> Introduces name (.Panic body ty)
| LambdaBody n ty body: Introduces name body -> Introduces name (.Lambda n ty body)
| Lambda ty body: Introduces name (.Lambda name ty body)

def LamTerm.subst (term subst: LamTerm) (name: Name) : LamTerm :=
  match term with
  | .App func arg => .App (func.subst subst name) (arg.subst subst name)
  | .Panic body ty => .Panic (body.subst subst name) ty
  | .Lambda n ty body => .Lambda n ty (body.subst subst name)
  | .Var n => if n = name then subst else term

def LamTerm.IsWellFormed.NoContextIntroductions
  {ctx: Context} {term: LamTerm} : term.IsWellFormed ctx -> ∀x ∈ ctx, ¬term.Introduces x := by
  intro wf
  induction wf with
  | Var => intros _ _ _; contradiction
  | Panic body ty wf ih =>
    intro x x_in_ctx i
    cases i; rename_i i
    exact ih _ x_in_ctx i
  | App _ _ _ _ ih₀ ih₁ =>
    intro x mem i
    cases i <;> rename_i i
    apply ih₀ _ mem i
    apply ih₁ _ mem i
  | Lambda _ _ _ nomem _ ih =>
    intro x mem i
    cases i <;> rename_i i
    apply ih x _ i
    apply Map.mem_insert.mpr (.inl _)
    assumption
    contradiction

def LamTerm.NoCommonIntroductions (a b: LamTerm) := ∀x, a.Introduces x -> b.Introduces x -> False

def LamTerm.NoCommonIntroductions.symm :
  NoCommonIntroductions a b ->
  NoCommonIntroductions b a := by
  intro h x ax bx
  apply h <;> assumption

def LamTerm.NoCommonIntroductions.ofSubTerm :
  NoCommonIntroductions a b ->
  IsSubTerm a₀ a ->
  NoCommonIntroductions a₀ b := by
  intro h sub x ax bx
  cases sub <;> apply h x _ bx
  exact .AppFunc _ _ ax
  exact .AppArg _ _ ax
  exact .Panic _ _ ax
  exact .LambdaBody _ _ _ ax

def LamTerm.NoCommonIntroductions.ofTransSubTerm :
  NoCommonIntroductions a b ->
  Relation.ReflTransGen IsSubTerm a₀ a ->
  NoCommonIntroductions a₀ b := by
  intro h sub
  induction sub with
  | refl => assumption
  | cons sub _ ih =>
    apply NoCommonIntroductions.ofSubTerm
    apply ih
    assumption
    assumption

def LamTerm.IsWellFormed.weaken
  {ctx: Context} {term: LamTerm} {x}:
  IsWellFormed ctx term ->
  (¬term.Introduces x.fst) ->
  IsWellFormed (insert x ctx) term := by
  intro wf nointro
  induction wf with
  | Panic _ _ _ ih =>
    apply IsWellFormed.Panic
    apply ih
    intro h
    apply nointro
    apply Introduces.Panic
    assumption
  | App _ _ _ _ ih₀ ih₁ =>
    apply IsWellFormed.App
    apply ih₀
    intro h
    apply nointro
    apply Introduces.AppFunc
    assumption
    apply ih₁
    intro h
    apply nointro
    apply Introduces.AppArg
    assumption
  | Var =>
    apply LamTerm.IsWellFormed.Var
    apply Map.mem_insert.mpr (.inl _)
    assumption
  | Lambda arg_name _ _ _  _ ih =>
    apply IsWellFormed.Lambda
    intro h
    cases Map.mem_insert.mp h
    contradiction
    subst arg_name
    apply nointro
    apply Introduces.Lambda
    rw [Map.insert_comm]
    apply ih
    intro h
    apply nointro
    apply Introduces.LambdaBody
    assumption
    intro h
    subst h
    apply nointro
    apply Introduces.Lambda

def LamTerm.IsWellFormed.subst
  {ctx: Context}
  {term subst: LamTerm} {name: Name}:
  name ∈ ctx ->
  term.IsWellFormed ctx ->
  subst.IsWellFormed (ctx.erase name) ->
  term.NoCommonIntroductions subst ->
  (term.subst subst name).IsWellFormed (ctx.erase name) := by
  intro name_in_ctx wf subst_wf nocomm
  induction wf with
  | Panic _ _ _ ih  =>
    apply IsWellFormed.Panic
    apply ih
    assumption
    assumption
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .Panic _ _
  | App _ _ _ _ ih₀ ih₁ =>
    apply IsWellFormed.App
    apply ih₀
    assumption
    assumption
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .AppFunc _ _
    apply ih₁
    assumption
    assumption
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .AppArg _ _
  | Lambda _ _ _ _ _ ih =>
    apply IsWellFormed.Lambda
    intro mem
    have ⟨arg_in_ctx, _⟩  := Map.mem_erase.mp mem
    contradiction
    rw [←Map.erase_insert_comm_of_ne]
    apply ih
    apply Map.mem_insert.mpr (.inl _)
    assumption
    · rw [Map.erase_insert_comm_of_ne]
      apply LamTerm.IsWellFormed.weaken
      assumption
      apply nocomm
      apply Introduces.Lambda
      dsimp
      intro h
      subst h
      contradiction
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .LambdaBody _ _ _
    dsimp
    have := nocomm
    intro h
    subst h
    contradiction
  | Var n n_in_ctx =>
    unfold LamTerm.subst
    split
    assumption
    apply IsWellFormed.Var
    apply Map.mem_erase.mpr ⟨_, _⟩
    assumption
    assumption

def LamTerm.IsWellTyped.weaken
  {ctx: Context} {term: LamTerm} {ty: LamType} {x}:
  IsWellTyped ctx term ty ->
  (¬term.Introduces x.fst) ->
  IsWellTyped (insert x ctx) term ty  := by
  intro wf nointro
  induction wf with
  | Panic _ _ _ ih =>
    apply IsWellTyped.Panic
    apply ih
    intro h
    apply nointro
    apply Introduces.Panic
    assumption
  | App _ _ _ _ _ _ ih₀ ih₁ =>
    apply IsWellTyped.App
    apply ih₀
    intro h
    apply nointro
    apply Introduces.AppFunc
    assumption
    apply ih₁
    intro h
    apply nointro
    apply Introduces.AppArg
    assumption
  | Var =>
    apply LamTerm.IsWellTyped.Var
    rw [Map.insert_get_elem_tail]
    assumption
  | Lambda arg_name _ _ _ _  _ ih =>
    apply IsWellTyped.Lambda
    intro h
    cases Map.mem_insert.mp h
    contradiction
    subst arg_name
    apply nointro
    apply Introduces.Lambda
    rw [Map.insert_comm]
    apply ih
    intro h
    apply nointro
    apply Introduces.LambdaBody
    assumption
    intro h
    subst h
    apply nointro
    apply Introduces.Lambda

def LamTerm.IsWellTyped.subst
  {ctx: Context} {ty: LamType}
  {term subst: LamTerm} {name: Name} {name_in_ctx: name ∈ ctx}:
  term.IsWellTyped ctx ty ->
  subst.IsWellTyped (ctx.erase name) ctx[name] ->
  term.NoCommonIntroductions subst ->
  (term.subst subst name).IsWellTyped (ctx.erase name) ty := by
  intro wf subst_wf nocomm
  induction wf with
  | Panic _ _ _ ih  =>
    apply IsWellTyped.Panic
    apply ih
    assumption
    apply nocomm.ofSubTerm
    apply IsSubTerm.Panic
  | App _ _ _ _ _  _ ih₀ ih₁ =>
    apply IsWellTyped.App
    apply ih₀
    assumption
    apply nocomm.ofSubTerm
    apply IsSubTerm.AppFunc
    apply ih₁
    assumption
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .AppArg _ _
  | Lambda _ _ _ _ _ _ ih =>
    apply IsWellTyped.Lambda
    intro mem
    have ⟨arg_in_ctx, _⟩  := Map.mem_erase.mp mem
    contradiction
    rw [←Map.erase_insert_comm_of_ne]
    apply ih
    rw [Map.insert_get_elem_tail, Map.erase_insert_comm_of_ne]
    apply IsWellTyped.weaken
    assumption
    apply nocomm
    apply Introduces.Lambda
    dsimp; intro h; subst h; contradiction
    apply NoCommonIntroductions.ofSubTerm
    assumption
    exact .LambdaBody _ _ _
    dsimp
    have := nocomm
    intro h
    subst h
    contradiction
  | Var n n_in_ctx =>
    unfold LamTerm.subst
    split
    subst n
    subst n_in_ctx
    assumption
    apply IsWellTyped.Var
    rw [Map.erase_get_elem]
    assumption
    apply Map.mem_erase.mpr ⟨_, _⟩
    assumption
    assumption

instance LamTerm.decIntroduces : ∀term, Decidable (LamTerm.Introduces name term)
| .Var _ => .isFalse nofun
| .Panic body _ =>
  match decIntroduces body with
  | .isTrue h => .isTrue (.Panic _ _ h)
  | .isFalse h => .isFalse fun | .Panic _ _ g => h g
| .App f a =>
  match decIntroduces f with
  | .isTrue h => .isTrue (.AppFunc _ _ h)
  | .isFalse hf =>
  match decIntroduces a with
  | .isTrue h => .isTrue (.AppArg _ _ h)
  | .isFalse ha => .isFalse fun
    | .AppArg _ _ h => ha h
    | .AppFunc _ _ h => hf h
| .Lambda n _ body =>
  if h:n = name then
    .isTrue <| h ▸ (.Lambda _ _)
  else
  match decIntroduces body with
  | .isTrue h => .isTrue (.LambdaBody _ _ _ h)
  | .isFalse ha => .isFalse fun
     | .Lambda _ _ => h rfl
     | .LambdaBody _ _ _ h => ha h

def LamTerm.max_intro_name : LamTerm -> Name
| .Var _ => ⊥
| .App f a => max f.max_intro_name a.max_intro_name
| .Panic b _ => b.max_intro_name
| .Lambda n _ b => max n b.max_intro_name

def Context.max_name (ctx: Context) : Name := by
  apply Quotient.lift (fun x => _) _ ctx.data
  intro names
  exact names.foldr (fun x y => max x.fst y) ⊥
  intro a b eq
  dsimp
  induction eq with
  | nil => rfl
  | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
  | cons _ _ ih => rw [List.foldr_cons, List.foldr_cons, ih]
  | swap x y =>
    dsimp [List.foldr_cons]
    rw [max_assoc, max_assoc, max_comm x.fst]

def LamTerm.rename (source dest: Name) : LamTerm -> LamTerm
| .Panic body ty => .Panic (body.rename source dest) ty
| .Var name => .Var <| name.rename source dest
| .App f a => .App (f.rename source dest) (a.rename source dest)
| .Lambda name ty body => .Lambda (name.rename source dest) ty (body.rename source dest)

def LamTerm.Introduces.rename {source dest: Name} {term: LamTerm}:
  term.Introduces source -> (term.rename source dest).Introduces dest := by
  intro i
  induction i with
  | AppFunc => apply Introduces.AppFunc; assumption
  | AppArg => apply Introduces.AppArg; assumption
  | Panic => apply Introduces.Panic; assumption
  | LambdaBody => apply Introduces.LambdaBody; assumption
  | Lambda =>
    unfold LamTerm.rename
    unfold Name.rename
    rw [if_pos rfl]
    apply Introduces.Lambda

def LamTerm.Introduces.rename_ne {source dest: Name} {term: LamTerm} (h: source ≠ dest):
  ¬(term.rename source dest).Introduces source := by
  induction term with
  | Var => exact nofun
  | Panic => intro h; cases h; contradiction
  | App =>
    intro h
    cases h
    contradiction
    contradiction
  | Lambda =>
    unfold LamTerm.rename Name.rename
    intro h
    split at h
    subst source
    cases h
    contradiction
    contradiction
    cases h
    contradiction
    contradiction

def LamTerm.IsWellFormed.rename_from_ctx
  (source dest: Name) {ctx: Context} {term: LamTerm}
  (hs: source ∈ ctx)
  (dest_nointro: ¬term.Introduces dest):
  term.IsWellFormed ctx -> (term.rename source dest).IsWellFormed (insert ⟨dest, ctx[source]⟩ (ctx.erase source)) := by
  intro wf
  induction wf with
  | Panic _ _ _ ih =>
    apply IsWellFormed.Panic
    apply ih
    intro h
    exact dest_nointro (.Panic _ _ h)
  | App _ _ _ _ ih₀ ih₁ =>
    apply IsWellFormed.App
    apply ih₀
    intro h
    exact dest_nointro (.AppFunc _ _ h)
    apply ih₁
    intro h
    exact dest_nointro (.AppArg _ _ h)
  | Lambda name ty body name_notin_ctx wf ih  =>
    replace hs' :=
      (IsWellFormed.Lambda _ _ _ name_notin_ctx wf).NoContextIntroductions _ hs
    replace hs'' :=
      wf.NoContextIntroductions _ (Map.mem_insert.mpr <| .inl hs)
    apply IsWellFormed.Lambda
    unfold Name.rename; split
    subst source
    exfalso
    exact hs' (.Lambda _ _)
    intro mem
    rw [Map.mem_insert, Map.mem_erase] at mem
    dsimp at mem
    rcases mem with ⟨mem, _⟩ | eq
    contradiction
    subst dest
    exact dest_nointro (.Lambda _ _)

    unfold Name.rename
    have name_ne_source : name ≠ source := fun h => name_notin_ctx (h ▸ hs)
    have name_ne_dest : name ≠ dest := fun h => dest_nointro (h ▸ .Lambda _ _)
    rw [if_neg name_ne_source]
    have := ih (Map.mem_insert.mpr <| .inl hs) (fun h => dest_nointro (.LambdaBody _ _ _ h))
    rw [Map.insert_get_elem_tail] at this
    rw [Map.erase_insert_comm_of_ne name_ne_source,
      Map.insert_comm] at this
    assumption
    dsimp
    exact name_ne_dest.symm
  | Var =>
    apply IsWellFormed.Var
    unfold Name.rename; split
    subst source; apply Map.mem_insert.mpr; right; rfl
    apply Map.mem_insert.mpr; left
    apply Map.mem_erase.mpr
    apply And.intro <;> assumption

def LamTerm.IsWellFormed.rename_no_intro
  {source dest: Name} {ctx: Context} {term: LamTerm} (hs: source ∉ ctx) (hs': ¬term.Introduces source):
  term.IsWellFormed ctx -> term.rename source dest = term := by
  intro wf
  induction wf with
  | Panic _ _ _ ih =>
    unfold rename
    rw [ih hs]
    intro h
    exact hs' (.Panic _ _ h)
  | App _ _ _ _ ih₀ ih₁ =>
    unfold rename
    rw [ih₀ hs, ih₁ hs]
    intro h
    exact hs' (.AppArg _ _ h)
    intro h
    exact hs' (.AppFunc _ _ h)
  | Lambda name _ _ _ _ ih  =>
    have : name ≠ source := by
      intro h
      subst source
      apply hs'
      apply Introduces.Lambda
    unfold rename
    rw [ih]
    congr
    unfold Name.rename
    rw [if_neg this]
    intro h
    cases Map.mem_insert.mp h
    contradiction
    subst source; contradiction
    intro h
    exact hs' (.LambdaBody _ _ _ h)
  | Var =>
    unfold rename Name.rename
    rw [if_neg]
    intro h
    subst h
    contradiction

def LamTerm.IsWellFormed.rename
  {source dest: Name} {ctx: Context} {term: LamTerm}
  (hs: term.Introduces source)
  (dest_notin_ctx: dest ∉ ctx)
  (dest_nointro: ¬term.Introduces dest):
  term.IsWellFormed ctx -> (term.rename source dest).IsWellFormed ctx := by
  intro wf
  cases wf with
  | Panic =>
    apply IsWellFormed.Panic
    apply LamTerm.IsWellFormed.rename
    cases hs
    assumption
    assumption
    intro  h
    exact dest_nointro (.Panic _ _ h)
    assumption
  | App func arg funcwf argwf =>
    by_cases hf:func.Introduces source
    <;> by_cases ha:arg.Introduces source
    · apply IsWellFormed.App
      apply IsWellFormed.rename
      assumption
      assumption
      intro h
      exact dest_nointro (.AppFunc _ _ h)
      assumption
      apply IsWellFormed.rename
      assumption
      assumption
      intro h
      exact dest_nointro (.AppArg _ _ h)
      assumption
    · apply IsWellFormed.App
      apply IsWellFormed.rename
      assumption
      assumption
      intro h
      exact dest_nointro (.AppFunc _ _ h)
      assumption
      rw [rename_no_intro]
      assumption
      apply flip (funcwf.NoContextIntroductions _)
      assumption
      assumption
      assumption
    · apply IsWellFormed.App
      rw [rename_no_intro]
      assumption
      apply flip (argwf.NoContextIntroductions _)
      assumption
      assumption
      assumption
      apply IsWellFormed.rename
      assumption
      assumption
      intro h
      exact dest_nointro (.AppArg _ _ h)
      assumption
    · cases hs <;> contradiction
  | Lambda name ty body name_notin_ctx wf  =>
    apply IsWellFormed.Lambda
    unfold Name.rename
    split
    assumption
    assumption
    unfold Name.rename
    split
    subst source
    have := LamTerm.IsWellFormed.rename_from_ctx name dest (ctx := insert ⟨name, ty⟩ ctx) (Map.mem_insert.mpr (.inr rfl)) (fun h => dest_nointro (.LambdaBody _ _ _ h)) wf
    rw [Map.insert_get_elem_head, Map.erase_insert_cancel (x := ⟨name, _⟩)] at this
    assumption
    assumption
    assumption
    cases hs with
    | Lambda => contradiction
    | LambdaBody =>
    apply LamTerm.IsWellFormed.rename
    assumption
    intro h
    cases Map.mem_insert.mp h
    contradiction
    dsimp at *; subst dest
    exact dest_nointro (.Lambda _ _)
    intro h
    exact dest_nointro (.LambdaBody _ _ _ h)
    assumption
  | Var =>
    apply IsWellFormed.Var
    unfold Name.rename; split
    subst source; contradiction
    assumption

def LamTerm.IsWellTyped.rename_from_ctx
  (source dest: Name) {ctx: Context} {term: LamTerm} {ty: LamType}
  (hs: source ∈ ctx)
  (dest_notin_ctx: dest ∉ ctx)
  (dest_nointro: ¬term.Introduces dest):
  term.IsWellTyped ctx ty -> (term.rename source dest).IsWellTyped (insert ⟨dest, ctx[source]⟩ (ctx.erase source)) ty := by
  intro wf
  induction wf with
  | Panic _ _ _ ih =>
    apply IsWellTyped.Panic
    apply ih
    assumption
    intro h
    exact dest_nointro (.Panic _ _ h)
  | App _ _ _ _ _ _ ih₀ ih₁ =>
    apply IsWellTyped.App
    apply ih₀
    assumption
    intro h
    exact dest_nointro (.AppFunc _ _ h)
    apply ih₁
    assumption
    intro h
    exact dest_nointro (.AppArg _ _ h)
  | Lambda name ty retty body name_notin_ctx wt ih  =>
    replace hs' :=
      (IsWellFormed.Lambda _ _ _ name_notin_ctx wt.IsWellFormed).NoContextIntroductions _ hs
    replace hs'' :=
      wt.IsWellFormed.NoContextIntroductions _ (Map.mem_insert.mpr <| .inl hs)
    apply IsWellTyped.Lambda
    unfold Name.rename; split
    subst source
    exfalso
    exact hs' (.Lambda _ _)
    intro mem
    rw [Map.mem_insert, Map.mem_erase] at mem
    dsimp at mem
    rcases mem with ⟨mem, _⟩ | eq
    contradiction
    subst dest
    exact dest_nointro (.Lambda _ _)

    unfold Name.rename
    have name_ne_source : name ≠ source := fun h => name_notin_ctx (h ▸ hs)
    have name_ne_dest : name ≠ dest := fun h => dest_nointro (h ▸ .Lambda _ _)
    rw [if_neg name_ne_source]
    have := ih (Map.mem_insert.mpr <| .inl hs) (by
      intro h
      cases Map.mem_insert.mp h
      contradiction
      subst dest
      contradiction) (fun h => dest_nointro (.LambdaBody _ _ _ h))
    rw [Map.insert_get_elem_tail] at this
    rw [Map.erase_insert_comm_of_ne name_ne_source,
      Map.insert_comm] at this
    assumption
    dsimp
    exact name_ne_dest.symm
  | Var =>
    unfold rename Name.rename
    split
    · subst source
      apply IsWellTyped.Var
      rw [Map.insert_get_elem_head]
      dsimp
      assumption
      dsimp
      intro h
      have ⟨_, _⟩ := Map.mem_erase.mp h
      contradiction
    · apply IsWellTyped.Var
      rw [Map.insert_get_elem_tail, Map.erase_get_elem]
      assumption
      apply Map.mem_erase.mpr
      apply And.intro
      assumption
      intro h
      subst h
      contradiction

def LamTerm.IsWellTyped.rename
  {source dest: Name} {ctx: Context} {term: LamTerm} {ty}
  (hs: term.Introduces source)
  (dest_notin_ctx: dest ∉ ctx)
  (dest_nointro: ¬term.Introduces dest):
  term.IsWellTyped ctx ty -> (term.rename source dest).IsWellTyped ctx ty := by
  intro wf
  cases wf with
  | Panic =>
    apply IsWellTyped.Panic
    apply LamTerm.IsWellTyped.rename
    cases hs
    assumption
    assumption
    intro  h
    exact dest_nointro (.Panic _ _ h)
    assumption
  | App retty _ func arg funcwf argwf =>
    by_cases hf:func.Introduces source
    <;> by_cases ha:arg.Introduces source
    · apply IsWellTyped.App
      apply IsWellTyped.rename
      assumption
      assumption
      intro h
      exact dest_nointro (.AppFunc _ _ h)
      assumption
      apply IsWellTyped.rename
      assumption
      assumption
      intro h
      exact dest_nointro (.AppArg _ _ h)
      assumption
    · apply IsWellTyped.App
      apply IsWellTyped.rename
      assumption
      assumption
      intro h
      exact dest_nointro (.AppFunc _ _ h)
      assumption
      rw [IsWellFormed.rename_no_intro]
      assumption
      apply flip (funcwf.IsWellFormed.NoContextIntroductions _)
      assumption
      assumption
      exact argwf.IsWellFormed
    · apply IsWellTyped.App
      rw [IsWellFormed.rename_no_intro]
      assumption
      apply flip (argwf.IsWellFormed.NoContextIntroductions _)
      assumption
      assumption
      exact funcwf.IsWellFormed
      apply IsWellTyped.rename
      assumption
      assumption
      intro h
      exact dest_nointro (.AppArg _ _ h)
      assumption
    · cases hs <;> contradiction
  | Lambda name ty retty body name_notin_ctx wf  =>
    apply IsWellTyped.Lambda
    unfold Name.rename
    split
    assumption
    assumption
    unfold Name.rename
    split
    subst source
    have := LamTerm.IsWellTyped.rename_from_ctx name dest (ctx := insert ⟨name, ty⟩ ctx) (Map.mem_insert.mpr (.inr rfl)) (by
      intro h
      cases Map.mem_insert.mp h
      contradiction
      subst dest
      exact dest_nointro (.Lambda _ _)) (fun h => dest_nointro (.LambdaBody _ _ _ h)) wf
    rw [Map.insert_get_elem_head, Map.erase_insert_cancel (x := ⟨name, _⟩)] at this
    assumption
    assumption
    assumption
    cases hs with
    | Lambda => contradiction
    | LambdaBody =>
    apply LamTerm.IsWellTyped.rename
    assumption
    intro h
    cases Map.mem_insert.mp h
    contradiction
    dsimp at *; subst dest
    exact dest_nointro (.Lambda _ _)
    intro h
    exact dest_nointro (.LambdaBody _ _ _ h)
    assumption
  | Var =>
    apply IsWellTyped.Var
    unfold Name.rename; split
    all_goals contradiction

def LamTerm.unique_typing {term: LamTerm}:
  term.IsWellTyped ctx ty₀ ->
  term.IsWellTyped ctx ty₁ ->
  ty₀ = ty₁ := by
  intro wt₀ wt₁
  induction term generalizing ctx ty₀ ty₁ with
  | Panic  =>
    cases wt₀; cases wt₁
    rfl
  | App func arg ih =>
    cases wt₀
    cases wt₁
    rename_i wt₀ _ _  wt₁
    cases ih wt₀ wt₁
    rfl
  | Lambda _ _ _ ih =>
    cases wt₀; cases wt₁
    rename_i wt₀ _ _ wt₁
    rw [ih wt₀ wt₁]
  | Var =>
    cases wt₀; cases wt₁
    subst ty₀; subst ty₁
    rfl
