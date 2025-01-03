import Math.Data.Multiset.Basic

inductive LamType where
| Void
| Func (arg ret: LamType)
deriving DecidableEq

inductive LamTerm where
| Panic (body: LamTerm) (ty: LamType)
| Lambda (arg_name: Nat) (arg_ty: LamType) (body: LamTerm)
| App (func arg: LamTerm)
| Var (name: Nat)

def nodup_keys (data: Multiset (Nat × LamType)) := data.Pairwise <| fun x y => x.1 ≠ y.1

structure Context: Type where
  data: Multiset (Nat × LamType)
  nodup_keys: nodup_keys data

namespace Context

instance : Membership Nat Context where
  mem ctx name := ∃v, ⟨name, v⟩ ∈ ctx.data

instance (x: Nat) (ctx: Context) : Decidable (x ∈ ctx) :=
  decidable_of_iff (∃y ∈ ctx.data, x = y.1) <| by
    apply Iff.intro
    intro ⟨⟨k, v⟩, mem, eq⟩
    exists v
    subst x
    assumption
    intro ⟨v, mem⟩
    exists ⟨x, v⟩

instance : GetElem Context Nat LamType (fun ctx name => name ∈ ctx) where
  getElem ctx name prf := by
    apply Quotient.hrecOn ctx.data (motive := fun list => (∃v, Multiset.mem  ⟨name, v⟩ list) -> _root_.nodup_keys list -> LamType)
    case f =>
      intro list mem _
      apply Option.getD _ LamType.Void
      apply Option.map _
      exact list.find? fun ⟨k, v⟩ => k = name
      exact Prod.snd
    case c =>
      dsimp
      intro a b eq
      apply Function.hfunext
      · show (∃v, (name, v) ∈ Multiset.mk _) = (∃v, (name, v) ∈ Multiset.mk _)
        congr
        funext
        congr 1
        apply Quotient.sound
        assumption
      intro h₀ h₁ heq₁
      apply Function.hfunext
      · congr 1
        apply Quotient.sound
        assumption
      intro h₂ h₃ heq₂
      apply heq_of_eq
      clear h₀ h₁ heq₁
      · induction eq with
        | nil => rfl
        | cons _ _ ih =>
          unfold List.find?
          split
          rfl
          apply ih
          apply proof_irrel_heq
          cases h₂
          assumption
          cases h₃
          assumption
        | trans _ _ ih₀ ih₁ =>
          rename_i x₀ x₁ x₂ x₁₂ x₂₃
          have : Multiset.Pairwise (fun x y => x.1 ≠ y.1) (Quotient.mk _ x₁) := by
            rw [Quotient.sound x₂₃]
            assumption
          rw [ih₀, ih₁]
          any_goals assumption
          any_goals apply proof_irrel_heq
        | swap =>
          unfold List.find? List.find?
          rename_i x y _
          cases hx:decide (x.fst = name) <;> cases hy:decide (y.fst = name) <;> dsimp
          exfalso
          cases h₂
          rename_i h
          apply h
          apply List.Mem.head
          rw [of_decide_eq_true hx, of_decide_eq_true hy]
    case a => exact prf
    case a => exact ctx.nodup_keys

-- remove an existing key from ctx
def erase (key: Nat) (ctx: Context) (h: key ∈ ctx) : Context where
  data := ctx.data.erase ⟨key, ctx[key]⟩
  nodup_keys := by
    apply Multiset.Pairwise.erase
    exact ctx.nodup_keys

-- insert a new key into the context
def insert_no_dup (key: Nat) (v: LamType) (ctx: Context) (h: key ∉ ctx) : Context where
  data := ctx.data.cons ⟨key, v⟩
  nodup_keys := by
    apply ctx.nodup_keys.cons
    intro x g
    intro eq; subst eq
    exact h ⟨_, g⟩

-- inserts key into ctx iff it doesn't already exist in ctx
def insert' (key: Nat) (ty: LamType) (ctx: Context) : Context :=
  if h:key ∈ ctx then
    ctx
  else
    ctx.insert_no_dup key ty h

-- remove a key from ctx
def remove (key: Nat) (ctx: Context) : Context :=
  if h:key ∈ ctx then
    ctx.erase key h
  else
    ctx

instance : EmptyCollection Context where
  emptyCollection := { data := ∅, nodup_keys := Multiset.Pairwise.nil }

instance : Insert (Nat × LamType) Context where
  insert x := insert' x.1 x.2

instance : Singleton (Nat × LamType) Context where
  singleton := (insert · ∅)

def mem_insert_no_dup {key: Nat} {ty: LamType} {ctx: Context} {h: key ∉ ctx}:
  ∀{x}, x ∈ ctx.insert_no_dup key ty h ↔ x ∈ ctx ∨ x = key := by
  intro x
  apply Iff.intro
  intro ⟨v, h⟩
  rcases Multiset.mem_cons.mp h with h | h
  right; cases h; rfl
  left; exact ⟨_, h⟩
  intro g
  rcases g with g | g
  obtain ⟨v, g⟩  := g
  exists v
  apply Multiset.mem_cons.mpr
  right; assumption
  exists ty
  apply Multiset.mem_cons.mpr
  left; rw [g]

def mem_insert'_head (key: Nat) (ty: LamType) (ctx: Context) :
  key ∈ ctx.insert' key ty := by
  unfold insert'
  split
  assumption
  apply mem_insert_no_dup.mpr
  right; rfl

def mem_insert'_tail (k key: Nat) (ty: LamType) (ctx: Context) :
  k ∈ ctx ->
  k ∈ ctx.insert' key ty := by
  intro h
  unfold insert'
  split
  assumption
  apply mem_insert_no_dup.mpr
  left; assumption

def of_mem_insert' (k key: Nat) (ty: LamType) (ctx: Context) :
  k ∈ ctx.insert' key ty ->
  k = key ∨ k ∈ ctx := by
  intro h
  unfold insert' at h
  split at h
  right; assumption
  exact (mem_insert_no_dup.mp h).symm

def mem_insert_head (x: Nat × LamType) (ctx: Context) :
  x.1 ∈ insert x ctx := by
  apply mem_insert'_head

def mem_insert_tail {x: Nat} {y: Nat × LamType} {ctx: Context} :
  x ∈ ctx ->
  x ∈ insert y ctx := by
  apply mem_insert'_tail

def of_mem_insert {x: Nat} {y: Nat × LamType} {ctx: Context} :
  x ∈ insert y ctx ->
  x = y.fst ∨ x ∈ ctx := by
  apply of_mem_insert'

macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply mem_insert_head)
macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply mem_insert_tail; get_elem_tactic)
macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply mem_insert_no_dup.mpr; left; get_elem_tactic)
macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply mem_insert_no_dup.mpr; right; get_elem_tactic)

def insert_nodup_get_elem (ctx: Context) (key: Nat) (ty: LamType) (h: key ∉ ctx) (g: name ∈ ctx ∨ name = key) :
  (insert_no_dup key ty ctx h)[name]'(mem_insert_no_dup.mpr g) = if hkey:name = key then ty else ctx[name]'(by
    cases g
    assumption
    contradiction) := by
  unfold insert_no_dup
  cases ctx with | mk ctx nodup =>
  cases ctx with | mk ctx =>
  show Option.getD _ LamType.Void = _
  unfold List.find?
  split <;>rename_i h'
  dsimp at h'
  cases of_decide_eq_true h'
  dsimp
  rw [dif_pos rfl]
  replace h' := of_decide_eq_false h'
  rw [dif_neg (Ne.symm h')]
  rfl

def insert_get_elem_head (ctx: Context) (key: Nat) (ty: LamType) (h: key ∉ ctx) : (insert ⟨key, ty⟩ ctx)[key] = ty := by
  show (insert' _ _ _)[_]'(_) = _
  unfold insert'
  split
  contradiction
  dsimp
  rw [insert_nodup_get_elem, dif_pos rfl]
  right; rfl

def insert_get_elem_tail (ctx: Context) (key k: Nat) (ty: LamType) (h: k ∈ ctx) : (insert ⟨key, ty⟩ ctx)[k] = ctx[k] := by
  show (insert' _ _ _)[_]'(_) = _
  unfold insert'
  split
  rfl
  dsimp
  rw [insert_nodup_get_elem, dif_neg]
  intro h
  cases h
  contradiction
  left; assumption

@[induction_eliminator]
def ind { motive: Context -> Prop } :
  (nil: motive ∅) ->
  (cons: ∀a as, a.1 ∉ as -> motive as -> motive (insert a as)) ->
  ∀x, motive x := by
  intro nil cons ctx
  cases ctx with | mk ctx nodup =>
  cases ctx with | mk ctx =>
  induction nodup
  exact nil
  rename_i a as a_notin_as as_nodup ih
  have : a.fst ∉ (mk (Multiset.mk _) as_nodup) := by
    intro ⟨_, h⟩
    exact a_notin_as _ h rfl
  have : motive (insert' _ _ _) := cons a _ this ih
  unfold insert' at this
  split at this
  contradiction
  assumption

def get_elem_of_mem_data (ctx: Context) :
  ∀{x}, (h: x ∈ ctx.data) -> ctx[x.1]'⟨_, h⟩ = x.2 := by
    intro x mem
    induction ctx
    contradiction
    rename_i a ctx  not_mem ih
    cases a with | mk a₀ a₁ =>
    simp [insert, insert'] at mem
    split at mem
    rw [insert_get_elem_tail]
    apply ih
    assumption
    rcases Multiset.mem_cons.mp mem with mem | mem
    subst x
    dsimp
    rw [insert_get_elem_head]
    assumption
    rw [insert_get_elem_tail]
    apply ih
    assumption

def mem_erase (key: Nat) (ctx: Context) (h: key ∈ ctx):
  ∀{x}, x ∈ ctx.erase key h ↔ x ∈ ctx ∧ x ≠ key := by
  intro x
  apply Iff.intro
  intro g
  apply flip And.intro
  intro h; cases h
  obtain ⟨v', h⟩ := h
  obtain ⟨v, g⟩ := g
  unfold Context.erase at g
  dsimp at g
  rw [get_elem_of_mem_data _ h] at g
  dsimp at g
  by_cases hv:v=v'
  subst v
  have := (Multiset.count_elem_erase_if_mem _ _ h (n := 2)).mpr (Multiset.MinCount.iff_mem.mpr g)

  -- have := Multiset.mem_erase
  -- have := Multiset.count_elem_erase _ _ (Multiset.MinCount.iff_mem.mpr g)

  -- have := (Multiset.count_elem_erase_if_mem _ _ g).mpr (Multiset.MinCount.iff_mem.mpr g)
  sorry
  sorry

def insert_comm (ctx: Context) (a b: Nat × LamType)
  (ne: a.1 ≠ b.1)
  : insert a (insert b ctx) = insert b (insert a ctx) := by
  cases a with | mk a₀ a₁ =>
  cases b with | mk b₀ b₁ =>
  replace ne: a₀ ≠ b₀ := ne
  show insert' _ _ (insert' _ _ _) = insert' _ _ (insert' _ _ _)
  unfold insert'
  dsimp
  split <;> rename_i hb <;> split <;> rename_i ha
  rfl
  rw [if_pos]
  obtain ⟨_, hb⟩ := hb
  exact ⟨_, Multiset.mem_cons.mpr (.inr hb)⟩
  rw [if_neg, if_pos]
  obtain ⟨_, ha⟩ := ha
  replace ha := Multiset.mem_cons.mp ha
  rcases ha with ha | ha
  exists b₁
  cases ha
  contradiction
  exact ⟨_, ha⟩
  intro ⟨_, mem⟩
  split at mem
  exact hb ⟨_, mem⟩
  obtain ⟨_, ha⟩ := ha
  replace ha := Multiset.mem_cons.mp ha
  rcases ha with ha | ha
  cases ha
  contradiction
  rename_i ha' _
  exact ha' ⟨_, ha⟩
  rw [if_neg, if_neg]
  rw [Multiset.cons_comm]
  intro h
  apply ha
  obtain ⟨_, h⟩ := h
  exact ⟨_, Multiset.mem_cons.mpr (.inr h)⟩
  intro h
  split at h
  obtain ⟨_, h⟩ := h
  exact hb ⟨_, h⟩
  obtain ⟨_, h⟩ := h
  replace h := Multiset.mem_cons.mp h
  rcases h with h | h
  cases h
  contradiction
  exact hb ⟨_, h⟩

def eq_insert_of_mem (x: Nat) (ctx: Context) : x ∈ ctx -> ∃v ctx', ctx = insert ⟨x, v⟩ ctx' ∧ x ∉ ctx' := by
  intro mem
  induction ctx generalizing x with
  | nil =>
    obtain ⟨_, _⟩ := mem
    contradiction
  | cons a as nomem ih =>
    if h:x = a.fst then
      exists a.snd
      exists as
      subst x
      apply And.intro
      rfl
      assumption
    else
      replace h : x ≠ a.fst := h
      cases of_mem_insert mem
      contradiction
      rename_i g
      replace ih := ih x g
      obtain ⟨v, ctx', prf, _⟩ := ih
      refine ⟨v, insert a ctx', ?_, ?_⟩
      · rw [prf]
        rw [insert_comm]
        exact h.symm
      intro g'
      cases of_mem_insert g'
      contradiction
      contradiction

@[ext]
def ext (a b: Context) : (∀{x}, x ∈ a ↔ x ∈ b) -> (∀x (h₀: x ∈ a) (h₁: x ∈ b), a[x] = b[x]) -> a = b := by
  intro mem_iff val_eq
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => rfl
    | cons b bs b_notin_bs ih =>
      have ⟨_, _⟩ := mem_iff.mpr (mem_insert_head _ _)
      contradiction
  | cons a as nomem ih =>
    cases a with | mk a₀ a₁ =>
    have ⟨v, b, eq, a_notin_b'⟩ := eq_insert_of_mem a₀ b (mem_iff.mp (mem_insert_head _ _))
    subst eq
    congr
    have := val_eq a₀ (mem_insert_head _ _) (mem_iff.mp <| mem_insert_head _ _)
    rw [insert_get_elem_head, insert_get_elem_head] at this
    exact this
    assumption
    assumption
    apply ih
    intro x
    apply Iff.intro
    intro h
    cases of_mem_insert <| mem_iff.mp (mem_insert_tail h)
    subst x; contradiction
    assumption
    intro h
    cases of_mem_insert <| mem_iff.mpr (mem_insert_tail h)
    subst x; contradiction
    assumption
    intro x h₀ h₁
    have := val_eq x (mem_insert_tail h₀) (mem_insert_tail h₁)
    rw [insert_get_elem_tail, insert_get_elem_tail] at this
    exact this

def not_mem_remove (key: Nat) (ctx: Context) : key ∉ ctx.remove key := by
  intro h
  obtain ⟨v, h⟩ := h
  unfold remove at h
  dsimp at h
  split at h <;> rename_i hkey
  obtain ⟨v', hkey⟩ := hkey
  obtain ⟨ctx', ctx'_spec⟩  := Multiset.mem_spec.mp hkey
  conv at h => { lhs; rhs; rw [ctx'_spec] }
  have := get_elem_of_mem_data ctx hkey
  dsimp at this
  rw [this] at h; clear this
  rw [Multiset.erase_cons, if_pos rfl] at h
  have := ctx.nodup_keys
  rw [ctx'_spec] at this
  have := this.head _ h
  contradiction
  exact hkey ⟨_ ,h⟩

def mem_remove (key: Nat) (ctx: Context) : ∀{k: Nat}, k ≠ key -> k ∈ ctx -> k ∈ ctx.remove key := by
  intro k ne hk
  unfold remove
  split
  obtain ⟨v, hk⟩ := hk
  exists v
  dsimp
  · cases ctx with | mk ctx nodup =>
    dsimp
    have ⟨ctx', hctx'⟩  := Multiset.mem_spec.mp hk
    dsimp at hctx'
    conv => { lhs; rhs; rw [hctx'] }
    rw [Multiset.erase_cons, if_neg]
    apply Multiset.mem_cons.mpr
    left; rfl
    intro h
    cases h
    contradiction
  · exact hk

def Context.data.inj : Function.Injective Context.data := by
  intro a b eq
  cases a; cases b; congr

def of_mem_remove (key: Nat) (ctx: Context) : ∀{k: Nat}, k ∈ ctx.remove key -> k ∈ ctx ∧ k ≠ key := by
  intro k mem
  apply flip And.intro
  intro h
  subst h
  exact not_mem_remove _ _ mem
  unfold remove at mem
  obtain ⟨v, mem⟩ := mem
  dsimp at mem
  split at mem <;> rename_i h
  have cnt := Multiset.MinCount.iff_mem.mpr mem
  refine ⟨_, Multiset.MinCount.iff_mem.mp <| (Multiset.count_erase _ _ ?_).mpr cnt⟩
  intro h
  cases h
  let ctx' := Context.mk (ctx.data.erase (key, ctx[key])) (by
    apply Multiset.Pairwise.erase
    exact ctx.nodup_keys)
  have : ctx' = ctx.remove key := by
    rw [remove]
    apply Context.data.inj
    dsimp
    rw [dif_pos]
  have : key ∈ ctx.remove key := by
    rw [←this]
    exact ⟨_, mem⟩
  exact not_mem_remove _ _ this
  exact ⟨_, mem⟩

def remove_insert (ne: x ≠ y.fst): remove x (insert y ctx) = insert y (remove x ctx) := by
  apply Context.data.inj
  simp [insert, remove, insert']
  repeat any_goals split

  split <;> split <;> rename_i h g
  any_goals rfl
  split <;> rename_i h'
  rfl
  exfalso; apply h'
  obtain ⟨v, h⟩ := h
  refine ⟨v, ?_⟩
  dsimp
  apply Multiset.MinCount.iff_mem.mp
  apply (Multiset.count_erase _ _ _).mp
  apply Multiset.MinCount.iff_mem.mpr
  assumption
  intro h
  have := (Prod.mk.inj h).left
  contradiction
  split <;> rename_i h'
  split




  rw [if_pos]

  sorry

end Context

inductive LamTerm.IsWellFormed : Context -> LamTerm -> Prop where
| Panic (body: LamTerm) (ty: LamType):
  IsWellFormed ctx body ->
  IsWellFormed ctx (.Panic body ty)
| Lambda (arg_name: Nat) (arg_ty: LamType) (body: LamTerm):
  -- lambdas must introduce new names into the context
  arg_name ∉ ctx ->
  IsWellFormed (insert ⟨arg_name, arg_ty⟩ ctx) body ->
  IsWellFormed ctx (.Lambda arg_name arg_ty body)
| App (func arg: LamTerm) :
  IsWellFormed ctx func ->
  IsWellFormed ctx arg ->
  IsWellFormed ctx (.App func arg)
| Var (name: Nat) :
  name ∈ ctx ->
  IsWellFormed ctx (.Var name)

inductive LamTerm.IsWellTyped : Context -> LamTerm -> LamType -> Prop where
| Panic (body: LamTerm) (ty: LamType):
  IsWellTyped ctx body .Void ->
  IsWellTyped ctx (.Panic body ty) ty
| Lambda (arg_name: Nat) (arg_ty ret_ty: LamType) (body: LamTerm):
  -- lambdas must introduce new names into the context
  arg_name ∉ ctx ->
  IsWellTyped (insert ⟨arg_name, arg_ty⟩ ctx) body ret_ty ->
  IsWellTyped ctx (.Lambda arg_name arg_ty body) (.Func arg_ty ret_ty)
| App (arg_ty ret_ty: LamType) (func arg: LamTerm) :
  IsWellTyped ctx func (.Func arg_ty ret_ty) ->
  IsWellTyped ctx arg arg_ty ->
  IsWellTyped ctx (.App func arg) ret_ty
| Var (name: Nat) (ty: LamType) (h: name ∈ ctx) :
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

inductive LamTerm.Introduces (name: Nat) : LamTerm -> Prop where
| AppFunc func arg: Introduces name func -> Introduces name (.App func arg)
| AppArg func arg: Introduces name arg -> Introduces name (.App func arg)
| Panic body ty: Introduces name body -> Introduces name (.Panic body ty)
| LambdaBody n ty body: Introduces name body -> Introduces name (.Lambda n ty body)
| Lambda ty body: Introduces name (.Lambda name ty body)

def LamTerm.subst (term subst: LamTerm) (name: Nat) : LamTerm :=
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
    exact ih x (Context.mem_insert_tail mem) i
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
    apply Context.mem_insert_tail
    assumption
  | Lambda arg_name _ _ _  _ ih =>
    apply IsWellFormed.Lambda
    intro h
    cases Context.of_mem_insert h
    subst arg_name
    apply nointro
    apply Introduces.Lambda
    contradiction
    rw [Context.insert_comm]
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
  {term subst: LamTerm} {name: Nat}:
  name ∈ ctx ->
  term.IsWellFormed ctx ->
  subst.IsWellFormed (ctx.remove name) ->
  term.NoCommonIntroductions subst ->
  (term.subst subst name).IsWellFormed (ctx.remove name) := by
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
    have ⟨arg_in_ctx, _⟩  := Context.of_mem_remove _ _ mem
    contradiction
    rw [←Context.remove_insert]
    apply ih
    apply Context.mem_insert_tail
    assumption
    · rw [Context.remove_insert]
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
    apply Context.mem_remove
    assumption
    assumption
