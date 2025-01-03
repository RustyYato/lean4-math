import Math.Data.Multiset.Basic

def Name := Nat
def Name.ofNat : Nat -> Name := id
def Name.toNat : Name -> Nat := id
instance : DecidableEq Name := inferInstanceAs (DecidableEq Nat)
instance : Repr Name := inferInstanceAs (Repr Nat)
attribute [irreducible] Name

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

structure Context: Type where
  data: Multiset (Name × LamType)
  nodup_keys: nodup_keys data

def Context.data.inj : Function.Injective Context.data := by
  intro a b eq
  cases a; cases b; congr

def Context.MinNameCount (ctx: Context) (name: Name) (n: Nat) := ctx.data.MinCountBy (·.1 = name) n
def Context.nodup_keys_MinNameCount (ctx: Context) : ∀name n, ctx.MinNameCount name n -> n ≤ 1 := by
  intro name n cnt
  unfold Context.MinNameCount at cnt
  cases ctx with | mk ctx nodup =>
  dsimp at cnt
  induction cnt with
  | nil => apply Nat.zero_le
  | cons a as n cnt ih =>
    apply ih
    exact Multiset.Pairwise.tail nodup
  | head a as n c h ih =>
    apply Nat.succ_le_succ
    cases n with
    | zero => apply Nat.zero_le
    | succ n =>
    exfalso
    have ⟨x, x_in_as, prf⟩ := Multiset.MinCountBy.one_iff.mp (c.reduce _ (Nat.le_add_left _ _))
    subst name
    exact nodup.head x x_in_as prf.symm

def Context.MinNameCount.ofMinCount_data (ctx: Context) : ∀x n, ctx.data.MinCount x n -> ctx.MinNameCount x.fst n := by
  intro name n
  apply Multiset.MinCountBy.subPredicate
  intro x mem eq
  rw [eq]

namespace Context

instance : Membership Name Context where
  mem ctx name := ∃v, ⟨name, v⟩ ∈ ctx.data

instance (x: Name) (ctx: Context) : Decidable (x ∈ ctx) :=
  decidable_of_iff (∃y ∈ ctx.data, x = y.1) <| by
    apply Iff.intro
    intro ⟨⟨k, v⟩, mem, eq⟩
    exists v
    subst x
    assumption
    intro ⟨v, mem⟩
    exists ⟨x, v⟩

instance : GetElem Context Name LamType (fun ctx name => name ∈ ctx) where
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
def erase (key: Name) (ctx: Context) (h: key ∈ ctx) : Context where
  data := ctx.data.erase ⟨key, ctx[key]⟩
  nodup_keys := by
    apply Multiset.Pairwise.erase
    exact ctx.nodup_keys

-- insert a new key into the context
def insert_no_dup (key: Name) (v: LamType) (ctx: Context) (h: key ∉ ctx) : Context where
  data := ctx.data.cons ⟨key, v⟩
  nodup_keys := by
    apply ctx.nodup_keys.cons
    intro x g
    intro eq; subst eq
    exact h ⟨_, g⟩

-- inserts key into ctx iff it doesn't already exist in ctx
def insert' (key: Name) (ty: LamType) (ctx: Context) : Context :=
  if h:key ∈ ctx then
    ctx
  else
    ctx.insert_no_dup key ty h

-- remove a key from ctx
def remove (key: Name) (ctx: Context) : Context :=
  if h:key ∈ ctx then
    ctx.erase key h
  else
    ctx

instance : EmptyCollection Context where
  emptyCollection := { data := ∅, nodup_keys := Multiset.Pairwise.nil }

instance : Insert (Name × LamType) Context where
  insert x := insert' x.1 x.2

instance : Singleton (Name × LamType) Context where
  singleton := (insert · ∅)

def mem_insert_no_dup {key: Name} {ty: LamType} {ctx: Context} {h: key ∉ ctx}:
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

def mem_insert'_head (key: Name) (ty: LamType) (ctx: Context) :
  key ∈ ctx.insert' key ty := by
  unfold insert'
  split
  assumption
  apply mem_insert_no_dup.mpr
  right; rfl

def mem_insert'_tail (k key: Name) (ty: LamType) (ctx: Context) :
  k ∈ ctx ->
  k ∈ ctx.insert' key ty := by
  intro h
  unfold insert'
  split
  assumption
  apply mem_insert_no_dup.mpr
  left; assumption

def of_mem_insert' (k key: Name) (ty: LamType) (ctx: Context) :
  k ∈ ctx.insert' key ty ->
  k = key ∨ k ∈ ctx := by
  intro h
  unfold insert' at h
  split at h
  right; assumption
  exact (mem_insert_no_dup.mp h).symm

def mem_insert_head (x: Name × LamType) (ctx: Context) :
  x.1 ∈ insert x ctx := by
  apply mem_insert'_head

def mem_insert_tail {x: Name} {y: Name × LamType} {ctx: Context} :
  x ∈ ctx ->
  x ∈ insert y ctx := by
  apply mem_insert'_tail

def of_mem_insert {x: Name} {y: Name × LamType} {ctx: Context} :
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

def insert_nodup_get_elem (ctx: Context) (key: Name) (ty: LamType) (h: key ∉ ctx) (g: name ∈ ctx ∨ name = key) :
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

def insert_get_elem_head (ctx: Context) (key: Name) (ty: LamType) (h: key ∉ ctx) : (insert ⟨key, ty⟩ ctx)[key] = ty := by
  show (insert' _ _ _)[_]'(_) = _
  unfold insert'
  split
  contradiction
  dsimp
  rw [insert_nodup_get_elem, dif_pos rfl]
  right; rfl

def insert_get_elem_tail (ctx: Context) (key k: Name) (ty: LamType) (h: k ∈ ctx) : (insert ⟨key, ty⟩ ctx)[k] = ctx[k] := by
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

def not_mem_erase (key: Name) (ctx: Context) (h: key ∈ ctx) : key ∉ ctx.erase key h := by
  intro g
  unfold erase at g
  obtain ⟨v, g⟩ := g
  dsimp at g
  obtain ⟨w, h⟩ := h
  rw [get_elem_of_mem_data _ h] at g
  dsimp at g
  have := Multiset.erase_sub (x₀ := ⟨key, w⟩) (as := ctx.data)
  replace this := Multiset.sub_mem this g
  replace this := get_elem_of_mem_data _ this; dsimp at this
  rw [get_elem_of_mem_data _ h] at this; dsimp at this
  subst v
  have := (Multiset.count_elem_erase_if_mem (key, w) (n := 2) _ h).mpr (Multiset.MinCount.iff_mem.mpr g)
  have := Context.MinNameCount.ofMinCount_data _ _ _ this
  have := ctx.nodup_keys_MinNameCount _ _ this
  contradiction

def not_mem_remove (key: Name) (ctx: Context) : key ∉ ctx.remove key := by
  unfold remove
  split
  apply not_mem_erase
  assumption

def mem_erase {key: Name} {ctx: Context} {h: key ∈ ctx}: ∀{x}, x ∈ ctx.erase key h ↔ x ∈ ctx ∧ x ≠ key := by
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
  · have := Multiset.erase_sub (x₀ := ⟨key, v'⟩) (as := ctx.data)
    replace this := Multiset.sub_mem this g
    replace this := get_elem_of_mem_data _ this; dsimp at this
    rw [get_elem_of_mem_data _ h] at this; dsimp at this
    subst v'
    apply not_mem_erase key ctx ⟨_, h⟩
    unfold erase
    refine ⟨v, ?_⟩
    dsimp
    rw [get_elem_of_mem_data _ h]
    exact g
  obtain ⟨v, h⟩ := h
  obtain ⟨v', g⟩ := g
  unfold erase at g
  dsimp at g
  rw [get_elem_of_mem_data _ h] at g
  have := Multiset.erase_sub (x₀ := ⟨key, v⟩) (as := ctx.data)
  exact ⟨_, Multiset.sub_mem this g⟩
  · intro ⟨mem, ne⟩
    obtain ⟨v, mem⟩ := mem
    refine ⟨v, ?_⟩
    apply Multiset.MinCount.iff_mem.mp
    unfold erase; dsimp
    apply (Multiset.count_erase _ _ _).mp
    apply Multiset.MinCount.iff_mem.mpr
    assumption
    intro h
    apply ne
    exact (Prod.mk.inj h).left.symm

def insert_no_dup_comm (ctx: Context) (a b: Name × LamType)
  (ne: a.1 ≠ b.1) (ha: a.1 ∉ ctx) (hb: b.1 ∉ ctx)
  : insert_no_dup a.1 a.2 (insert_no_dup b.1 b.2 ctx hb) (by
    intro h
    cases mem_insert_no_dup.mp h
    contradiction
    contradiction) = insert_no_dup b.1 b.2 (insert_no_dup a.1 a.2 ctx ha) (by
    intro h
    cases mem_insert_no_dup.mp h
    contradiction
    apply ne.symm
    assumption) := by
  unfold insert_no_dup
  apply Context.data.inj
  dsimp
  rw [Multiset.cons_comm]

def insert_comm (ctx: Context) (a b: Name × LamType)
  (ne: a.1 ≠ b.1)
  : insert a (insert b ctx) = insert b (insert a ctx) := by
  cases a with | mk a₀ a₁ =>
  cases b with | mk b₀ b₁ =>
  replace ne: a₀ ≠ b₀ := ne
  show insert' _ _ (insert' _ _ _) = insert' _ _ (insert' _ _ _)
  unfold insert'
  dsimp
  have ne' := ne.symm
  repeat any_goals split
  any_goals rfl
  any_goals
    exfalso
    rename ¬_ ∈ insert_no_dup _ _ _ _ => h₂
    apply h₂
    apply mem_insert_no_dup.mpr
    left; assumption
  any_goals
    exfalso
    rename_i h₀ h₁ h₂
    cases mem_insert_no_dup.mp h₀
    contradiction
    contradiction
  exfalso
  rename_i _ _ h₁ h₀
  cases mem_insert_no_dup.mp h₀
  contradiction
  contradiction
  rw [insert_no_dup_comm _ (a₀, a₁) (b₀, b₁)]
  assumption

def eq_insert_of_mem (x: Name) (ctx: Context) : x ∈ ctx -> ∃v ctx', ctx = insert ⟨x, v⟩ ctx' ∧ x ∉ ctx' := by
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

def mem_remove (key: Name) (ctx: Context) : ∀{k: Name}, k ≠ key -> k ∈ ctx -> k ∈ ctx.remove key := by
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

def of_mem_remove (key: Name) (ctx: Context) : ∀{k: Name}, k ∈ ctx.remove key -> k ∈ ctx ∧ k ≠ key := by
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
  {term subst: LamTerm} {name: Name}:
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
