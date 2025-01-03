import Math.Data.Multiset.Basic

inductive LamType where
| Void
| Unit
| Func (arg ret: LamType)
deriving DecidableEq

inductive LamTerm where
| ConstUnit
| Panic (body: LamTerm) (ty: LamType)
| Lambda (arg_name: Nat) (arg_ty: LamType) (body: LamTerm)
| App (func arg: LamTerm)
| Var (name: Nat)

def nodup_keys (data: Multiset (Nat × LamType)) := data.Pairwise <| fun x y => x.1 ≠ y.1

structure Context: Type where
  data: Multiset (Nat × LamType)
  nodup_keys: nodup_keys data

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

-- inserts key into ctx iff it doesn't already exist in ctx
def Context.insert' (key: Nat) (ty: LamType) (ctx: Context) : Context where
  data :=
    if key ∈ ctx then
      ctx.data
    else
      ⟨key, ty⟩ ::ₘ ctx.data
  nodup_keys := by
    split <;> rename_i h
    exact ctx.nodup_keys
    apply ctx.nodup_keys.cons
    intro ⟨k, v⟩ mem eq
    apply h
    dsimp at eq
    subst k
    exists v

instance : EmptyCollection Context where
  emptyCollection := { data := ∅, nodup_keys := Multiset.Pairwise.nil }

instance : Insert (Nat × LamType) Context where
  insert x := Context.insert' x.1 x.2

instance : Singleton (Nat × LamType) Context where
  singleton := (insert · ∅)

instance : GetElem Context Nat LamType (fun ctx name => name ∈ ctx) where
  getElem ctx name prf := by
    apply Quotient.hrecOn ctx.data (motive := fun list => (∃v, Multiset.mem  ⟨name, v⟩ list) -> nodup_keys list -> LamType)
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

def Context.mem_insert'_head (key: Nat) (ty: LamType) (ctx: Context) :
  key ∈ ctx.insert' key ty := by
  unfold insert'
  split
  rename_i h
  show ∃_, _
  assumption
  exists ty
  apply Multiset.mem_head

def Context.mem_insert'_tail (k key: Nat) (ty: LamType) (ctx: Context) :
  k ∈ ctx ->
  k ∈ ctx.insert' key ty := by
  intro h
  unfold insert'
  split
  rename_i h
  show ∃_, _
  assumption
  obtain ⟨v, mem⟩ := h
  exists v
  apply Multiset.mem_tail
  assumption

def Context.of_mem_insert' (k key: Nat) (ty: LamType) (ctx: Context) :
  k ∈ ctx.insert' key ty ->
  k = key ∨ k ∈ ctx := by
  intro h
  unfold insert' at h
  split at h
  right; assumption
  obtain ⟨_, h⟩ := h
  rcases Multiset.mem_cons.mp h with h | h
  cases h
  left; rfl
  right; exact ⟨_ ,h⟩

def Context.mem_insert_head (x: Nat × LamType) (ctx: Context) :
  x.1 ∈ insert x ctx := by
  apply mem_insert'_head

def Context.mem_insert_tail {x: Nat} {y: Nat × LamType} {ctx: Context} :
  x ∈ ctx ->
  x ∈ insert y ctx := by
  apply mem_insert'_tail

def Context.of_mem_insert {x: Nat} {y: Nat × LamType} {ctx: Context} :
  x ∈ insert y ctx ->
  x = y.fst ∨ x ∈ ctx := by
  apply of_mem_insert'

macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply Context.mem_insert_head)
macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply Context.mem_insert_tail; get_elem_tactic)

def Context.insert_get_elem_head (ctx: Context) (key: Nat) (ty: LamType) (h: key ∉ ctx) : (insert ⟨key, ty⟩ ctx)[key] = ty := by
  show (insert' _ _ _)[_]'(_) = _
  unfold insert'
  cases ctx with | mk ctx nodup =>
  cases ctx with | mk ctx =>
  split <;> show Option.getD _ LamType.Void = _
  contradiction
  unfold List.find?
  dsimp
  rw [decide_eq_true_iff.mpr rfl]
  rfl

def Context.insert_get_elem_tail (ctx: Context) (key k: Nat) (ty: LamType) (h: k ∈ ctx) : (insert ⟨key, ty⟩ ctx)[k] = ctx[k] := by
  show (insert' _ _ _)[_]'(_) = _
  unfold insert'
  cases ctx with | mk ctx nodup =>
  cases ctx with | mk ctx =>
  split <;> show Option.getD _ LamType.Void = _
  rfl
  have k_ne_key : k ≠ key := by
    intro eq
    cases eq; contradiction
  unfold List.find?
  dsimp
  rw [decide_eq_false_iff_not.mpr k_ne_key.symm]
  rfl

@[induction_eliminator]
def Context.ind { motive: Context -> Prop } :
  (nil: motive ∅) ->
  (cons: ∀a as, a.1 ∉ as -> motive as -> motive (insert a as)) ->
  ∀x, motive x := by
  intro nil cons ctx
  cases ctx with | mk ctx nodup =>
  cases ctx with | mk ctx =>
  induction nodup
  exact nil
  rename_i a as a_notin_as as_nodup ih
  have : a.fst ∉ (Context.mk (Multiset.mk _) as_nodup) := by
    intro ⟨_, h⟩
    exact a_notin_as _ h rfl
  have : motive (insert' _ _ _) := cons a _ this ih
  unfold insert' at this
  split at this
  contradiction
  assumption

def Context.insert_comm (ctx: Context) (a b: Nat × LamType)
  (ne: a.1 ≠ b.1)
  : insert a (insert b ctx) = insert b (insert a ctx) := by
  cases a with | mk a₀ a₁ =>
  cases b with | mk b₀ b₁ =>
  replace ne: a₀ ≠ b₀ := ne
  show insert' _ _ (insert' _ _ _) = insert' _ _ (insert' _ _ _)
  unfold insert'
  dsimp
  congr 1
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

def Context.eq_insert_of_mem (x: Nat) (ctx: Context) : x ∈ ctx -> ∃v ctx', ctx = insert ⟨x, v⟩ ctx' ∧ x ∉ ctx' := by
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
def Context.ext (a b: Context) : (∀{x}, x ∈ a ↔ x ∈ b) -> (∀x (h₀: x ∈ a) (h₁: x ∈ b), a[x] = b[x]) -> a = b := by
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

inductive LamTerm.WellFormed : Context -> LamTerm -> Prop where
| ConstUnit: WellFormed ctx .ConstUnit
| Panic (body: LamTerm) (ty: LamType):
  WellFormed ctx body ->
  WellFormed ctx (.Panic body ty)
| Lambda (arg_name: Nat) (arg_ty: LamType) (body: LamTerm):
  -- lambdas must introduce new names into the context
  arg_name ∉ ctx ->
  WellFormed (insert ⟨arg_name, arg_ty⟩ ctx) body ->
  WellFormed ctx (.Lambda arg_name arg_ty ty)
| App (func arg: LamTerm) :
  WellFormed ctx func ->
  WellFormed ctx arg ->
  WellFormed ctx (.App func arg)
| Var (name: Nat) :
  name ∈ ctx ->
  WellFormed ctx (.Var name)
