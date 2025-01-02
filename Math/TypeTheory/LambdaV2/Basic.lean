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

structure Context: Type where
  data: Multiset (Nat × LamType)
  nodup_keys: data.Pairwise <| fun x y => x.1 ≠ y.1

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
def Context.insert (key: Nat) (ty: LamType) (ctx: Context) : Context where
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
  insert x := Context.insert x.1 x.2

instance : Singleton (Nat × LamType) Context where
  singleton := (insert · ∅)

instance : GetElem Context Nat LamType (fun ctx name => name ∈ ctx) where
  getElem ctx name prf := by
    apply Quotient.hrecOn ctx.data (motive := fun list => (∃v, Multiset.mem  ⟨name, v⟩ list) -> Multiset.Pairwise (fun x y => x.1 ≠ y.1) list -> LamType)
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

def Context.mem_insert_head (key: Nat) (ty: LamType) (ctx: Context) :
  key ∈ ctx.insert key ty := by
  unfold insert
  split
  rename_i h
  show ∃_, _
  assumption
  exists ty
  apply Multiset.mem_head

def Context.mem_insert_tail (k key: Nat) (ty: LamType) (ctx: Context) :
  k ∈ ctx ->
  k ∈ ctx.insert key ty := by
  intro h
  unfold insert
  split
  rename_i h
  show ∃_, _
  assumption
  obtain ⟨v, mem⟩ := h
  exists v
  apply Multiset.mem_tail
  assumption

macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply Context.mem_insert_head)
macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply Context.mem_insert_tail; get_elem_tactic)

def Context.insert_get_elem_head (ctx: Context) (key: Nat) (ty: LamType) (h: key ∉ ctx) : (ctx.insert key ty)[key] = ty := by
  unfold insert
  cases ctx with | mk ctx nodup =>
  cases ctx with | mk ctx =>
  split <;> show Option.getD _ LamType.Void = _
  contradiction
  unfold List.find?
  dsimp
  rw [decide_eq_true_iff.mpr rfl]
  rfl

def Context.insert_get_elem_tail (ctx: Context) (key k: Nat) (ty: LamType) (h: k ∈ ctx) : (ctx.insert key ty)[k] = ctx[k] := by
  unfold insert
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

infix:65 "::*" => Context.push
