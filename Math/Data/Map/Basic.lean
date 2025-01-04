import Math.Data.Multiset.Basic

def NodupKeys (data: Multiset (α × β)) := data.Pairwise <| fun x y => x.1 ≠ y.1

structure Map (α β: Type*) where
  data: Multiset (α × β)
  nodup_keys: NodupKeys data

namespace Map

variable {α β: Type*}

def data.inj : Function.Injective (Map.data (α := α) (β := β)) := by
  intro a b eq
  cases a; cases b; congr

def MinKeyCount (map: Map α β) (key: α) (n: Nat) := map.data.MinCountBy (·.1 = key) n
def nodup_keys_MinKeyCount (map: Map α β) : ∀name n, map.MinKeyCount name n -> n ≤ 1 := by
  intro name n cnt
  unfold Map.MinKeyCount at cnt
  cases map with | mk ctx nodup =>
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

def Context.MinNameCount.ofMinCount_data (map: Map α β) : ∀x n, map.data.MinCount x n -> map.MinKeyCount x.fst n := by
  intro name n
  apply Multiset.MinCountBy.subPredicate
  intro x mem eq
  rw [eq]

instance : Membership α (Map α β) where
  mem ctx name := ∃v, ⟨name, v⟩ ∈ ctx.data

instance [DecidableEq α] (x: α) (map: Map α β) : Decidable (x ∈ map) :=
  decidable_of_iff (∃y ∈ map.data, x = y.1) <| by
    apply Iff.intro
    intro ⟨⟨k, v⟩, mem, eq⟩
    exists v
    subst x
    assumption
    intro ⟨v, mem⟩
    exists ⟨x, v⟩

instance [DecidableEq α] : GetElem (Map α β) α β (fun ctx name => name ∈ ctx) where
  getElem ctx name prf := by
    apply Quotient.hrecOn ctx.data (motive := fun list => (∃v, Multiset.mem  ⟨name, v⟩ list) -> NodupKeys list -> β)
    case f =>
      intro list mem _
      apply Option.get _ _
      apply Option.map _
      exact list.find? fun ⟨k, v⟩ => k = name
      exact Prod.snd
      simp
      exact mem
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
      congr 1
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

-- insert a new key into the context
def insert_no_dup (key: α) (v: β) (ctx: Map α β) (h: key ∉ ctx) : Map α β where
  data := ctx.data.cons ⟨key, v⟩
  nodup_keys := by
    apply ctx.nodup_keys.cons
    intro x g
    intro eq; subst eq
    exact h ⟨_, g⟩

def mem_insert_no_dup {key: α} {val: β} {map: Map α β} {h: key ∉ map}:
  ∀{x}, x ∈ map.insert_no_dup key val h ↔ x ∈ map ∨ x = key := by
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
  exists val
  apply Multiset.mem_cons.mpr
  left; rw [g]

macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply mem_insert_no_dup.mpr; left; get_elem_tactic)
macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|apply mem_insert_no_dup.mpr; right; get_elem_tactic)

variable [DecidableEq α]

def insert_nodup_get_elem (map: Map α β) (key: α) (val: β) (h: key ∉ map) (g: name ∈ map ∨ name = key) :
  (insert_no_dup key val map h)[name]'(mem_insert_no_dup.mpr g) = if hkey:name = key then val else map[name]'(by
    cases g
    assumption
    contradiction) := by
  unfold insert_no_dup
  cases map with | mk map nodup =>
  cases map with | mk map =>
  show Option.get _ _ = if h:name = key then _ else Option.get _ _
  dsimp
  split
  rw [Option.get_eq_getD (fallback := val), Option.getD_eq_iff]; left
  rename_i h
  rw [List.find?, decide_eq_true h.symm]
  rfl
  congr 2
  rw [List.find?]
  rw [decide_eq_false_iff_not.mpr]
  dsimp; intro h; cases h; contradiction

instance : EmptyCollection (Map α β) where
  emptyCollection := { data := ∅, nodup_keys := Multiset.Pairwise.nil }

@[induction_eliminator]
def ind { motive: Map α β -> Prop } :
  (nil: motive ∅) ->
  (cons: ∀k v as, (h: k ∉ as) -> motive as -> motive (insert_no_dup k v as h)) ->
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
  exact cons a.fst a.snd _ this ih

def get_elem_of_mem_data (map: Map α β) :
  ∀{x}, (h: x ∈ map.data) -> map[x.1]'⟨_, h⟩ = x.2 := by
    intro x mem
    induction map
    contradiction
    rename_i k v map not_mem ih
    dsimp [insert_no_dup] at mem
    cases mem using Multiset.cases_mem_cons
    dsimp
    rw [insert_nodup_get_elem, dif_pos rfl]
    right; rfl
    rw [insert_nodup_get_elem, dif_neg]
    apply ih
    assumption
    intro
    subst k
    rename_i h
    exact not_mem ⟨_, h⟩
    left
    rename_i h
    exact ⟨_, h⟩

-- remove a key from ctx
def erase (key: α) (map: Map α β) : Map α β where
  data := map.data.eraseP (fun k => key = k.1) <| by
    intro x y hx hy px py
    dsimp at px py
    ext
    rw [←of_decide_eq_true px, ←of_decide_eq_true py]
    rw [←get_elem_of_mem_data _ hx, ←get_elem_of_mem_data _ hy]
    congr 1
    rw [←of_decide_eq_true px, ←of_decide_eq_true py]
  nodup_keys := by
    apply Multiset.Pairwise.sub
    apply Multiset.eraseP_sub
    exact map.nodup_keys

instance : Insert (α × β) (Map α β) where
  insert | ⟨key, val⟩, map => if h:key ∈ map then map else map.insert_no_dup key val h

def not_mem_erase {map: Map α β} : key ∉ map.erase key := by
  intro h
  obtain ⟨v', h⟩ := h
  cases map with | mk map nodup =>
  unfold erase at h; dsimp at h
  induction map with
  | nil => contradiction
  | cons kv map ih =>
    obtain ⟨k, v⟩ := kv
    rw [Multiset.eraseP_cons] at h
    split at h <;> (rename_i g; dsimp at g)
    cases of_decide_eq_true g
    exact nodup.head _ h rfl
    have ne : key ≠ k := of_decide_eq_false (Bool.eq_false_iff.mpr g)
    replace h := Multiset.mem_cons.mp h
    rcases h with h | h
    cases h
    contradiction
    exact ih nodup.tail h

def erase_insert_no_dup_comm_of_ne {k v key} {map: Map α β} (h: k ≠ key) (g: k ∉ map) :
  (map.insert_no_dup k v g).erase key = ((map.erase key).insert_no_dup k v <| by
    intro mem_erase
    obtain ⟨v', h'⟩ := mem_erase
    have := Multiset.MinCount.iff_mem.mp <| Multiset.eraseP_sub _ _ (Multiset.MinCount.iff_mem.mpr h')
    exact g ⟨_, this⟩) := by
  unfold erase insert_no_dup
  dsimp
  congr
  rw [Multiset.eraseP_cons, if_neg]
  intro g
  exact h (of_decide_eq_true g).symm

def erase_insert_no_dup_cancel {k v} {map: Map α β} (g: k ∉ map) :
  (map.insert_no_dup k v g).erase k = map := by
  unfold erase insert_no_dup
  dsimp
  congr
  rw [Multiset.eraseP_cons, if_pos]
  apply decide_eq_true_iff.mpr rfl

def mem_erase {map: Map α β} : ∀{x}, x ∈ map.erase key ↔ x ∈ map ∧ x ≠ key := by
  intro x
  induction map with
  | nil =>
    apply Iff.intro
    intro h
    obtain ⟨_, _⟩ := h
    contradiction
    intro h
    obtain ⟨⟨_, _⟩, _⟩ := h
    contradiction
  | cons k v map k_notin_map ih =>
    by_cases h:k=key
    subst k; rw [erase_insert_no_dup_cancel]
    apply Iff.intro
    intro x_in_map
    apply And.intro
    apply mem_insert_no_dup.mpr; left; assumption
    intro h
    subst x; contradiction
    intro ⟨mem, ne⟩
    cases mem_insert_no_dup.mp mem <;> trivial
    rw [erase_insert_no_dup_comm_of_ne h]
    apply Iff.intro
    intro mem
    replace mem := mem_insert_no_dup.mp mem
    rcases mem with mem | eq
    have ⟨mem, ne⟩  := ih.mp mem
    apply And.intro _ ne
    apply mem_insert_no_dup.mpr; left; assumption
    subst k
    apply And.intro _ h
    apply mem_insert_no_dup.mpr; right; rfl
    intro ⟨mem, ne⟩
    apply mem_insert_no_dup.mpr
    rcases mem_insert_no_dup.mp mem with mem | eq
    left; apply ih.mpr
    apply And.intro <;> assumption
    right; assumption

def insert_no_dup_comm {map: Map α β} {k₀ k₁ v₀ v₁} (h₀: k₀ ∉ map) (h₁: k₁ ∉ map) (h₂: k₀ ≠ k₁):
  insert_no_dup k₀ v₀ (map.insert_no_dup k₁ v₁ h₁) (by
    intro mem
    cases mem_insert_no_dup.mp mem <;> contradiction) = insert_no_dup k₁ v₁ (map.insert_no_dup k₀ v₀ h₀) (by
    intro mem
    have := h₂.symm
    cases mem_insert_no_dup.mp mem <;> contradiction) := by
    unfold insert_no_dup
    congr 1
    dsimp
    rw [Multiset.cons_comm]

def eq_insert_of_mem (x: α) (ctx: Map α β) : x ∈ ctx -> ∃v map' h, ctx = insert_no_dup x v map' h := by
  intro mem
  induction ctx generalizing x with
  | nil =>
    obtain ⟨_, _⟩ := mem
    contradiction
  | cons a₀ a₁ as nomem ih =>
    if h:x = a₀ then
      exists a₁
      exists as
      subst x
      refine ⟨?_, ?_⟩
      assumption
      simp [insert]
    else
      replace h : x ≠ a₀ := h
      have ⟨v, map', x_not_in_map', as_eq⟩ := ih x (by
        cases mem_insert_no_dup.mp mem
        assumption
        contradiction)
      subst as
      refine ⟨v, insert_no_dup a₀ a₁ map' ?_, ?_, ?_⟩
      intro mem'
      apply nomem
      apply mem_insert_no_dup.mpr
      left; assumption
      intro mem'
      cases mem_insert_no_dup.mp mem'
      contradiction
      contradiction
      rw [insert_no_dup_comm]
      symm; assumption

@[ext]
def ext (a b: Map α β) :
  (∀{k}, k ∈ a ↔ k ∈ b) ->
  (∀k (h₀: k ∈ a) (h₁: k ∈ b), a[k] = b[k]) ->
  a = b := by
  intro mem_iff val_eq
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => rfl
    | cons b bs b_notin_bs ih =>
      have ⟨_, _⟩ := mem_iff.mpr (mem_insert_no_dup.mpr (.inr rfl))
      contradiction
  | cons a₀ a₁ as nomem ih =>
    have ⟨v, b, a₀_notin_map', eq⟩ := eq_insert_of_mem a₀ b (mem_iff.mp <| mem_insert_no_dup.mpr <| .inr rfl)
    subst eq
    congr
    have := val_eq a₀ (mem_insert_no_dup.mpr (.inr rfl)) (mem_insert_no_dup.mpr (.inr rfl))
    rw [insert_nodup_get_elem, insert_nodup_get_elem, dif_pos rfl, dif_pos rfl] at this
    assumption
    right; rfl; right; rfl
    apply ih
    · intro k
      apply Iff.intro
      intro mem
      cases mem_insert_no_dup.mp (mem_iff.mp (mem_insert_no_dup.mpr (.inl mem)))
      assumption
      subst k
      contradiction
      intro mem
      cases mem_insert_no_dup.mp (mem_iff.mpr (mem_insert_no_dup.mpr (.inl mem)))
      assumption
      subst k
      contradiction
    · intro k h₀ h₁
      have := val_eq k (mem_insert_no_dup.mpr (.inl h₀)) (mem_insert_no_dup.mpr (.inl h₁))
      rw [insert_nodup_get_elem, insert_nodup_get_elem, dif_neg, dif_neg] at this
      assumption
      intro h
      exact a₀_notin_map' (h ▸ h₁)
      intro h
      exact a₀_notin_map' (h ▸ h₁)
      left; assumption
      left; assumption

def mem_insert {kv: α × β} {map: Map α β}:
  ∀{x}, x ∈ insert kv map ↔ x ∈ map ∨ x = kv.1 := by
  intro x
  simp [insert]
  split
  apply Iff.intro .inl
  intro h
  cases h
  assumption
  subst x
  assumption
  apply mem_insert_no_dup

def insert_comm {x y: α × β} {map: Map α β} (h: x.1 ≠ y.1):
  insert x (insert y map) = insert y (insert x map) := by
  simp [insert]
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
  have := h.symm
  contradiction
  rw [insert_no_dup_comm]
  assumption

def erase_insert_comm_of_ne {key} {map: Map α β} (h: x.fst ≠ key) :
  (insert x map).erase key = (insert x  (map.erase key)) := by
  simp [insert]
  split <;> split
  rfl
  rename_i h₀ h₁
  have := h₁ (mem_erase.mpr ⟨h₀, h⟩)
  contradiction
  rename_i h₀ h₁
  have := h₀ (mem_erase.mp h₁).left
  contradiction
  rw [erase_insert_no_dup_comm_of_ne]
  assumption

def insert_get_elem_tail {key} {map: Map α β} (h: key ∈ map) :
  (insert x map)[key]'(mem_insert.mpr (.inl h)) = map[key]  := by
  simp [insert]
  split
  rfl
  rw [insert_nodup_get_elem, dif_neg]
  intro h
  subst h
  contradiction
  left
  assumption

def erase_get_elem {map: Map α β} (h: key ∈ erase k map) :
  (erase k map)[key] = map[key]'(mem_erase.mp h).left := by
  obtain ⟨v, h⟩ := h
  rw [get_elem_of_mem_data _ h]
  unfold erase at h
  have := Multiset.sub_mem Multiset.eraseP_sub h
  rw [get_elem_of_mem_data _ this]

end Map
