import Math.Logic.Basic
import Math.Function.Basic

inductive List.MinCount : List α -> α -> Nat -> Prop where
| nil x : MinCount [] x 0
| cons x a as n : MinCount as x n -> MinCount (a::as) x n
| head a as n : MinCount as a n -> MinCount (a::as) a n.succ

@[simp]
def List.MinCount.zero : List.MinCount as x 0 := by
  induction as
  apply List.MinCount.nil
  apply List.MinCount.cons
  assumption

@[simp]
def List.MinCount.reduce : List.MinCount as x n -> ∀{m}, m ≤ n -> List.MinCount as x m := by
  intro c m h
  induction as generalizing m n with
  | nil =>
    cases c
    cases Nat.le_zero.mp h
    apply MinCount.nil
  | cons a as ih =>
    cases c
    apply List.MinCount.cons
    apply ih
    assumption
    assumption
    cases m
    apply MinCount.zero
    apply List.MinCount.head
    apply ih
    assumption
    apply Nat.le_of_succ_le_succ
    assumption

attribute [simp] List.MinCount.head List.MinCount.cons

def List.mem_iff_MinCount_one : x ∈ as ↔ List.MinCount as x 1 := by
  induction as with
  | nil => apply Iff.intro <;> (intro; contradiction)
  | cons a as ih =>
    apply Iff.intro <;> intro h
    cases h
    simp
    apply MinCount.cons
    apply ih.mp
    assumption
    cases h
    apply List.Mem.tail
    apply ih.mpr
    assumption
    apply List.Mem.head

def List.mem_iff_exists_perm_cons (x: α) (as: List α) :
  x ∈ as ↔ ∃as', as ≈ x::as' := by
  induction as with
  | nil =>
    simp
    intro _ h
    have := h.length_eq
    contradiction
  | cons a as ih  =>
    apply Iff.intro
    intro mem
    cases mem
    exists as
    apply List.Perm.refl
    rename_i mem
    have ⟨as', perm⟩  := ih.mp mem
    exists a::as'
    apply flip List.Perm.trans
    apply List.Perm.swap
    apply List.Perm.cons
    assumption
    intro ⟨as', perm⟩
    apply perm.mem_iff.mpr
    apply List.Mem.head

def List.find_perm_cons [DecidableEq α] (x: α) (as: List α) (h: x ∈ as) :
  (as': _) ×' as ≈ x::as' := by
  match as with
  | nil => nomatch h
  | cons a as =>
    if g:x = a then
      apply PSigma.mk as
      subst x
      apply List.Perm.cons
      apply List.Perm.refl
    else
      have ⟨as', perm⟩  := find_perm_cons x as (by
        cases h
        contradiction
        assumption)
      apply PSigma.mk (a::as')
      apply List.Perm.trans
      apply List.Perm.cons
      assumption
      apply List.Perm.swap

def List.MinCount.of_perm (h: as ≈ bs) : List.MinCount as x n -> List.MinCount bs x n := by
  intro c
  induction h generalizing n with
  | nil => assumption
  | cons x _ ih =>
    cases c
    apply MinCount.cons
    apply ih
    assumption
    apply MinCount.head
    apply ih
    assumption
  | trans _ _ aih bih =>
    apply bih
    apply aih
    assumption
  | swap =>
    cases c <;> rename_i c <;>
    cases c <;> rename_i c
    apply MinCount.cons; apply MinCount.cons; assumption
    apply MinCount.head; apply MinCount.cons; assumption
    apply MinCount.cons; apply MinCount.head; assumption
    apply MinCount.head; apply MinCount.head; assumption

def List.Perm.min_count_iff (h: List.Perm as bs) : List.MinCount as x n ↔ List.MinCount bs x n := by
  apply Iff.intro
  apply List.MinCount.of_perm; assumption
  apply List.MinCount.of_perm; apply List.Perm.symm; assumption

def List.MinCount.iff_perm : as ≈ bs ↔ ∀x n, List.MinCount as x n ↔ List.MinCount bs x n := by
  apply Iff.intro
  · intro h x n
    apply Iff.intro
    apply MinCount.of_perm
    assumption
    apply MinCount.of_perm
    apply List.Perm.symm
    assumption
  · intro h
    induction as generalizing bs with
    | nil =>
      cases bs with
      | nil => apply List.Perm.refl
      | cons b bs =>
        have := (h b 1).mpr List.MinCount.zero.head
        contradiction
    | cons a as ih =>
      have ⟨bs', perm⟩ := (List.mem_iff_MinCount_one.symm.trans (List.mem_iff_exists_perm_cons a bs)).mp ((h _ _).mp (List.MinCount.zero.head))
      apply List.Perm.trans _ perm.symm
      apply List.Perm.cons
      apply ih
      intro x n
      apply Iff.intro
      intro c
      cases MinCount.of_perm perm ((h _ _).mp (c.cons _ _))
      assumption
      cases MinCount.of_perm perm ((h _ _).mp (c.head _ _))
      apply MinCount.reduce
      assumption
      apply Nat.le_succ
      assumption
      intro c
      cases (h _ _).mpr (MinCount.of_perm perm.symm (c.cons _ _))
      assumption
      cases (h _ _).mpr (MinCount.of_perm perm.symm (c.head _ _))
      apply MinCount.reduce
      assumption
      apply Nat.le_succ
      assumption

def List.MinCount_count [BEq α] [LawfulBEq α] (x: α) (as: List α) : List.MinCount as x (as.count x) := by
  induction as with
  | nil => apply List.MinCount.nil
  | cons a as ih =>
    rw [count_cons]
    split <;> rename_i h
    cases LawfulBEq.eq_of_beq h
    apply List.MinCount.head
    assumption
    apply List.MinCount.cons
    assumption

def List.reduce (default: α) (op: α -> α -> α) : List α -> α
| [] => default
| a::as => op a <| reduce default op as

def List.reduce_spec
  (default: α)
  (op: α -> α -> α)
  [Std.Associative op]
  [Std.Commutative op]:
  ∀as bs, as ≈ bs -> List.reduce default op as = List.reduce default op bs := by
  intro as bs perm
  induction perm with
  | trans _ _ aih bih => rw [aih, bih]
  | nil => rfl
  | cons _ _ ih =>
    unfold reduce
    rw [ih]
  | swap =>
    unfold reduce reduce
    ac_rfl

instance List.decPerm [DecidableEq α] (as bs: List α) : Decidable (as ≈ bs) :=
match as with
| [] => match bs with
  | [] => .isTrue List.Perm.nil
  | _::_ => .isFalse fun h => nomatch (List.Perm.length_eq h)
| a::as =>
  if h: a ∈ bs then
    have ⟨bs', perm'⟩ := bs.find_perm_cons _ h
    match List.decPerm as bs' with
    | .isTrue perm =>
      .isTrue <| by
      apply Perm.trans _ (Perm.symm perm')
      apply Perm.cons
      assumption
    | .isFalse perm => by
      apply Decidable.isFalse
      intro p
      have := (p.trans perm').cons_inv
      contradiction
  else by
    apply Decidable.isFalse
    intro h
    have := h.mem_iff.mp (List.Mem.head _)
    contradiction

def List.minCount_of_nodup (as: List α) : as.Nodup -> as.MinCount x n -> n ≤ 1 := by
  intro nodup mincount
  induction nodup generalizing n with
  | nil =>
    cases mincount
    apply Nat.zero_le
  | cons nomem nodup ih =>
    rename_i a as
    cases mincount <;> rename_i mincount
    apply ih
    assumption
    rename_i n
    replace nomem : x ∉ as := fun h => nomem _ h rfl
    have := mem_iff_MinCount_one.not_iff_not.mp nomem
    cases n
    apply Nat.le_refl
    exfalso
    apply this
    apply MinCount.reduce
    exact mincount
    apply Nat.le_add_left

def List.nodup_map (as: List α) (f: α -> β) :
  Function.Injective f -> as.Nodup -> (as.map f).Nodup := by
  intro finj nodup
  induction nodup with
  | nil => apply List.Pairwise.nil
  | cons nomem nodup ih =>
    rename_i a as
    replace nomem : a ∉ as := fun h => nomem _ h rfl
    apply List.Pairwise.cons
    intro x mem
    replace ⟨x₀, x₀_in_as, fx₀_eq_x⟩ := List.mem_map.mp mem
    subst x
    intro h
    cases finj h
    contradiction
    assumption

def List.nodup_append (as bs: List α) :
  as.Nodup ->
  bs.Nodup ->
  (∀x, x ∈ as -> x ∈ bs -> False) ->
  (as ++ bs).Nodup := by
  intro asnodup bsnodup nocommon
  induction asnodup with
  | nil => exact bsnodup
  | cons nomem nodup ih =>
    rename_i a as
    apply List.Pairwise.cons
    intro x mem
    intro g
    subst x
    rcases List.mem_append.mp mem with memas | membs
    exact nomem _ memas rfl
    apply nocommon
    apply List.Mem.head
    assumption
    apply ih
    intro x memas membs
    apply nocommon
    apply List.Mem.tail
    assumption
    assumption

def List.nodup_filterMap (as: List α) (f: α -> Option β) :
  as.Nodup ->
  (∀{x y}, (f x).isSome -> f x = f y -> x = y) ->
  (as.filterMap f).Nodup := by
  intro nodup finj
  induction nodup with
  | nil => apply List.Pairwise.nil
  | cons nomem nodup ih =>
    rename_i a as
    unfold filterMap
    split <;> (rename_i h; rename Option β => b; clear b)
    assumption
    apply List.Pairwise.cons _ ih
    intro x mem g
    subst x
    rename_i b
    have ⟨a₀, a₀_mem, fa₀_eq_b⟩  := List.mem_filterMap.mp mem
    have := (finj · (h.trans fa₀_eq_b.symm))
    rw [h] at this
    cases this rfl
    apply nomem
    assumption
    rfl

def List.nodup_flatMap (as: List α) (f: α -> List β) :
  as.Nodup ->
  (∀x, (f x).Nodup) ->
  (∀{x y}, x ∈ as -> y ∈ as -> ∀z, z ∈ f x -> z ∈ f y -> x = y) ->
  (as.flatMap f).Nodup := by
  intro asnodup nodups nocommon
  induction as with
  | nil => apply List.Pairwise.nil
  | cons a as ih =>
    apply List.nodup_append
    apply nodups
    apply ih
    · exact asnodup.tail
    · intro x y xas yas z zx zy
      apply nocommon
      apply List.Mem.tail; assumption
      apply List.Mem.tail; assumption
      assumption
      assumption
    · intro x fx mem
      have ⟨b, b_in_as, x_in_fb⟩  := List.mem_flatMap.mp mem
      have := (nodup_cons.mp asnodup).left
      cases nocommon (List.Mem.head _) (List.Mem.tail _ b_in_as) x fx x_in_fb
      contradiction

def List.sum_const (as: List Nat) (h: ∀x y, x ∈ as -> y ∈ as -> x = y) :
  as.sum = match as.head? with
  | .some x => x * as.length
  | .none => 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    dsimp
    rw [Nat.mul_succ, Nat.add_comm]
    congr
    have := ih (by
      intro x y xm ym
      apply h
      apply List.Mem.tail; assumption
      apply List.Mem.tail; assumption)
    cases as with
    | nil => rfl
    | cons a' as =>
      have : a = a' := h a a' (List.Mem.head _) (List.Mem.tail _ <| List.Mem.head _)
      subst a'
      exact this

def List.sum_const' (as: List Nat) (a: Nat) (h: ∀x ∈ as, x = a) :
  as.sum = a * as.length := by
  rw [sum_const]
  cases as
  rfl
  dsimp
  rename_i b _
  rw [h b]
  apply List.Mem.head
  intro x y _ _
  rw [h x, h y]
  assumption
  assumption

def List.length_flatMap (as: List α) (f: α -> List β) : (as.flatMap f).length = List.sum (as.map fun x => (f x).length) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]
