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
