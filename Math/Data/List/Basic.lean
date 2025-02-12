import Math.Logic.Basic
import Math.Function.Basic

inductive List.MinCountBy (P: α -> Prop) : List α -> Nat -> Prop where
| nil : MinCountBy P [] 0
| cons a as n : MinCountBy P as n -> MinCountBy P (a::as) n
| head a as n : P a -> MinCountBy P as n -> MinCountBy P (a::as) n.succ

abbrev List.MinCount (as: List α) (x: α) (n: Nat) := as.MinCountBy (· = x) n

def List.MinCount.head : MinCount as a n -> MinCount (a::as) a n.succ := MinCountBy.head _ _ _ rfl

@[simp]
def List.MinCountBy.zero {as: List α} : as.MinCountBy P 0 := by
  induction as
  apply List.MinCountBy.nil
  apply List.MinCountBy.cons
  assumption

def List.MinCount.zero {as: List α} : as.MinCount x 0 := MinCountBy.zero

@[simp]
def List.MinCountBy.reduce : List.MinCountBy P as n -> ∀{m}, m ≤ n -> List.MinCountBy P as m := by
  intro c m h
  induction as generalizing m n with
  | nil =>
    cases c
    cases Nat.le_zero.mp h
    apply MinCountBy.nil
  | cons a as ih =>
    cases c
    apply List.MinCountBy.cons
    apply ih
    assumption
    assumption
    cases m
    apply MinCountBy.zero
    apply List.MinCountBy.head
    assumption
    apply ih
    assumption
    apply Nat.le_of_succ_le_succ
    assumption

attribute [simp] List.MinCountBy.head List.MinCountBy.cons

def List.mem_iff_MinCount_one : x ∈ as ↔ List.MinCount as x 1 := by
  induction as with
  | nil => apply Iff.intro <;> (intro; contradiction)
  | cons a as ih =>
    apply Iff.intro <;> intro h
    cases h
    simp
    apply MinCountBy.cons
    apply ih.mp
    assumption
    cases h
    apply List.Mem.tail
    apply ih.mpr
    assumption
    subst x
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

def List.MinCountBy.of_perm (h: as ≈ bs) : List.MinCountBy P as n -> List.MinCountBy P bs n := by
  intro c
  induction h generalizing n with
  | nil => assumption
  | cons x _ ih =>
    cases c
    apply MinCountBy.cons
    apply ih
    assumption
    apply MinCountBy.head
    assumption
    apply ih
    assumption
  | trans _ _ aih bih =>
    apply bih
    apply aih
    assumption
  | swap =>
    cases c <;> rename_i c <;>
    cases c <;> rename_i c
    apply MinCountBy.cons; apply MinCountBy.cons; assumption
    apply MinCountBy.head; assumption; apply MinCountBy.cons; assumption
    apply MinCountBy.cons; apply MinCountBy.head; assumption; assumption
    apply MinCountBy.head; assumption; apply MinCountBy.head; assumption; assumption

def List.MinCount.of_perm (h: as ≈ bs) : List.MinCount as x n -> List.MinCount bs x n := MinCountBy.of_perm h

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
        have := (h b 1).mpr <| List.MinCount.zero.head
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
      subst x
      cases MinCount.of_perm perm ((h _ _).mp c.head)
      apply MinCountBy.reduce
      assumption
      apply Nat.le_succ
      assumption
      intro c
      cases (h _ _).mpr (MinCount.of_perm perm.symm (c.cons _ _))
      assumption
      subst x
      cases (h _ _).mpr (MinCount.of_perm perm.symm c.head)
      apply MinCountBy.reduce
      assumption
      apply Nat.le_succ
      assumption

def List.MinCount_count [BEq α] [LawfulBEq α] (x: α) (as: List α) : List.MinCount as x (as.count x) := by
  induction as with
  | nil => apply List.MinCountBy.nil
  | cons a as ih =>
    rw [count_cons]
    split <;> rename_i h
    cases LawfulBEq.eq_of_beq h
    apply List.MinCount.head
    assumption
    apply List.MinCountBy.cons
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
    rename_i n h'
    replace nomem : x ∉ as := fun h => nomem _ h h'
    have := mem_iff_MinCount_one.not_iff_not.mp nomem
    cases n
    apply Nat.le_refl
    exfalso
    apply this
    subst x
    rename_i n
    apply MinCountBy.reduce
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

def List.nodup_filter (as: List α) (f: α -> Bool) :
  as.Nodup ->
  (as.filter f).Nodup := by
  intro ha
  induction ha with
  | nil => apply List.Pairwise.nil
  | cons nomem nodup ih =>
    unfold filter
    split
    apply List.Pairwise.cons
    · intro x mem
      have ⟨_, _⟩ := List.mem_filter.mp mem
      apply nomem
      assumption
    assumption
    assumption

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

def List.product [Mul α] [OfNat α 1] : List α -> α
| [] => 1
| a::as => a * product as

def List.product_const (as: List Nat) (h: ∀x y, x ∈ as -> y ∈ as -> x = y) :
  as.product = match as.head? with
  | .some x => x ^ as.length
  | .none => 1 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    dsimp
    rw [Nat.pow_succ, Nat.mul_comm]
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
      dsimp at this
      rw [product, this]
      rfl

def List.product_const' (as: List Nat) (a: Nat) (h: ∀x ∈ as, x = a) :
  as.product = a ^ as.length := by
  rw [product_const]
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

def List.Nodup.singleton (x: α) : List.Nodup [x] := List.Pairwise.cons nofun List.Pairwise.nil

def List.MinCountBy.pop_head : (a::as).MinCountBy P (n + 1) -> as.MinCountBy P n := by
  intro h
  cases h; rename_i h
  apply h.reduce
  apply Nat.le_succ
  assumption

def List.MinCount.pop_head : (a::as).MinCount a (n + 1) -> as.MinCount a n := by
  intro h
  cases h; rename_i h
  apply h.reduce
  apply Nat.le_succ
  assumption

def List.MinCountBy.subPredicate {P Q: α -> Prop} {as: List α} (h: ∀x ∈ as, P x -> Q x) : as.MinCountBy P n -> as.MinCountBy Q n := by
  intro c
  induction c with
  | nil => apply MinCountBy.nil
  | cons _ _ _ _ ih =>
    apply MinCountBy.cons
    apply ih
    intro x mem
    apply h
    apply List.Mem.tail
    assumption
  | head _ _ _ _ _ ih  =>
    apply List.MinCountBy.head
    apply h
    apply List.Mem.head
    assumption
    apply ih
    intro x mem
    apply h
    apply List.Mem.tail
    assumption

def List.MinCountBy.map {P: α -> Prop} {Q: β -> Prop} {f: α -> β} {as: List α} (h: ∀x ∈ as, P x -> Q (f x)) : as.MinCountBy P n -> (as.map f).MinCountBy Q n := by
  intro c
  induction c with
  | nil => apply MinCountBy.nil
  | cons _ _ _ _ ih =>
    apply MinCountBy.cons
    apply ih
    intro x mem
    apply h
    apply List.Mem.tail
    assumption
  | head _ _ _ _ _ ih  =>
    apply List.MinCountBy.head
    apply h
    apply List.Mem.head
    assumption
    apply ih
    intro x mem
    apply h
    apply List.Mem.tail
    assumption

def List.Pairwise.head :
  List.Pairwise P (a::as) ->
  ∀x ∈ as, P a x
| .cons pa _ => pa

abbrev List.Elem (as: List α) := { x // x ∈ as }
instance : CoeSort (List α) (Sort _) := ⟨List.Elem⟩

def List.nodup_pmap (as: List α) {P: α -> Prop} {f: ∀x, P x -> β} {ofmem} (inj: ∀x y h₀ h₁, HEq (f x h₀) (f y h₁) -> x = y) : as.Nodup ↔ (as.pmap f ofmem).Nodup := by
  induction as with
  | nil => apply Iff.intro <;> (intro; apply List.Pairwise.nil)
  | cons a as ih =>
    apply Iff.intro
    intro h
    cases h; rename_i hs h
    apply List.Pairwise.cons
    intro x g eq
    subst x
    have ⟨a', mem, eq⟩ := List.mem_pmap.mp g
    cases inj _ _ _ _ (heq_of_eq eq)
    exact h _ mem rfl
    show (List.pmap _ _ _).Nodup
    apply ih.mp
    exact hs
    intro h
    cases h; rename_i hs h
    apply Pairwise.cons
    intro x mem g
    have px := ofmem x (List.Mem.tail _ mem)
    exact h (f x px) (List.mem_pmap_of_mem mem) (g ▸ rfl)
    apply ih.mpr
    assumption

def List.nodup_attach (as: List α) : as.Nodup ↔ as.attach.Nodup := by
  apply List.nodup_pmap
  intro x y _ _ eq
  cases eq
  rfl

def List.dedup [DecidableEq α] : List α -> List α
| [] => []
| a::as =>
  have as' := as.dedup
  if a ∈ as' then as' else a::as'

def List.mem_dedup [DecidableEq α] {as: List α} :
  ∀{x}, x ∈ as ↔ x ∈ List.dedup as := by
  intro x
  induction as with
  | nil => rfl
  | cons a as ih =>
    unfold dedup; dsimp; split <;> rename_i h
    apply Iff.intro
    intro mem
    cases mem
    assumption
    apply ih.mp
    assumption
    intro
    apply List.Mem.tail
    apply ih.mpr
    assumption
    apply Iff.intro
    intro mem
    cases mem
    apply List.Mem.head
    apply List.Mem.tail
    apply ih.mp
    assumption
    intro g
    cases g
    apply List.Mem.head
    apply List.Mem.tail
    apply ih.mpr
    assumption

def List.nodup_dedup [DecidableEq α] (as: List α) : as.dedup.Nodup := by
  induction as with
  | nil => apply List.Pairwise.nil
  | cons a as =>
    unfold dedup; dsimp; split <;> rename_i h
    assumption
    apply List.Pairwise.cons
    intro x m h; subst x; contradiction
    assumption

def List.mincount_le_one_iff_nodup {as: List α} :
  as.Nodup ↔ ∀{x: α} {n: Nat}, as.MinCount x n -> n ≤ 1 := by
  induction as with
  | nil =>
    apply Iff.intro
    intro h x n c
    replace c : List.MinCount [] x n := c
    cases c
    apply Nat.zero_le
    intro
    apply List.Pairwise.nil
  | cons a as ih =>
    apply Iff.intro
    intro h
    cases h
    rename_i has ha
    intro x n c
    cases c
    apply ih.mp
    assumption
    assumption
    · apply Nat.succ_le_succ
      subst x
      have : a ∉ as := (ha a · rfl)
      apply Decidable.byContradiction
      intro h
      replace h := Nat.lt_of_not_le h
      rename_i n _
      match n with
      | n + 1 =>
      rename_i c
      have : List.MinCount _ _ _ := c.reduce (m := 1) (Nat.succ_le_succ (Nat.zero_le _))
      rw [←List.mem_iff_MinCount_one] at this
      contradiction
    intro h
    apply List.Pairwise.cons
    intro x hx
    intro h; subst x
    rw [List.mem_iff_MinCount_one] at hx
    have := h hx.head
    contradiction
    apply ih.mpr
    intro x n c
    apply h
    apply c.cons

def List.ext_nodup (as: List α) (bs: List α) (ha: as.Nodup) (hb: bs.Nodup) :
  (h: ∀{x}, x ∈ as ↔ x ∈ bs) -> as ≈ bs := by
  intro h
  apply List.MinCount.iff_perm.mpr
  intro x n
  match n with
  | 0 =>
    apply Iff.intro <;> intro
    apply List.MinCount.zero
    apply List.MinCount.zero
  | 1 =>
    rw [←List.mem_iff_MinCount_one, ←List.mem_iff_MinCount_one]
    apply h
  | n + 2 =>
    rw [List.mincount_le_one_iff_nodup] at ha hb
    apply Iff.intro
    intro c
    have := ha c
    contradiction
    intro c
    have := hb c
    contradiction

def List.nodup_getElem_inj {as: List α} (h: as.Nodup)
  {i j: Nat} {hi: i < as.length} {hj: j < as.length} :
  as[i] = as[j] -> i = j := by
  intro g
  induction i generalizing j as with
  | zero =>
    cases j with
    | zero => rfl
    | succ j =>
    cases as with
    | nil => contradiction
    | cons a as =>
      dsimp at g
      rw [g] at h
      have := Nat.lt_of_succ_lt_succ hj
      have := h.head as[j] (List.getElem_mem _)
      contradiction
  | succ i ih =>
    cases j with
    | zero =>
      cases as with
      | nil => contradiction
      | cons a as =>
        dsimp at g
        rw [←g] at h
        have := Nat.lt_of_succ_lt_succ hi
        have := h.head as[i] (List.getElem_mem _)
        contradiction
    | succ j =>
      cases as with
      | nil => contradiction
      | cons a as =>
      rw [ih]
      exact h.tail
      apply Nat.lt_of_succ_lt_succ
      assumption
      apply Nat.lt_of_succ_lt_succ
      assumption
      assumption
