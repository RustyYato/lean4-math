import Math.Function.Basic

def List.Pairwise.head :
  List.Pairwise P (a::as) ->
  ∀x ∈ as, P a x
| .cons pa _ => pa

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

def List.nodup_iff_getElem_inj {as: List α}:
  as.Nodup ↔ Function.Injective (fun i: Fin as.length => as[i]) := by
  apply Iff.intro
  intro h i j eq
  exact Fin.val_inj.mp (List.nodup_getElem_inj h eq)
  intro h
  induction as with
  | nil => apply List.Pairwise.nil
  | cons a as ih =>
    apply List.Pairwise.cons
    rintro _ mem rfl
    have ⟨i, iLt, g⟩ := List.getElem_of_mem mem
    subst a
    have := Fin.mk.inj (@h ⟨0, Nat.zero_lt_succ _⟩ ⟨i+1, Nat.succ_lt_succ iLt⟩ rfl)
    contradiction
    apply ih
    intro x y eq
    exact Fin.succ_inj.mp (@h x.succ y.succ eq)

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

def List.nodup_ofFn (f: Fin n -> α) : Function.Injective f ↔ (List.ofFn f).Nodup := by
  rw [List.nodup_iff_getElem_inj]
  apply Iff.intro
  intro finj
  intro x y eq
  simp at eq
  apply Fin.val_inj.mp
  apply Fin.mk.inj (finj eq)
  intro inj x y eq
  have := @inj ⟨x.val, ?_⟩ ⟨y.val, ?_⟩
  simp at this
  replace := this eq
  apply Fin.val_inj.mp
  assumption
  rw [List.length_ofFn]
  apply Fin.isLt
  rw [List.length_ofFn]
  apply Fin.isLt

def List.nodup_eraseIdx (as: List α) (h: as.Nodup) : (as.eraseIdx i).Nodup := by
  induction as generalizing i with
  | nil => assumption
  | cons a as ih =>
    cases i with
    | zero => apply h.tail
    | succ i =>
      apply List.Pairwise.cons
      intro x hx
      exact h.head _ (List.mem_of_mem_eraseIdx hx)
      apply ih
      exact h.tail

def List.getElem_idxOf [BEq α] [LawfulBEq α] (as: List α) (a: α) (ha: a ∈ as) : as[as.idxOf a]'(List.idxOf_lt_length ha) = a := by
  apply Option.some.inj
  rw [←List.getElem?_eq_getElem]
  induction as with
  | nil => contradiction
  | cons a₀ as ih =>
    simp [idxOf_cons, cond]
    split <;> rename_i h
    cases LawfulBEq.eq_of_beq h
    rfl
    rw [List.getElem?_cons_succ]
    apply ih
    cases ha
    rw [LawfulBEq.rfl] at h
    contradiction
    assumption

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
