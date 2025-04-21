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
