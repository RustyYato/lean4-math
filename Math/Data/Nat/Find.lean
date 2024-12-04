import Math.Data.Nat.Order

namespace nat

structure FindResult (P: nat -> Bool) where
  val: nat
  prop: P val
  not_prop: ∀x < val, ¬P x

abbrev findType (P: nat -> Bool) (_h: ∃x, P x) := { x : nat // ∀y < x, ¬P y }

variable (P: nat -> Bool) {h: ∃x, P x}

def find_rel (a b: findType P h): Prop := a.val > b.val

def findType.mk (x: nat) (g: ∀y < x, ¬P y) : findType P h := ⟨x, g⟩

def findType.le (a: findType P h) (x: nat) (hx: P x) : a.val ≤ x := by
  apply Decidable.byContradiction
  intro h
  have := a.property _ (lt_of_not_le h)
  contradiction

def findType.acc (x: nat) (px: P x) (a: findType P h) : Acc (find_rel P) a := by
  apply Acc.intro
  intro b r
  replace r : a.val < b.val := r
  apply findType.acc
  assumption
termination_by x - a.val
decreasing_by
  have := a.le P _ px
  have := b.le P _ px
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, ha⟩ := b
  dsimp at r
  dsimp
  apply lt_add_right_iff_lt.mpr
  show (x - b) + (a + b) < _
  rw [←add_assoc (x - a), sub_add_cancel]
  rw [add_comm a, ←add_assoc, sub_add_cancel]
  apply lt_add_left_iff_lt.mp
  assumption
  assumption
  assumption

instance (P: nat -> Bool) (h: ∃n, P n) : WellFoundedRelation (findType P h) where
  rel a b := b.val < a.val
  wf := by
    obtain ⟨x, px⟩ := h
    apply WellFounded.intro
    apply findType.acc
    assumption

def findAux (P: nat -> Bool) (h: ∃n, P n) (x: findType P h)
  : FindResult P :=
  match g:P x with
  | true => ⟨x, g, x.property⟩
  | false => findAux P h <| findType.mk P x.val.succ <| by
    intro y lt
    cases lt_or_eq_of_le (le_of_lt_succ lt)
    apply x.property
    assumption
    subst y
    apply Bool.eq_false_iff.mp
    assumption
termination_by x
decreasing_by
  unfold findType.mk
  simp
  apply nat.lt_succ_self

def find {P: nat -> Bool} (h: ∃n, P n) : nat := (findAux P h ⟨0, nofun⟩).val
def find_spec {P: nat -> Bool} (h: ∃n, P n) : P (find h) := (findAux P h ⟨0, nofun⟩).prop
def lt_find_spec {P: nat -> Bool} (h: ∃n, P n) : ∀x < find h, ¬P x := (findAux P h ⟨0, nofun⟩).not_prop

def findP {P: nat -> Prop} [DecidablePred P] (h: ∃n, P n) : nat := find (P := fun x => decide (P x)) <| by
  obtain ⟨x, Px⟩ := h
  exists x
  dsimp
  rw [decide_eq_true Px]
def findP_spec {P: nat -> Prop} [DecidablePred P] (h: ∃n, P n) : P (findP h) := by
  unfold findP
  apply decide_eq_true_iff.mp
  apply find_spec (P := fun x => decide (P x))
def lt_findP_spec {P: nat -> Prop} [DecidablePred P] (h: ∃n, P n) : ∀x < findP h, ¬P x:= by
  unfold findP
  intro x r px
  apply lt_find_spec (P := fun x => decide (P x))
  assumption
  apply decide_eq_true_iff.mpr
  assumption

instance Nat.decExistsLtTR
  (P: Nat -> Prop)
  [d: DecidablePred P]
  (n m: Nat)
  (m_le_n: m ≤ n)
  (h: ∀x ≥ m, x < n -> ¬P x) : Decidable (∃x < n, P x) :=
  match m with
  | 0 => .isFalse <| by
    intro ⟨x, x_lt_n, Px⟩
    have := h x (Nat.zero_le x) x_lt_n
    contradiction
  | m + 1 =>
    match d m with
    | .isTrue h => .isTrue ⟨m, m_le_n, h⟩
    | .isFalse g₀ =>
      decExistsLtTR P n m (Nat.le_trans (Nat.le_succ _) m_le_n) (by
        intro x m_le_x x_lt_n
        cases lt_or_eq_of_le m_le_x
        apply h
        apply Nat.succ_le_of_lt
        assumption
        assumption
        subst x
        assumption)

instance decExistsLtStdNat (P: Nat -> Prop) [d: DecidablePred P] (n: Nat) : Decidable (∃x < n, P x) :=
  Nat.decExistsLtTR P n n (Nat.le_refl _) (fun _ h g => (Nat.not_le_of_lt g h).elim)

instance decExistsLtNat (P: nat -> Prop) [DecidablePred P] (n: nat) : Decidable (∃x < n, P x) :=
  decidable_of_iff (∃x < n.toNat, P (ofNat x)) (by
    apply Iff.intro
    intro ⟨x, x_lt, prf⟩
    exists ofNat x
    apply And.intro
    apply (LT_iff_toNat_lt _ _).mpr
    rw [toNat.LeftInverse]
    assumption
    assumption
    intro ⟨x, x_lt, prf⟩
    exists toNat x
    apply And.intro
    apply (LT_iff_toNat_lt _ _).mp
    assumption
    assumption)

instance {P: nat -> Prop} [DecidablePred P] (n: nat) : Decidable (∀x < n, P x) :=
  decidable_of_iff (¬∃x < n, ¬P x) (by simp)

end nat
