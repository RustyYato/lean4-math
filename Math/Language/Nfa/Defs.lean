import Math.Language.Defs

structure Nfa (σ α: Type*) where
  step: σ -> α -> Set α
  start: Set α
  accept: Set α

namespace Nfa

def stepSet (nfa: Nfa σ α) (a: σ) (states: Set α) : Set α :=
  states.bind (nfa.step a)

def runWith (nfa: Nfa σ α) (states: Set α) : List σ -> Set α
| [] => states
| a::as => nfa.runWith (nfa.stepSet a states) as

def run (nfa: Nfa σ α) (word: List σ) : Set α :=
  nfa.runWith nfa.start word

def Matches (nfa: Nfa σ α) (word: List σ) : Prop :=
  (nfa.run word ∩ nfa.accept).Nonempty

def Language (nfa: Nfa σ α) : Langauge σ where
  Mem := nfa.Matches

-- if running the nfa from this state set never hits an accepting node
-- then this is a dead state
def IsDeadStateSet (nfa: Nfa σ α) (states: Set α) :=
  ∀word: List σ, nfa.runWith states word ∩ nfa.accept = ∅

-- a state set is reachable from another if there is a word
-- which transitions the nfa from `b` to `a`
def IsReachableFrom (nfa: Nfa σ α) (a b: Set α) :=
  ∃word, nfa.runWith b word = a

def ReachableStates (nfa: Nfa σ α) (s: Set α) :=
  Set.mk fun a => nfa.IsReachableFrom a s

def ReachableStates.ofIdempot (nfa: Nfa σ α) (s: Set α) :
  (∀x, nfa.stepSet x s = s) -> nfa.ReachableStates s = {s} := by
  intro h
  ext t
  apply flip Iff.intro
  · rintro rfl
    exists []
  · rintro ⟨word, rfl⟩
    show _ = s
    induction word with
    | nil => rfl
    | cons w ws ih =>
      unfold runWith
      rw [h, ih]

def runWith_append (nfa: Nfa σ α) (a b: Set α) (w₀ w₁: List σ) :
  nfa.runWith a w₀ = b ->
  nfa.runWith a (w₀ ++ w₁) = nfa.runWith b w₁ := by
  intro h
  induction w₀ generalizing a with
  | nil =>
    replace h : a = b := h
    subst a
    rfl
  | cons w ws ih =>
    rw [List.cons_append, runWith]
    apply ih
    assumption

def IsDeadStateSet.ofIsReachableFrom (nfa: Nfa σ α) (a b: Set α)
  (hb: nfa.IsDeadStateSet b) (h: nfa.IsReachableFrom a b) : nfa.IsDeadStateSet a := by
  obtain ⟨word, hx⟩ := h
  intro w
  have : nfa.runWith b (word ++ w) = nfa.runWith a w := by
    apply runWith_append
    assumption
  rw [←nfa.runWith_append b a word w]
  clear this
  apply hb
  assumption

def IsDeadStateSet.ofStep (nfa: Nfa σ α) (a: Set α)
  (ha: a ∩ nfa.accept = ∅)
  (h: ∀x, nfa.IsDeadStateSet (nfa.stepSet x a)) : nfa.IsDeadStateSet a := by
  intro word
  induction word
  assumption
  apply h

def IsDeadStateSet.ofIdempot (nfa: Nfa σ α) (a: Set α)
  (ha: a ∩ nfa.accept = ∅)
  (h: ∀x, (nfa.stepSet x a) = a) : nfa.IsDeadStateSet a := by
  intro word
  induction word
  assumption
  unfold runWith
  rw [h]
  assumption

def empty (σ α: Type*) : Nfa σ α where
  step _ _ := ∅
  start := ∅
  accept := ∅

def empty_reachable : (empty σ α).ReachableStates (empty σ α).start = {∅} := by
  apply ReachableStates.ofIdempot
  intro x
  show stepSet _ _ ∅ = ∅
  unfold stepSet
  simp

def empty_run : (empty σ α).run xs = ∅ := by
  have : (empty σ α).run xs ∈ (empty σ α).ReachableStates (empty σ α).start := by exists xs
  rw [empty_reachable] at this
  assumption

def empty_language : (empty σ α).Language = ∅ := by
  apply Set.ext_empty
  intro l h
  replace h : (empty σ α).Matches l := h
  unfold Matches at h
  rw [empty_run] at h
  simp at h
  contradiction

def single [DecidableEq σ] (x: σ) : Nfa σ Bool where
  step a s :=
    if a = x ∧ !s then
      {true}
    else
      ∅
  start := {false}
  accept := {true}

@[simp]
def single_start [DecidableEq σ] (x: σ):
  (single x).start = {false} := rfl

@[simp]
def single_step [DecidableEq σ] (x: σ):
  (single x).step a s =
    if a = x ∧ !s then
      {true}
    else
      ∅ := rfl

def single_dead_state [DecidableEq σ] (x: σ) : (single x).IsDeadStateSet ∅ := by
  apply IsDeadStateSet.ofIdempot
  simp
  intro y
  simp [stepSet]

def single_language [DecidableEq σ] (x: σ) : (single x).Language = {[x]} := by
  ext l
  simp
  apply flip Iff.intro
  · rintro rfl
    show Matches _ _
    unfold Matches
    exists true
    apply And.intro _ rfl
    unfold run runWith runWith
      stepSet
    rw [Set.mem_bind]
    exists false
    simp
  · intro h
    match l with
    | [] =>
      replace h : (single x).Matches [] := h
      unfold Matches run runWith at h
      obtain ⟨x, rfl, h₁⟩ := h
      contradiction
    | [y] =>
      congr
      replace h : (single x).Matches [y] := h
      unfold Matches run at h
      simp [runWith, stepSet, single] at h
      split at h
      assumption
      simp at h
      contradiction
    | x₀::x₁::xs =>
      replace h : (single x).Matches (x₀::x₁::xs) := h
      unfold Matches run at h
      simp [runWith, stepSet] at h
      split at h
      simp [runWith] at h
      rw [single_dead_state] at h
      contradiction
      simp at h
      rw [single_dead_state] at h
      contradiction

@[simp]
def alt_step' (a: Nfa σ α) (b: Nfa σ β) (x: σ) : α ⊕ β -> Set (α ⊕ β)
| .inl s => (a.step x s).image .inl
| .inr s => (b.step x s).image .inr

def alt (a: Nfa σ α) (b: Nfa σ β) : Nfa σ (α ⊕ β) where
  step := alt_step' a b
  start := a.start.sum b.start
  accept := a.accept.sum b.accept

@[simp] def alt_step (a: Nfa σ α) (b: Nfa σ β) : (alt a b).step = alt_step' a b := rfl
@[simp] def alt_start (a: Nfa σ α) (b: Nfa σ β) : (alt a b).start = a.start.sum b.start := rfl
@[simp] def alt_accept (a: Nfa σ α) (b: Nfa σ β) : (alt a b).accept = a.accept.sum b.accept := rfl

def alt_stepSet (a: Nfa σ α) (b: Nfa σ β) (sa: Set α) (sb: Set β) (w: σ) : (alt a b).stepSet w (sa.sum sb) = (a.stepSet w sa).sum (b.stepSet w sb) := by
  unfold stepSet
  rw [Set.sum_bind, alt_step]
  unfold alt_step'
  simp [alt_step']
  rw [←Function.comp_def, ←Function.comp_def, Set.bind_image, Set.bind_image]
  rw [←Set.sum_eq_image_union]

def alt_runWith (a: Nfa σ α) (b: Nfa σ β) (sa: Set α) (sb: Set β) : (alt a b).runWith (sa.sum sb) word = (a.runWith sa word).sum (b.runWith sb word) := by
  induction word generalizing sa sb with
  | nil => rfl
  | cons w word ih => simp [runWith, alt_stepSet, ih]

def alt_run (a: Nfa σ α) (b: Nfa σ β) : (alt a b).run word = (a.run word).sum (b.run word) := by
  unfold run
  simp [alt_runWith]

def alt_language (a: Nfa σ α) (b: Nfa σ β) : (alt a b).Language = a.Language ∪ b.Language := by
  ext word
  apply Iff.intro
  · intro h
    obtain ⟨x, hx, h⟩ := h
    simp at h
    rw [Set.sum_eq_image_union] at h
    rcases h with ⟨x, h₁, rfl⟩ | ⟨x, h₁, rfl⟩
    · left
      exists x
      apply And.intro _ h₁
      rw [alt_run] at hx
      simpa using hx
    · right
      exists x
      apply And.intro _ h₁
      rw [alt_run] at hx
      simpa using hx
  · intro h
    rcases h with ⟨s, hs, h₀⟩ | ⟨s, hs, h₀⟩
    · exists .inl s
      apply And.intro
      · clear h₀
        simpa [alt_run]
      · simpa [alt_accept]
    · exists .inr s
      apply And.intro
      · clear h₀
        simpa [alt_run]
      · simpa [alt_accept]

end Nfa
