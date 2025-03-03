import Math.Data.Fintype.Basic

namespace Fintype

section ind

variable {α: Type*} (motive: α -> Prop) (set: List α)

private
def indInputType (set: List α): Prop :=
  match set with
  | [] => True
  | a::as => motive a ∧ indInputType as

def indCasesType (set: List α): Prop :=
  match set with
  | [] => ∀x: α, motive x
  | a::as => motive a -> indCasesType as

private
def indInputType.toIndCases
  (h: indInputType motive set -> ∀x, motive x):
  Fintype.indCasesType motive set := by
  induction set with
  | nil =>
    apply h
    exact True.intro
  | cons a as ih =>
    intro g
    apply ih
    intro ih' x
    apply h
    apply And.intro
    assumption
    assumption

private def indInput:
  indInputType motive set -> ∀x ∈ set, motive x := by
  induction set with
  | nil =>
    intro _ _ mem
    contradiction
  | cons a as ih =>
    intro h x mem
    cases mem
    apply h.left
    apply ih
    exact h.right
    assumption

def indCases (α: Type*) [f: Fintype α] {motive: α -> Prop} :
  Fintype.indCasesType motive f.all := by
  apply Fintype.indInputType.toIndCases
  intro inp x
  apply Fintype.indInput
  assumption
  apply f.complete

end ind

section rec

variable {α: Type u} (motive: α -> Type v) (set: List α)

private
def recInputType (set: List α): Type (max u v) :=
  match set with
  | [] => PUnit
  | a::as => motive a × recInputType as

def recCasesType (set: List α): Type _ :=
  match set with
  | [] => ∀x: α, motive x
  | a::as => motive a -> recCasesType as

private
def recInputType.toRecCases
  (set: List α)
  (h: recInputType motive set -> ∀x, motive x):
  Fintype.recCasesType motive set :=
  match set with
  | [] => fun _ => h PUnit.unit _
  | _::as => fun g => recInputType.toRecCases as <| fun ih' => h ⟨g, ih'⟩

private def recInput [DecidableEq α] {set}:
  recInputType motive set -> ∀x ∈ set, motive x :=
  match set with
  | [] => nofun
  | a::as =>
    fun h x mem =>
      match decEq x a with
      | .isTrue (.refl _) => h.1
      | isFalse ne => recInput h.2 _ <| by
        cases mem
        contradiction
        assumption

def recCases (α: Type u) [DecidableEq α] [f: Fintype α] (motive: α -> Type v) :
  Fintype.recCasesType motive f.all := by
  apply Fintype.recInputType.toRecCases
  intro inp x
  apply Fintype.recInput _ inp
  apply f.complete

end rec

end Fintype
