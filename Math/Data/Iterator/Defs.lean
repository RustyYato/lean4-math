import Math.Type.Notation
import Math.Relation.Defs

class Iterator (σ: Type*) (α: outParam Type*) where
  next : σ -> Option (σ × α)

namespace Iterator

protected class inductive IsFinite [Iterator σ α] : σ -> Prop where
| empty (σ₀: σ) (h: next σ₀ = .none) : Iterator.IsFinite σ₀
| next (σ₀ σ₁: σ) (a: α) (h: next σ₀ = .some (σ₁, a)) : Iterator.IsFinite σ₁ -> Iterator.IsFinite σ₀

protected inductive Rel₁ {σ α: Type*} [it: Iterator σ α]: σ -> σ -> Prop where
| intro (σ₀ σ₁: σ) (a: α) : it.next σ₀ = (σ₁, a) -> Iterator.Rel₁ σ₁ σ₀

def IsFinite.toAcc [Iterator σ α] (σ₀: σ) [h: Iterator.IsFinite σ₀] : Acc Iterator.Rel₁ σ₀ := by
  induction h with
  | empty _ h =>
    apply Acc.intro
    rintro _ ⟨_, _, _, g⟩
    rw [h] at g
    contradiction
  | next σ₀ σ₁ a h h₁ ih =>
    apply Acc.intro
    rintro _ ⟨_, _, _, g⟩
    rw [h] at g
    cases g
    assumption

def fold_step [Iterator σ α] (f: α -> γ -> γ) (σ₀: σ) (ih: (y : σ) → Iterator.Rel₁ y σ₀ → (fun _ => γ → γ) y) : γ -> γ :=
  match h:next σ₀ with
  | .some (σ₁, a) => (ih σ₁ (Iterator.Rel₁.intro _ _ _ h) <| f a ·)
  | .none => id

def fold [Iterator σ α] (f: α -> γ -> γ) (σ₀: σ) [ifin: Iterator.IsFinite σ₀] : γ -> γ :=
  WellFounded.fixF (C := fun _ => γ -> γ) (fold_step f) _ ifin.toAcc

def len [Iterator σ α] (σ₀: σ) [Iterator.IsFinite σ₀] : ℕ :=
  fold (fun _ => Nat.succ) σ₀ 0

def fold_empty [it: Iterator σ α] (f: α -> γ -> γ) (σ₀: σ) (h: next σ₀ = .none) [ifin: Iterator.IsFinite σ₀] : fold f σ₀ = id := by
  ext acc
  unfold fold
  rw [WellFounded.fixF_eq]
  show fold_step _ _ (fun _ _ => (@fold _ _ _ _ f _ ?_)) _ = _
  · unfold fold_step fold_step.match_1; dsimp
    conv => { lhs; arg 3; rw [h] }
    rfl
  rename_i x hx
  cases hx; rename_i g
  rw [h] at g; contradiction

def fold_next [it: Iterator σ α] (f: α -> γ -> γ) (σ₀ σ₁: σ) (a: α) (h: next σ₀ = (σ₁, a)) [ifin: Iterator.IsFinite σ₀] (acc: γ) : fold f σ₀ acc = (@fold _ _ _ _ f σ₁ (by
  cases ifin; rename_i g
  rw [h] at g
  contradiction; rename_i g
  rw [h] at g
  cases g
  assumption) (f a acc)) := by
  rw [fold, WellFounded.fixF_eq]
  show fold_step _ _ (fun _ _ => (@fold _ _ _ _ f _ ?_)) _ = _
  unfold fold_step fold_step.match_1; dsimp
  conv => { lhs; arg 3; rw [h] }
  rename_i x hx
  cases hx
  cases ifin
  rename_i g; rw [g] at h
  contradiction
  rename_i g
  rw [h] at g
  cases g
  rename_i g _
  rw [h] at g
  cases g
  assumption

instance : Iterator (List α) α where
  next
  | [] => .none
  | x::xs => (xs, x)

instance (xs: List α) : Iterator.IsFinite xs := by
    induction xs with
    | nil =>
      apply Iterator.IsFinite.empty
      rfl
    | cons x xs ih =>
      apply Iterator.IsFinite.next
      rfl; assumption

def with_iterator (σ: Type*) := σ

instance [Iterator σ α] : Iterator (with_iterator σ) (σ × α) where
  next x := match next (σ := σ) x with
    | .some x => .some (x.1, x)
    | .none => .none

end Iterator
