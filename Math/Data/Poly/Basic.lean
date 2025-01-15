import Math.Function.Basic
import Math.Data.Like.Func
import Math.Data.StdNat.Find
import Math.Relation.Basic

def Poly.DegreeLe [Zero α] (f: Nat -> α) (bound: Nat) :=
  ∀n > bound, f n = 0

structure Poly (α: Type*) [Zero α] where
  coeffs: Nat -> α
  has_degree: Squash (Σ'bound: Nat, Poly.DegreeLe coeffs bound)

namespace Poly

instance [Zero α] : Zero (Poly α) where
  zero := {
    coeffs _ := 0
    has_degree := Squash.mk ⟨0, fun _ _ => rfl⟩
  }

section degree

variable [Zero α] [BEq α] [LawfulBEq α]

private
def findDegree (f: Nat -> α) : (Σ'm: Nat, Poly.DegreeLe f m) -> Σ'm: Nat, Poly.DegreeLe f m ∧ ∀x, Poly.DegreeLe f x -> m ≤ x
| ⟨0, h⟩ => ⟨0, h, fun _ _ => Nat.zero_le _⟩
| ⟨m + 1, hm⟩ => by
  if f (m + 1) == 0 then
    refine Poly.findDegree f ⟨m, ?_⟩
    intro n m_lt_n
    have := hm n
    rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt m_lt_n) with m_lt_n | m_eq_n
    apply hm
    assumption
    subst n
    apply LawfulBEq.eq_of_beq
    assumption
  else
    refine ⟨m+1, hm, ?_⟩
    intro x deg
    apply Decidable.byContradiction
    intro g
    replace g := Nat.lt_of_not_le g
    rw [(deg _ g), LawfulBEq.rfl] at *
    contradiction

def degree (p: Poly α) : Nat := by
  apply p.has_degree.liftOn _ _
  intro h
  -- search for the degree starting at the current degree
  -- since we expect that to be a good estimate. This way we
  -- will usually only have to check a single number
  exact (findDegree p.coeffs h).fst
  intro a b _
  generalize Poly.findDegree p.coeffs a = x
  generalize Poly.findDegree p.coeffs b = y
  apply Nat.le_antisymm
  apply x.snd.right
  exact y.snd.left
  apply y.snd.right
  exact x.snd.left

def degree.DegreeLe (p: Poly α) : Poly.DegreeLe p.coeffs p.degree := by
  cases p with
  | mk f h =>
  induction h using Quot.ind with
  | mk h =>
  dsimp
  exact (Poly.findDegree f h).snd.left

def degree_is_minimal (p: Poly α) : ∀x, Poly.DegreeLe p.coeffs x -> p.degree ≤ x := by
  cases p with
  | mk f h =>
  induction h using Quot.ind with
  | mk h =>
  dsimp
  exact (Poly.findDegree f h).snd.right

end degree

end Poly
