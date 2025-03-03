import Math.Data.Fintype.Defs

namespace Fin

def all_fins_until (n: Nat) : ∀m ≤ n, List (Fin n)
| 0, _ => []
| m+1, h => ⟨m, Nat.lt_of_succ_le h⟩::all_fins_until n m (Nat.le_trans (Nat.le_succ _) h)

def all_fins (n: Nat) := all_fins_until n n (Nat.le_refl _)

def mem_all_fins_until (n m: Nat) (h: m ≤ n) :
  ∀{x}, x ∈ all_fins_until n m h ↔ x < m := by
  intro x
  induction m with
  | zero =>
    apply Iff.intro
    iterate 2
      intro
      contradiction
  | succ m ih =>
    apply Iff.intro
    intro g
    cases g
    apply Nat.lt_succ_self
    apply Nat.lt_trans
    apply (ih _).mp
    assumption
    apply Nat.lt_succ_self
    intro g
    cases x with | mk x xLt =>
    dsimp at g
    cases Nat.lt_or_eq_of_le <| Nat.le_of_lt_succ g <;> rename_i g
    apply List.Mem.tail
    apply (ih _).mpr
    assumption
    subst x
    apply List.Mem.head

def mem_all_fins (n: Nat) :
  ∀x, x ∈ all_fins n := by
  intro x
  apply (mem_all_fins_until _ _ (Nat.le_refl _)).mpr
  exact x.isLt

def all_fins_until_nodup (n m: Nat) (h: m ≤ n) :
  (all_fins_until n m h).Nodup := by
  induction m with
  | zero => apply List.Pairwise.nil
  | succ m ih =>
    apply List.Pairwise.cons
    intro x g xeq
    subst x
    exact Nat.lt_irrefl _ <| (mem_all_fins_until _ _ _).mp g
    apply ih

def all_fins_nodup (n: Nat) : (all_fins n).Nodup := all_fins_until_nodup _ _ _

def length_all_fins_unil (n m: Nat) (h: m ≤ n) : (all_fins_until n m h).length = m := by
  induction m
  rfl
  unfold all_fins_until List.length
  congr
  rename_i ih
  apply ih

def length_all_fins (n: Nat) : (all_fins n).length = n := length_all_fins_unil _ _ _

instance : Fintype (Fin n) where
  all := Fin.all_fins _
  nodup := Fin.all_fins_nodup _
  complete := Fin.mem_all_fins _

end Fin

def Fin.card_eq (f: Fintype (Fin n)) : f.card = n := by
  rw [Fintype.card_eq _ Fin.instFintype]
  unfold Fintype.card Fin.instFintype Fintype.all
  simp
  rw [length_all_fins]
