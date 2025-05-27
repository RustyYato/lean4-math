import Math.Data.Fintype.Impls.Pi
import Math.Data.Fintype.Impls.Sigma
import Math.Data.Fintype.Impls.Embed
import Math.Data.Fintype.Impls.Equiv

namespace Fintype

def exists_not_mem_preimage_aux (f: Fin n ↪ α) (l: List α) (h: ∀x, f x ∈ l) : n ≤ l.length := by
  induction n generalizing l with
  | zero => apply Nat.zero_le
  | succ n ih =>
    cases l with
    | nil =>
    have := h 0
    contradiction
    | cons l ls =>
    apply Nat.succ_le_succ
    by_cases g:∃x, f x = l
    · obtain ⟨i, hi⟩ := g
      apply ih ((Embedding.fin_erase i).trans f) ls ?_
      intro x
      simp
      by_cases hx:x.val < i
      rw [Embedding.apply_fin_erase_of_lt _ _ hx]
      cases h x.castSucc
      rw [f.inj.eq_iff] at hi
      subst i
      have := Nat.lt_irrefl _ hx
      contradiction
      assumption
      simp at hx
      rw [Embedding.apply_fin_erase_of_ge _ _ hx]
      cases h x.succ
      rw [f.inj.eq_iff] at hi
      subst i
      have : x.val + 1 ≤ x.val := hx
      omega
      assumption
    · simp at g
      apply ih ((Embedding.finSucc _).trans f) ls ?_
      intro x
      cases h x.succ
      have := g x.succ
      contradiction
      assumption

def exists_not_mem_preimage [Fintype ι] (f: ι ↪ α) (l: List α) (h: l.length < card ι) : ∃i: ι, f i ∉ l := by
  classical
  apply Classical.byContradiction
  intro g; simp at g
  rw [←Nat.not_le] at h
  apply h; clear h
  rename_i fι
  induction fι using ind generalizing l with
  | @ind card rι =>
  show card ≤ _
  have decode : Fin card ↪ ι := ⟨rι.decode, rι.bij.Injective⟩
  let f' := decode.trans f
  replace g : ∀i, f' i ∈ l := by
    intro i
    apply g
  apply exists_not_mem_preimage_aux
  assumption

end Fintype
