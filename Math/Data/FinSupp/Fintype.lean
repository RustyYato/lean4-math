import Math.Data.FinSupp.Algebra
import Math.Data.Fintype.Algebra

namespace Finsupp

variable [FiniteSupportSet S ι]

def sum_eq_fintypesum
  [Zero α] [∀a: α, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0):
  f.sum g resp = ∑i: f.support, g i.val (f i.val) := by
  rw [Finsupp.sum_eq_support_sum]
  unfold _root_.sum
  show _ = ((Multiset.map ((fun i => g i (f i)) ∘ (fun i: f.support => i.val))) _).sum
  rw [←Multiset.map_map]
  congr
  unfold Finset.univ Fintype.all instFintypeElem
  simp
  suffices f.support = f.support.attach.map_emb Embedding.subtypeVal by
    rw (occs := [1]) [this]
    rfl
  ext i
  simp [Finset.mem_map_emb]
  apply Iff.intro
  intro h
  refine ⟨i, h, ?_, ?_⟩
  apply Finset.mem_attach
  rfl
  rintro ⟨i, h, _, rfl⟩
  assumption

end Finsupp
