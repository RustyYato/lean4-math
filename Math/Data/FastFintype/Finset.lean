import Math.Data.Finset.Basic
import Math.Data.FastFintype.Defs
import Math.Data.Vector.Defs
import Math.Data.Set.Basic

def Finset.univ (α: Type*) [Fintype α] : Finset α where
  val := Fintype.lift (fun f: Fintype.Encoding α => Multiset.mk (List.ofFn f.all)) (by
    classical
    intro x y
    have ⟨eqv, h⟩ := x.equiv y
    dsimp; apply Quotient.sound
    have := Function.Vector.perm_of_equiv (.ofList (List.ofFn x.all)) (.ofList (List.ofFn y.all)) (
        (Equiv.fin (by simp)).trans (eqv.trans (Equiv.fin (by simp)))) ?_
    rwa [ Function.Vector.Perm.iff_ofList_perm] at this
    intro i
    simp
    apply h)
  property := by
    rename_i fα
    induction fα with | mk fα =>
    show (Multiset.mk _).Nodup
    apply (List.nodup_ofFn _).mp
    exact fα.all.inj

@[simp]
def Finset.mem_univ {α: Type*} [fα: Fintype α] (a: α) : a ∈ Finset.univ α := by
  induction fα with | mk fα =>
  show a ∈ List.ofFn fα.all
  simp;
  have ⟨i, eq⟩ := fα.complete a
  exists i; symm; assumption

instance [DecidableEq α] [Fintype α] : SetComplement (Finset α) where
  scompl x := Finset.univ α \ x

@[simp]
def Finset.mem_compl {α: Type*} [DecidableEq α] [fα: Fintype α] {s: Finset α}:
  ∀{x}, x ∈ sᶜ ↔ x ∉ s := by
  intro x
  show x ∈ _ \ _  ↔ _
  simp [Finset.mem_sdiff]

@[simp]
def Finset.compl_compl {α: Type*} [DecidableEq α] [fα: Fintype α] (s: Finset α): sᶜᶜ = s := by
  ext x; simp
