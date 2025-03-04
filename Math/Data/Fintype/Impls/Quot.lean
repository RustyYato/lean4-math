import Math.Data.Fintype.Defs
import Math.Data.Quotient.Basic
import Math.Logic.Equiv.Basic

namespace Quotient

private def list_choice [DecidableEq ι] {α: ι -> Sort*} [S: ∀i, Setoid (α i)] (f: ∀i, Quotient (S i)):
  ∀(list: List ι), Quotient (Setoid.forallSetoid (fun x: { i: ι // i ∈ list } => α x))
| [] => Quotient.mk _ nofun
| i::rest =>
  Quotient.liftOn₂ (f i) (list_choice f rest)
    (fun a f' => Quotient.mk _ (fun ⟨i₀, hi⟩  => if h:i = i₀ then Eq.ndrec a h else f' ⟨i₀, by
      cases hi
      contradiction
      assumption⟩)) (by
      intro a b c d ac bd
      dsimp
      apply Quotient.sound
      intro ⟨i₀, hi⟩
      dsimp
      split
      subst i
      assumption
      apply bd)

def mk_list_choice {ι : Type*} [DecidableEq ι] {α: ι -> Sort*}
    [S: ∀i, Setoid (α i)] (f: ∀i, α i) :
    ∀(l : List ι), (list_choice (fun i => Quotient.mk _ (f i)) l) = Quotient.mk (Setoid.forallSetoid _) (fun x: { i: ι // i ∈ l } => f x) := by
    intro list
    induction list with
    | nil =>
      apply Quotient.sound
      nofun
    | cons i list ih =>
      unfold list_choice
      rw [ih]; clear ih
      apply Quotient.sound
      intro ⟨i₀, h⟩
      dsimp; split
      subst i
      rfl
      rfl

def list_exists_rep
  [DecidableEq ι]
  {α: ι -> Sort*}
  [S: ∀i, Setoid (α i)]
  (f: ∀i, Quotient (S i)) :
  ∀(list: List ι), ∃g: ∀i ∈ list, α i, (fun i (h: i ∈ list) => f i) = fun i (h: i ∈ list) => Quotient.mk _ (g i h) := by
  intro list
  induction list with
  | nil =>
    exists nofun
    ext i h
    contradiction
  | cons i rest ih =>
    obtain ⟨g, eq⟩ := ih
    obtain ⟨a, eq'⟩ := (f i).exists_rep
    refine ⟨?_, ?_⟩
    intro i₀ h
    if i = i₀ then
      subst i₀
      assumption
    else
      apply g
      cases h
      contradiction
      assumption
    ext i₀ h
    split
    subst i₀
    symm; assumption
    apply congrFun (congrFun eq _)

def fin_ind
  [DecidableEq ι]
  [ft: Fintype ι]
  {α: ι -> Sort*}
  [S: ∀i, Setoid (α i)]
  {motive: (∀i, Quotient (S i)) -> Prop}
  (mk: ∀(f: ∀i, α i), motive (fun i => Quotient.mk _ (f i)))
  (f: ∀i, Quotient (S i)) : motive f :=
  match ft with
  | .mk ⟨all, nodup⟩ complete => by
    cases all with | mk all =>
    replace complete: ∀x, x ∈ all := complete
    replace nodup: all.Nodup := nodup
    have ⟨g, f_eq_g⟩  := list_exists_rep f all
    let f' : ∀i, α i := fun i => g i (complete _)
    have : f = fun i => Quotient.mk _ (f' i) := by
      ext i
      exact congrFun (congrFun f_eq_g i) (complete _)
    rw [this]
    apply mk

variable [DecidableEq ι] [ft: Fintype ι] {α: ι -> Sort*} [S: ∀i, Setoid (α i)]

def fin_choice (f: ∀i, Quotient (S i)): Quotient (Setoid.forallSetoid α) := by
  let e := Equiv.subtype_quot_equiv_quot_subtype
    (fun l : List ι ↦ ∀ i, i ∈ l)
    (fun s : Multiset ι ↦ ∀ i, i ∈ s)
    (s₂ := Setoid.subtypeSetoid _)
    (fun i ↦ Iff.rfl)
    (fun _ _ ↦ Iff.rfl) ⟨_, Finset.mem_univ⟩
  refine e.lift ?_ ?_
  · intro ⟨all, complete⟩
    refine (list_choice f all).lift ?_ ?_
    · intro f
      apply Quotient.mk
      intro i
      exact f ⟨i, complete _⟩
    · intro a b eqv
      apply Quotient.sound
      intro i
      apply eqv
  · intro ⟨as, as_complete⟩ ⟨bs, bs_complete⟩ eqv
    dsimp only
    induction f using fin_ind with | mk f =>
    rw [mk_list_choice, mk_list_choice]
    rfl

def mk_fin_choice (a : ∀ i, α i) :
    fin_choice (S := S) (Quotient.mk _ <| a ·) = Quotient.mk _ a := by
  dsimp [fin_choice]
  obtain ⟨l, hl⟩ := ((Finset.univ _).val : Multiset ι).exists_rep
  simp [←hl, Equiv.subtype_quot_equiv_quot_subtype, mk_list_choice]
  rfl

def fin_choice_equiv: (∀i, Quotient (S i)) ≃ Quotient (Setoid.forallSetoid α) where
  toFun := fin_choice
  invFun := apply
  leftInv := by
    intro f
    induction f using fin_ind with | mk f =>
    rw [mk_fin_choice]
    rfl
  rightInv := by
    intro f
    induction f using Quot.ind with | mk f =>
    apply mk_fin_choice

def mk_fin_choice_equiv (f: ∀i, α i): fin_choice_equiv (fun i => Quotient.mk _ (f i)) = Quotient.mk _ f := by
  apply mk_fin_choice

def mk_fin_choice_equiv_symm (f: ∀i, α i): fin_choice_equiv.symm (Quotient.mk _ f) = fun i => Quotient.mk _ (f i)  := by
  apply fin_choice_equiv.inj
  rw [Equiv.symm_coe, mk_fin_choice_equiv]

def fin_ilift
  {S: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β) (resp: ∀a b: ∀i, α i, (∀i, a i ≈ b i) -> f a = f b)
  (q: ∀i, Quotient (S i)) : β := (fin_choice_equiv q).lift f resp

def mk_fin_ilift
  [S: ∀i, Setoid (α i)]
  (f: (∀i, α i) -> β) (resp: ∀a b: ∀i, α i, (∀i, a i ≈ b i) -> f a = f b)
  (a: ∀i, α i) :
  fin_ilift f resp (fun i => Quotient.mk _ (a i)) = f a := by
  unfold fin_ilift
  rw [mk_fin_choice_equiv]
  rfl

end Quotient

namespace Fintype

def equiv_trunc_subtype  : Fintype α ≃ Trunc { list: List α // list.Nodup ∧ ∀x, x ∈ list } where
  toFun f := by
    apply f.recOnSubsingleton
    intro all nodup complete
    exact Trunc.mk {
      val := all
      property := ⟨nodup, complete⟩
    }
  invFun f := by
    apply f.recOnSubsingleton (motive := fun _ => _)
    intro ⟨all, ⟨nodup, complete⟩⟩
    exact {
      all := ⟨Multiset.mk all, nodup⟩
      complete := complete
    }
  leftInv _ := by apply Subsingleton.allEq
  rightInv _ := by apply Subsingleton.allEq

end Fintype
