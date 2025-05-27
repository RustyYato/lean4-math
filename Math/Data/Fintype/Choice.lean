import Math.Data.Fintype.Defs
import Math.Data.Quotient.Basic
import Math.Data.Setoid.Basic

namespace Quotient

private unsafe def fin_ilift'
  {α: Fin n -> Type*}
  {S: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β) (_resp: ∀a b: ∀i, α i, (∀i, a i ≈ b i) -> f a = f b)
  (q: ∀i, Quotient (S i)) : β := f (fun i => (q i).lift id lcProof)

-- this is safe because `Fin n` has one canonical representation. i.e.
-- for every closed term of `Fin n` it is either defeq or not equal
-- which means that `f` can only take on one value per `Fin n`
@[implemented_by fin_ilift']
def fin_ilift
  {α: Fin n -> Type*}
  {S: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β) (resp: ∀a b: ∀i, α i, (∀i, a i ≈ b i) -> f a = f b)
  (q: ∀i, Quotient (S i)) : β :=
  match hn':n with
  | 0 => f nofun
  | n + 1 =>
    fin_ilift (fun f' =>
      (q 0).lift (fun a =>
        f (fun
        | 0 => a
        | ⟨i + 1, hi⟩ => f' ⟨i, Nat.lt_of_succ_lt_succ hi⟩)) <| by
        intro a b hj
        simp
        apply resp
        intro i
        cases i using Fin.cases
        assumption
        rfl) (by
        intro a b h
        induction q 0 using Quotient.ind with | _ q' =>
        simp [Quotient.mk_lift]
        apply resp
        intro i
        cases i using Fin.cases
        rfl
        apply h) (fun i => q i.succ)

@[simp]
def fin_ilift_mk
  {α: Fin n -> Type*}
  {S: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β) (resp: ∀a b: ∀i, α i, (∀i, a i ≈ b i) -> f a = f b)
  (q: ∀i, α i) : fin_ilift f resp (fun i => Quotient.mk _ (q i)) = f q := by
  induction n with
  | zero =>
    show f _ = _
    congr
    apply Subsingleton.allEq
  | succ n ih =>
    unfold Quotient.fin_ilift
    simp [Quotient.mk_lift, ih]
    congr; ext i
    cases i using Fin.cases
    rfl
    rfl

def fin_ind {α: Fin n -> Type*} [S: ∀i, Setoid (α i)] {motive: (∀i, Quotient (S i)) -> Prop}
  (mk: ∀f: ∀i, α i, motive (fun i => Quotient.mk _ (f i)))
  (q: ∀i, Quotient (S i)) : motive q := by
  induction n with
  | zero =>
    rw [show q = fun i => Quotient.mk _ i.elim0 from ?_]
    apply mk
    apply Subsingleton.allEq
  | succ n ih =>
    have := ih (α := fun i => α i.succ) (motive := fun f' => motive <| fun
      | 0 => q 0
      | ⟨i + 1, hi⟩ => f' ⟨i, Nat.lt_of_succ_lt_succ hi⟩) ?_ (fun i => q i.succ)
    apply cast _ this
    congr; ext i
    cases i using Fin.cases
    rfl
    rfl
    intro f
    induction h:q 0 using Quotient.ind with | _ q₀ =>
    apply cast _ (mk <| fun
      | 0 => q₀
      | ⟨i + 1, hi⟩ => f ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
    congr
    ext i
    cases i using Fin.cases
    rfl
    rfl

variable [DecidableEq ι] [Fintype ι] {α: ι -> Type*} [S: ∀i, Setoid (α i)]

def finInd
  {motive : (∀i, Quotient (S i)) -> Prop}
  (mk: ∀f: ∀i, α i, motive (fun i => Quotient.mk _ (f i)))
  (q: ∀i, Quotient (S i)) : motive q := by
  rename_i fι
  induction fι.toEquiv with | _ eqv =>
  let q' := fun i => q (eqv i)
  induction hq':q' using fin_ind with | _ q'₀ =>
  let q'' : ∀i, Quotient (S i) := fun i => Quotient.mk (S i) (cast (by congr <;> simp) (q'₀ (eqv.symm i)))
  rw [show q = q'' from ?_]
  apply mk
  ext i
  rw [←eqv.symm_coe i]
  show q' _ = _
  simp [q'', hq']
  apply Quotient.sound
  apply Setoid.eqv_of_eq
  symm; apply cast_eq_of_heq
  congr
  simp

def finChoice (f: ∀i, Quotient (S i)): Quotient (Setoid.forallSetoid α) := by
  refine (Fintype.toEquiv ι).lift ?_ ?_
  · intro eqv
    refine fin_ilift ?_ ?_ (fun i => f (eqv i))
    · intro g
      apply Quotient.mk _
      intro i
      apply cast _ (g (eqv.symm i))
      congr; simp
    · intro a b h
      apply Quotient.sound
      intro i
      simp
      have := h (eqv.symm i)
      rwa [Setoid.cast_eqv]
      rw [Equiv.symm_coe]
  · intro a b
    induction f using finInd with | mk f =>
    simp
    apply Quotient.sound
    intro i
    simp
    apply Setoid.eqv_of_eq
    congr 1
    simp
    apply proof_irrel_heq
    rw [Equiv.symm_coe, Equiv.symm_coe]

def finChoice_mk (a : ∀ i, α i) : finChoice (S := S) (Quotient.mk _ <| a ·) = Quotient.mk _ a := by
  rename_i fι
  unfold finChoice
  induction heqv:Fintype.toEquiv ι with | _ eqv =>
  simp
  apply Quotient.sound
  intro i
  apply Setoid.eqv_of_eq
  simp
  apply cast_eq_of_heq
  rw [Equiv.symm_coe]

end Quotient
