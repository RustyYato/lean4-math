import Math.Data.Encodable.Defs
import Math.Data.Quotient.Basic

namespace Quotient

private unsafe def countable_ilift'
  {α: ℕ -> Type*}
  {S: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β) (_resp: ∀a b: ∀i, α i, (∀i, a i ≈ b i) -> f a = f b)
  (q: ∀i, Quotient (S i)) : β := f (fun i => (q i).lift id lcProof)

-- this is safe because `Nat` has one canonical representation. i.e.
-- for every closed term of `Nat` it is either defeq or not equal
-- which means that `f` can only take on one value per `Nat`
@[implemented_by countable_ilift']
def countable_ilift
  {α: ℕ -> Type*}
  {S: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β) (resp: ∀a b: ∀i, α i, (∀i, a i ≈ b i) -> f a = f b)
  (q: ∀i, Quotient (S i)) : β := Quotient.ilift f resp q

@[simp]
def countable_ilift_mk
  {α: Nat -> Type*}
  {S: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β) (resp: ∀a b: ∀i, α i, (∀i, a i ≈ b i) -> f a = f b)
  (q: ∀i, α i) : countable_ilift f resp (fun i => Quotient.mk _ (q i)) = f q := by
  apply Quotient.mk_ilift

attribute [irreducible] countable_ilift

variable [e: Encodable ι] {α: ι -> Type*} [S: ∀i, Setoid (α i)]

@[irreducible]
def countableChoice (f: ∀i, Quotient (S i)): Quotient (Setoid.forallSetoid α) := by
  let α' (e: Encodable.Repr ι) (i: ℕ) := match e.decode i with
    | .some x => α x
    | .none => PUnit
  let S' (e: Encodable.Repr ι) (i: ℕ) : Setoid (α' e i) := by
    unfold α'
    exact match e.decode i with
    | .some x => S x
    | .none => Setoid.trueSetoid _
  let f' (e: Encodable.Repr ι) (i: ℕ) : Quotient (S' e i) :=by
    unfold S' α'
    exact match e.decode i with
    | .some x => f x
    | .none => Trunc.mk PUnit.unit
  let mk' (e: Encodable.Repr ι) (i: ℕ) : α' e i -> Quotient (S' e i) := by
    unfold S' α'
    exact match e.decode i with
    | .some i => Quotient.mk _
    | .none => Trunc.mk

  refine e.toRepr.lift ?_ ?_
  · intro e
    have := countable_ilift (α := α' e) (S := S' e) (β := Quotient (@Setoid.forallSetoid (α := α' e) _ (S' e))) (Quotient.mk _) (by
      intro f₀ f₁ h
      apply Quotient.sound
      intro i; apply h) (f' e)
    refine this.lift ?_ ?_
    · intro g
      apply Quotient.mk _
      intro i
      have := g (e i)
      refine cast ?_ this
      simp [α']
    · dsimp
      intro f g h
      apply Quotient.sound
      intro i
      dsimp
      apply (@Setoid.cast_eqv' _ _ _ _ _ _ _ _).mpr (h (e i))
      dsimp
      simp [S', α']
      rw [e.coe_decode]
  · intro r₀ r₁
    dsimp
    induction hf:f using Quotient.iind with | mk f₀ =>
    have h₀ : f' r₀ = (fun i => Quotient.mk _ <| by
      unfold α'
      exact match r₀.decode i with
      | .some x => f₀ x
      | .none => PUnit.unit) := by
      ext i; dsimp [f', S', α']
      rw [hf]
      dsimp
      split
      rfl
      rfl
    have h₁ : f' r₁ = (fun i => Quotient.mk _ <| by
      unfold α'
      exact match r₁.decode i with
      | .some x => f₀ x
      | .none => PUnit.unit) := by
      ext i; dsimp [f', S', α']
      rw [hf]
      dsimp
      split
      rfl
      rfl
    rw [h₀, h₁]; clear h₀ h₁
    simp [Quotient.mk_lift]
    apply Quotient.sound
    intro i; dsimp
    rw [Setoid.cast_eqv₀ (h₀ := by simp [α']) (h₁ := by simp [α']) (Sβ := S' _ _) (Sα := S' _ _) (x := f₀ i) (y := f₀ i)]
    · simp [S', α']
      rw [r₀.coe_decode]
    · simp [S', α']
      rw [r₁.coe_decode]
    · simp [S', α']
      rw [r₀.coe_decode]
    · simp [S', α']
      rw [r₁.coe_decode]

def countableChoice_mk (f: ∀i, α i): countableChoice (fun i => Quotient.mk _ (f i)) = Quotient.mk _ f := by
  let α' (e: Encodable.Repr ι) (i: ℕ) := match e.decode i with
    | .some x => α x
    | .none => PUnit
  let S' (e: Encodable.Repr ι) (i: ℕ) : Setoid (α' e i) := by
    unfold α'
    exact match e.decode i with
    | .some x => S x
    | .none => Setoid.trueSetoid _
  let mk' (e: Encodable.Repr ι) (i: ℕ) : α' e i -> Quotient (S' e i) := by
    unfold S' α'
    exact match e.decode i with
    | .some i => Quotient.mk _
    | .none => Trunc.mk
  let f' (e: Encodable.Repr ι) (i: ℕ) : Quotient (S' e i) := by
    unfold S' α'
    exact match e.decode i with
    | .some i => Quotient.mk _ (f i)
    | .none => Trunc.mk PUnit.unit
  let f'' (e: Encodable.Repr ι) (i: ℕ) : Quotient (S' e i) := by
    unfold S' α'
    exact Quotient.mk _ <| match e.decode i with
    | .some i => (f i)
    | .none => PUnit.unit
  have f'_eq_f'': f' = f'' := by
    simp [f', f'', S', α']
    ext e i
    split <;> rfl
  unfold countableChoice
  cases e with | ofRepr e =>
  induction e with | mk e =>
  simp
  show Quotient.lift _ _ (countable_ilift (fun f₀ => Quotient.mk _ _) _ (f' e)) = _
  rw [f'_eq_f'']
  erw [countable_ilift_mk, Quotient.mk_lift]
  apply Quotient.sound
  intro i
  simp
  apply Setoid.eqv_of_eq
  apply cast_eq_of_heq
  rw [e.coe_decode]

end Quotient
