noncomputable
def Quot.out {r: α -> α -> Prop} (q: Quot r) : α := Classical.choose q.exists_rep
noncomputable
def Quotient.out {s: Setoid α} (q: Quotient s) : α := Quot.out q

noncomputable
def Quot.out_spec {r: α -> α -> Prop} (q: Quot r) : Quot.mk r q.out = q := Classical.choose_spec q.exists_rep
noncomputable
def Quotient.out_spec {s: Setoid α} (q: Quotient s) : Quotient.mk s q.out = q := Quot.out_spec q

def Quot.mk_lift : Quot.lift f resp (Quot.mk _ x) = f x := rfl

def Quotient.mk_lift : Quotient.lift f resp (Quotient.mk _ x) = f x := rfl

def Quotient.iind
  {α: ι -> Sort u}
  {s: ∀i: ι, Setoid (α i)}
  {motive: (∀i, Quotient (s i)) -> Prop}
  (mk: ∀f: ∀i, α i, motive (fun x => (Quotient.mk (s _) (f x)))):
  ∀f, motive f := by
  intro f
  have : ∀x: ι, ∃y, Quotient.mk (s _) y = f x := by
    intro x
    apply Quotient.exists_rep
  have ⟨g, eq⟩ := Classical.axiomOfChoice this
  rw [show f = (fun x => (Quotient.mk (s _) (g x))) from ?_]
  apply mk
  ext x
  symm; apply eq

noncomputable def Quotient.ilift
  {α: ι -> Sort u}
  {s: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β)
  (_resp: ∀g₀ g₁: ∀i, α i, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁):
  (∀i, Quotient (s i)) -> β := fun h => f (fun i => (h i).out)

def Quotient.mk_ilift
  {α: ι -> Sort u}
  {s: ∀i, Setoid (α i)}
  (f: (∀i, α i) -> β)
  (resp: ∀g₀ g₁: ∀i, α i, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁)
  (h: ∀i, α i):
  Quotient.ilift f resp (fun i => Quotient.mk (s i) (h i)) = f h := by
  apply resp
  intro
  dsimp
  apply Quotient.exact
  apply Quotient.out_spec _

def Quot.hsound
  {r: α -> α -> Prop}
  {s: β -> β -> Prop}
  (a: α)
  (b: β)
  (tyeq: α = β)
  (releq: HEq r s) :
  r a (tyeq ▸ b) ->
  HEq (Quot.mk r a) (Quot.mk s b) := by
  intro h
  subst tyeq
  subst releq
  apply heq_of_eq
  apply sound
  assumption
