unsafe def Quot.usnafe_cast_unchecked {r: α -> α -> Prop} : Quot r -> α := Quot.lift id lcProof

noncomputable
def Quot.out {r: α -> α -> Prop} (q: Quot r) : α := Classical.choose q.exists_rep
noncomputable
def Quotient.out {s: Setoid α} (q: Quotient s) : α := Quot.out q

noncomputable
def Quot.out_spec {r: α -> α -> Prop} (q: Quot r) : Quot.mk r q.out = q := Classical.choose_spec q.exists_rep
noncomputable
def Quotient.out_spec {s: Setoid α} (q: Quotient s) : Quotient.mk s q.out = q := Quot.out_spec q

def Quotient.mk_lift : Quotient.lift f resp (Quotient.mk _ x) = f x := rfl

private unsafe def Quotient.ilift_compute {s: Setoid α}
  (f: (ι -> α) -> β)
  (_resp: ∀g₀ g₁: ι -> α, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁):
  (ι -> Quotient s) -> β :=
  fun h => f (fun i => (h i).usnafe_cast_unchecked)

@[implemented_by Quotient.ilift_compute]
def Quotient.ilift {s: Setoid α}
  (f: (ι -> α) -> β)
  (_resp: ∀g₀ g₁: ι -> α, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁):
  (ι -> Quotient s) -> β :=
  fun h => f (fun i => (h i).out)

def Quotient.mk_ilift {s: Setoid α}
  (f: (ι -> α) -> β)
  (resp: ∀g₀ g₁: ι -> α, (∀x, g₀ x ≈ g₁ x) -> f g₀ = f g₁)
  (h: ι -> α):
  Quotient.ilift f resp (fun x => Quotient.mk s (h x)) = f h := by
  apply resp
  intro
  dsimp
  apply Quotient.exact
  apply Quotient.out_spec _

def Quotient.iind
  {s: Setoid α}
  {motive: (ι -> Quotient s) -> Prop}
  (mk: ∀f: ι -> α, motive (fun x => (Quotient.mk s (f x)))):
  ∀f, motive f := by
  intro f
  have : ∀x: ι, ∃y, Quotient.mk s y = f x := by
    intro x
    apply Quotient.exists_rep
  have ⟨g, eq⟩ := Classical.axiomOfChoice this
  rw [show f = (fun x => (Quotient.mk s (g x))) from ?_]
  apply mk
  ext x
  symm; apply eq
