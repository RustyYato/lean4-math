-- an axiomatic version of trunc, just to show all the guts that
-- are hidden by lean

axiom Trunc (α: Type u) : Type u

instance [Nonempty α] (f: α -> β) : Subsingleton { x // ∀a: α, x = f a } where
  allEq a b := by
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    rename_i h
    obtain ⟨x⟩ := h
    cases ha x
    cases hb x
    rfl

noncomputable section

namespace Trunc

variable {α: Type u}
-- the constructor for `Trunc`
protected axiom mk (a: α) : Trunc α

-- the recursor for `Trunc`, you can only eliminate a Trunc
-- iff you are eliminating into a subsingleton type
@[elab_as_elim]
protected axiom rec
  {motive: Trunc α -> Sort v}
  [∀f, Subsingleton (motive f)]
  (mk: ∀a, motive (.mk a))
  (t: Trunc α) :
  motive t
-- Trunc is subsingleton by definition
protected axiom sound (a b: Trunc α) : a = b
-- the computation rule for `rec`
protected axiom compute
  {motive: Trunc α -> Sort v}
  [∀f, Subsingleton (motive f)]
  (mk': ∀a, motive (.mk a))
  (a: α) : Trunc.rec mk' (.mk a) = mk' a

instance : Subsingleton (Trunc α) where
  allEq := Trunc.sound

@[induction_eliminator]
def ind {motive: Trunc α -> Prop} (mk: ∀a, motive (.mk a)) (x: Trunc α) : motive x := by
  apply Trunc.rec (motive := motive)
  assumption

def lift (f: α -> β) (hf: ∀a b, f a = f b) (x: Trunc α) : β :=
  have : Nonempty α := by induction x with | mk x => exact ⟨x⟩
  (show { x // ∀a, x = f a } by
    apply x.rec (motive := fun _ => _) fun a => ?_
    exists f a
    intro x
    apply hf).val

def lift_mk (f: α -> β) (hf: ∀a b, f a = f b) (x: α) : lift f hf (.mk x) = f x := by
  have : Nonempty α := ⟨x⟩
  unfold lift
  simp
  rw [Trunc.compute]

def casesOn.{u_1} : {motive : Trunc α → Sort u_1} → [∀f, Subsingleton (motive f)] → (t : Trunc α) → ((a : α) → motive (.mk a)) → motive t :=
fun {motive} _ t mk => Trunc.rec (motive := motive) (fun a => mk a) t

instance : Monad Trunc where
  pure := .mk
  bind t f := t.rec f

instance {α: Type _ -> Type _} [∀i, Subsingleton (α i)] [Monad α] : LawfulMonad α where
  map_const := Subsingleton.allEq _ _
  id_map _ := Subsingleton.allEq _ _
  seqLeft_eq _ _ := Subsingleton.allEq _ _
  seqRight_eq _ _ := Subsingleton.allEq _ _
  pure_seq _ _ := Subsingleton.allEq _ _
  bind_pure_comp _ _ := Subsingleton.allEq _ _
  bind_map _ _ := Subsingleton.allEq _ _
  pure_bind _ _ := Subsingleton.allEq _ _
  bind_assoc _ _ _ := Subsingleton.allEq _ _

end Trunc

end
