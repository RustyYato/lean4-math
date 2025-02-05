import Math.Data.Set.Finite
import Math.Order.Lattice.SetLike
import Math.Data.EncodableInto.Basic
import Math.Algebra.Ring

variable (α β: Type*) (S: Type*) [SetLike S α]

section

variable (f: α -> β) (default: β) (set: S)

structure FinSupp.FiniteSupport where
  card: Nat
  set: S
  decMem: DecidablePred (· ∈ set) := by infer_instance
  enc: EncodableInto set (Fin card)
  spec: ∀x, f x ≠ default -> x ∈ set

end

structure FinSupp (default: β) where
  toFun: α -> β
  support: Squash (FinSupp.FiniteSupport α β S toFun default)

variable {α: Type*} {β: Type*} {default: β} {S: Type*} [SetLike S α]
  [Sup S] [Inf S] [LE S] [LT S] [IsSetLikeLattice S]

instance : FunLike (FinSupp α β S default) α β where
  coe x := x.toFun
  coe_inj := by
    intro a b eq
    cases a; cases b; congr
    apply Subsingleton.helim
    dsimp at eq
    rw [eq]

@[ext]
def FinSupp.ext (a b: FinSupp α β S default) : (∀x, a x = b x) -> a = b :=
  DFunLike.ext _ _

private def sup_encodable
  (ha: FinSupp.FiniteSupport α β S f default₀)
  (hb: FinSupp.FiniteSupport α β S g default₁) : EncodableInto (ha.set ⊔ hb.set: S) (Fin (ha.card + hb.card)) where
  encode_into x :=
    match hb.decMem x with
    | .isTrue hx => (hb.enc.encode_into ⟨x, hx⟩).castLE (Nat.le_add_left _ _)
    | .isFalse hx =>
      (ha.enc.encode_into ⟨x, by
        have := x.property
        rw [←mem_coe, IsSetLikeLattice.sup_eq_set_sup] at this
        cases this
        assumption
        contradiction⟩).addNat hb.card
  decode_from' x :=
    if hx:x.val < hb.card then
      match hb.enc.decode_from' ⟨x.val, hx⟩ with
      | .none => .none
      | .some val => .some ⟨val.val, by
        rw [←mem_coe, IsSetLikeLattice.sup_eq_set_sup]
        exact .inr val.property⟩
    else
      match ha.enc.decode_from' ⟨x.val - hb.card, by
        refine Nat.sub_lt_right_of_lt_add ?_ ?_
        apply Nat.le_of_not_lt; assumption
        apply Fin.isLt⟩ with
      | .none => .none
      | .some val => .some ⟨val.val, by
        rw [←mem_coe, IsSetLikeLattice.sup_eq_set_sup]
        exact .inl val.property⟩
  spec_decode_from' := by
    intro ⟨x, hx⟩
    dsimp
    cases hb.decMem x
    dsimp
    rw [dif_neg]
    conv in _ + hb.card - hb.card => { rw [Nat.add_sub_cancel] }
    dsimp
    rw [ha.enc.spec_decode_from']
    apply Nat.not_lt_of_le
    apply Nat.le_add_left
    dsimp
    rw [dif_pos]
    rw [hb.enc.spec_decode_from']
    apply Fin.isLt

instance [DecidableEq β] : DecidableEq (FinSupp α β S default) := by
  intro a b
  apply a.support.lift
  intro ha
  apply b.support.lift
  intro hb
  have := sup_encodable ha hb
  have := Fintype.ofEncodableIntoFin (α := (ha.set ⊔ hb.set: S)) (n := ha.card + hb.card)
  if h:(∀x: (ha.set ⊔ hb.set: S), a.toFun x = b.toFun x) then
    apply Decidable.isTrue
    ext x
    by_cases ha':a x = default
    by_cases hb':b x = default
    rw [ha', hb']
    apply h ⟨x, ?_⟩
    rw [←mem_coe, IsSetLikeLattice.sup_eq_set_sup]
    right
    apply hb.spec
    assumption
    apply h ⟨x, ?_⟩
    rw [←mem_coe, IsSetLikeLattice.sup_eq_set_sup]
    left
    apply ha.spec
    assumption
  else
    apply Decidable.isFalse
    intro g
    subst g
    rw [Classical.not_forall] at h
    obtain ⟨_, _⟩ := h
    contradiction

instance [h: Inhabited S] [he: IsLawfulEmptySetLike S] : Zero (FinSupp α β S default) where
  zero := {
    toFun _:= default
    support := Squash.mk {
      set := h.default
      card := 0
      decMem x := .isFalse fun h => he.elim ⟨_, h⟩
      enc := {
        encode_into := elim_empty
        decode_from' _ := .none
        spec_decode_from' x := elim_empty x
      }
      spec := by intro x h; contradiction
    }
  }

instance [Zero β] [Add β] [IsAddZeroClass β] : Add (FinSupp α β S 0) where
  add a b := {
    toFun x := a x + b x
    support :=
      a.support.lift fun ha =>
      b.support.lift fun hb => Squash.mk {
        set := ha.set ⊔ hb.set
        card := ha.card + hb.card
        decMem x :=
          have := ha.decMem; have := hb.decMem
          decidable_of_iff (x ∈ ha.set ∨ x ∈ hb.set) <| by
            dsimp
            rw [←mem_coe (_ ⊔ _), IsSetLikeLattice.sup_eq_set_sup]
            rfl
        enc := sup_encodable ha hb
        spec := by
          intro x hx
          rw [←mem_coe, IsSetLikeLattice.sup_eq_set_sup]
          by_cases ha':a x = 0
          rw [ha', zero_add] at hx
          right;
          apply hb.spec
          assumption
          left
          apply ha.spec
          assumption
      }
  }
