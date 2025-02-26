import Math.Tactics.PPWithUniv
import Math.Logic.Equiv.Basic
import Math.Type.Notation

-- a type is `u` small if there exists an equivalent type in `Type u`
@[pp_with_univ]
class Small.{u, v} (α: Type v): Prop where
  exists_equiv: ∃β: Type u, Nonempty (α ≃ β)

def Shrink (α: Type v) [h: Small.{u} α] : Type u := Classical.choose h.exists_equiv
noncomputable def Shrink.spec (α: Type v) [h: Small.{u} α] : α ≃ Shrink α := Classical.choice (Classical.choose_spec h.exists_equiv)

def Small.map [g: Small.{u} α] (h: α ≃ β) : Small.{u} β where
  exists_equiv :=
    have ⟨α₀, ⟨eqv⟩⟩ := g.exists_equiv
    ⟨α₀, ⟨h.symm.trans eqv⟩⟩

def Small.lift [g: Small.{u} α] : Small.{u} (ULift.{v} α) :=
  Small.map (Equiv.ulift _).symm

def Small.down [g: Small.{u} (ULift α)] : Small.{u} α :=
  Small.map (Equiv.ulift _)

instance (priority := 1001) Small.refl (α: Type u) : Small.{u, u} α where
  exists_equiv := ⟨α, ⟨Equiv.rfl⟩⟩
instance {α: Type} : Small.{u, 0} α := @Small.down α (Small.refl (ULift.{u} α))
instance {α: Type u} : Small.{u+1} α := @Small.down α (Small.refl (ULift.{u+1} α))
instance {α: Type u} : Small.{u, max v u} (ULift α) := Small.lift.{u}
instance : Small.{max v (u + 1)} (Type u) := @Small.down (Type u) (Small.refl _)

@[ext]
def Shrink.ext {α : Type v} [Small.{w} α] {x y : Shrink α}
  (w : (spec _).symm x = (spec _).symm y) : x = y := (spec α).symm.inj w

@[induction_eliminator, elab_as_elim]
protected noncomputable def Shrink.rec {α : Type*} [Small.{w} α] {F : Shrink α → Sort v}
    (h : ∀ X, F (spec _ X)) : ∀ X, F X :=
  fun X => cast (α := F (spec _ ((spec _).symm X))) (by rw [Equiv.symm_coe]) (h _)

instance {α: Type*} {β: α -> Type*} [ha: Small.{u} α] [hb: ∀a: α, Small.{u} (β a)] : Small.{u} (Σa: α, β a) where
  exists_equiv := by
    let β₀: Shrink α -> Type u := fun a: Shrink α => Shrink (β ((Shrink.spec α).symm a))
    refine ⟨Σa: Shrink α, β₀ a, ⟨?_⟩⟩
    apply Equiv.congrSigma (Shrink.spec α)
    rintro x
    apply (Shrink.spec (β x)).trans
    show Shrink _ ≃ Shrink (β _)
    show Shrink _ ≃ Shrink (β ((Shrink.spec α).symm ((Shrink.spec α) x)))
    rw [Equiv.coe_symm]

instance {α: Type*} {β: α -> Type*} [ha: Small.{u} α] [hb: ∀a: α, Small.{u} (β a)] : Small.{u} (∀a: α, β a) where
  exists_equiv := by
    let β₀: Shrink α -> Type u := fun a: Shrink α => Shrink (β ((Shrink.spec α).symm a))
    refine ⟨∀a: Shrink α, β₀ a, ⟨?_⟩⟩
    apply Equiv.congrPi (Shrink.spec α)
    intro x
    apply (Shrink.spec (β x)).trans
    show Shrink _ ≃ Shrink (β _)
    show Shrink _ ≃ Shrink (β ((Shrink.spec α).symm ((Shrink.spec α) x)))
    rw [Equiv.coe_symm]
