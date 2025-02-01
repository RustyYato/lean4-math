import Math.Algebra.Ring
import Math.Data.Set.Lattice

structure Subgroup (α: Type*) [GroupOps α] [IsGroup α] where
  set: Set α
  one_mem: 1 ∈ set
  inv_mem: ∀x ∈ set, x⁻¹ ∈ set
  mul_mem: ∀x y, x ∈ set -> y ∈ set -> x * y ∈ set

namespace Subgroup

variable {α: Type*} [GroupOps α] [IsGroup α]

inductive Generate (s: Set α) : α -> Prop where
| of : x ∈ s -> Generate s x
| one : Generate s 1
| inv : Generate s a -> Generate s a⁻¹
| mul : Generate s a -> Generate s b -> Generate s (a * b)

def generated (s: Set α) : Subgroup α where
  set := Set.mk (Generate s)
  one_mem := Generate.one
  inv_mem _ := Generate.inv
  mul_mem _ _ := Generate.mul

instance : Bot (Subgroup α) where
  bot := {
    set := {1}
    one_mem := rfl
    inv_mem a amem := by
      subst a
      rw [inv_one]
      rfl
    mul_mem a b amem bmem := by
      subst a; subst b
      rw [mul_one]
      rfl
  }

instance : Top (Subgroup α) where
  top := {
    set := ⊤
    one_mem := True.intro
    inv_mem _ _ := True.intro
    mul_mem _ _ _ _ := True.intro
  }

instance : LE (Subgroup α) where
  le a b := a.set ⊆ b.set

instance : LT (Subgroup α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : Inf (Subgroup α) where
  inf a b := {
    set := a.set ∩ b.set
    one_mem := ⟨a.one_mem, b.one_mem⟩
    inv_mem := by
      intro x ⟨ha, hb⟩
      exact ⟨a.inv_mem _ ha, b.inv_mem _ hb⟩
    mul_mem := by
      intro x y ⟨hax, hbx⟩ ⟨hay, hby⟩
      exact ⟨a.mul_mem _ _ hax hay, b.mul_mem _ _ hbx hby⟩
  }

instance : Sup (Subgroup α) where
  sup a b := generated (a.set ∪ b.set)

instance : InfSet (Subgroup α) where
  sInf s := {
    set := sInf (s.image Subgroup.set)
    one_mem := by
      apply Set.mem_sInter.mpr
      intro x ⟨x, _, eq⟩; subst eq
      apply x.one_mem
    inv_mem x hx := by
      intro y ⟨y, _, eq⟩; subst eq
      apply Subgroup.inv_mem
      apply hx
      apply Set.mem_image'
      assumption
    mul_mem a b ha hb := by
      intro x ⟨x, _, eq⟩; subst eq
      apply Subgroup.mul_mem
      apply ha
      apply Set.mem_image'
      assumption
      apply hb
      apply Set.mem_image'
      assumption
  }

instance : SupSet (Subgroup α) where
  sSup s := generated (sSup (s.image Subgroup.set))

instance : IsLawfulLT (Subgroup α) where
  lt_iff_le_and_not_le := Iff.rfl

def orderEmbedSet : Subgroup α ↪o Set α where
  toFun := Subgroup.set
  inj := by
    intro x y eq
    cases x; cases y; congr
  resp_rel := Iff.rfl

def le_generated (a: Subgroup α) {s: Set α} : a.set ⊆ s -> a ≤ generated s := by
  intro h  x hx
  apply Generate.of
  apply h
  assumption

instance : IsPartialOrder (Subgroup α) :=
  orderEmbedSet.inducedIsPartialOrder'

instance : IsLawfulTop (Subgroup α) where
  le_top := by
    intro x
    apply Set.sub_univ

instance : IsLawfulBot (Subgroup α) where
  bot_le := by
    intro g x mem
    cases mem
    apply g.one_mem

instance : IsSemiLatticeSup (Subgroup α) where
  le_sup_left := by
    intro x y
    apply le_generated
    apply Set.sub_union_left
  le_sup_right := by
    intro x y
    apply le_generated
    apply Set.sub_union_right
  sup_le := by
    intro a b k ak bk x hx
    induction hx with
    | of h =>
      cases h
      apply ak; assumption
      apply bk; assumption
    | one => apply k.one_mem
    | inv => apply k.inv_mem; assumption
    | mul => apply k.mul_mem <;> assumption

instance : IsSemiLatticeInf (Subgroup α) where
  inf_le_left := by
    intro x y
    apply Set.inter_sub_left
  inf_le_right := by
    intro x y
    apply Set.inter_sub_right
  le_inf := by
    intro x y k kx ky a ha
    apply And.intro
    apply kx; apply ha
    apply ky; apply ha

instance : IsLattice (Subgroup α) := Lattice.mk _

instance : IsCompleteSemiLatticeSup (Subgroup α) where
  le_sSup := by
    intro U s hs x hx
    apply Generate.of
    apply Set.mem_sUnion.mpr
    exists s.set
    apply And.intro
    apply Set.mem_image'
    assumption
    assumption
  sSup_le := by
    intro  U s hs x hx
    induction hx with
    | of h =>
      obtain ⟨_, ⟨s', s'_mem, eq⟩ , x_in_s'⟩ := h; subst eq
      apply hs
      assumption
      assumption
    | one => apply Subgroup.one_mem
    | inv => apply Subgroup.inv_mem; assumption
    | mul => apply Subgroup.mul_mem <;> assumption

instance : IsCompleteSemiLatticeInf (Subgroup α) where
  sInf_le := by
    intro U s hs x hx
    apply hx
    apply Set.mem_image'
    assumption
  le_sInf := by
    intro U s hs x hx y ⟨y, _, eq⟩
    subst eq
    apply hs
    assumption
    assumption

instance : IsCompleteLattice (Subgroup α) := IsCompleteLattice.mk _

scoped instance {g: Subgroup α} : One g.set where
  one := ⟨1, g.one_mem⟩
scoped instance {g: Subgroup α} : Inv g.set where
  inv x := ⟨x.val⁻¹, g.inv_mem _ x.property⟩
scoped instance {g: Subgroup α} : Mul g.set where
  mul x y := ⟨x.val * y.val, g.mul_mem _ _ x.property y.property⟩

scoped instance {g: Subgroup α} : MonoidOps g.set where
  npow := flip npowRec
scoped instance {g: Subgroup α} : GroupOps g.set where
  zpow := flip zpowRec

instance {g: Subgroup α} : IsGroup g.set where
  mul_assoc a b c := by
    apply Subtype.val_inj
    apply mul_assoc
  one_mul a := by
    apply Subtype.val_inj
    apply one_mul
  mul_one a := by
    apply Subtype.val_inj
    apply mul_one
  inv_mul_cancel a := by
    apply Subtype.val_inj
    apply inv_mul_cancel
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl

end Subgroup
