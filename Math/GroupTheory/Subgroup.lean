import Math.Algebra.Ring
import Math.Data.Set.Lattice
import Math.GroupTheory.Basic

structure Subgroup {α: Type*} (g: Group α) where
  set: Set g
  one_mem: 1 ∈ set
  inv_mem: ∀x ∈ set, x⁻¹ ∈ set
  mul_mem: ∀x y, x ∈ set -> y ∈ set -> x * y ∈ set

namespace Subgroup

variable {α: Type*} {g: Group α}

def opp (a: Subgroup g) : Subgroup g.opp where
  set := a.set
  one_mem := a.one_mem
  inv_mem := a.inv_mem
  mul_mem := by
    intro x y hx hy
    apply a.mul_mem
    assumption
    assumption

inductive Generate (s: Set g) : g -> Prop where
| of : x ∈ s -> Generate s x
| one : Generate s 1
| inv : Generate s a -> Generate s a⁻¹
| mul : Generate s a -> Generate s b -> Generate s (a * b)

def generated (s: Set g) : Subgroup g where
  set := Set.mk (Generate s)
  one_mem := Generate.one
  inv_mem _ := Generate.inv
  mul_mem _ _ := Generate.mul

instance : Bot (Subgroup g) where
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

instance : Top (Subgroup g) where
  top := {
    set := ⊤
    one_mem := True.intro
    inv_mem _ _ := True.intro
    mul_mem _ _ _ _ := True.intro
  }

instance : LE (Subgroup g) where
  le a b := a.set ⊆ b.set

instance : LT (Subgroup g) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : Inf (Subgroup g) where
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

instance : Sup (Subgroup g) where
  sup a b := generated (a.set ∪ b.set)

instance : InfSet (Subgroup g) where
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

instance : SupSet (Subgroup g) where
  sSup s := generated (sSup (s.image Subgroup.set))

instance : IsLawfulLT (Subgroup g) where
  lt_iff_le_and_not_le := Iff.rfl

def orderEmbedSet : Subgroup g ↪o Set α where
  toFun := Subgroup.set
  inj := by
    intro x y eq
    cases x; cases y; congr
  resp_rel := Iff.rfl

def le_generated (a: Subgroup g) {s: Set α} : a.set ⊆ s -> a ≤ generated s := by
  intro h  x hx
  apply Generate.of
  apply h
  assumption

instance : IsPartialOrder (Subgroup g) :=
  orderEmbedSet.inducedIsPartialOrder'

instance : IsLawfulTop (Subgroup g) where
  le_top := by
    intro x
    apply Set.sub_univ

instance : IsLawfulBot (Subgroup g) where
  bot_le := by
    intro g x mem
    cases mem
    apply g.one_mem

instance : IsSemiLatticeSup (Subgroup g) where
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

instance : IsSemiLatticeInf (Subgroup g) where
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

instance : IsLattice (Subgroup g) := Lattice.mk _

instance : IsCompleteSemiLatticeSup (Subgroup g) where
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

instance : IsCompleteSemiLatticeInf (Subgroup g) where
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

instance : IsCompleteLattice (Subgroup g) := IsCompleteLattice.mk _

@[ext]
def ext (a b: Subgroup g) : (∀x, x ∈ a.set ↔ x ∈ b.set) -> a = b:= by
  intro h
  apply orderEmbedSet.inj
  ext
  apply h

scoped instance {g: Subgroup g} : One g.set where
  one := ⟨1, g.one_mem⟩
scoped instance {g: Subgroup g} : Inv g.set where
  inv x := ⟨x.val⁻¹, g.inv_mem _ x.property⟩
scoped instance {g: Subgroup g} : Mul g.set where
  mul x y := ⟨x.val * y.val, g.mul_mem _ _ x.property y.property⟩

scoped instance {g: Subgroup g} : MonoidOps g.set where
  npow := flip npowRec
scoped instance {g: Subgroup g} : GroupOps g.set where
  zpow := flip zpowRec

instance {g: Subgroup g} : IsGroup g.set where
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

def toGroup (A: Subgroup g) : Group A.set where

def image (s: Subgroup g) (h: g →g g') : Subgroup g' where
  set := s.set.image h
  one_mem := by
    apply Set.mem_image.mpr
    exists 1
    apply And.intro
    apply s.one_mem
    rw [resp_one]
  inv_mem := by
    intro _ ⟨x, _, eq⟩; subst eq
    rw [←resp_inv]
    apply Set.mem_image'
    apply s.inv_mem
    assumption
  mul_mem := by
    intro _ _ ⟨x, _,  eqx⟩ ⟨y, _, eqy⟩
    subst eqx eqy
    rw [←resp_mul]
    apply Set.mem_image'
    apply s.mul_mem
    assumption
    assumption

def preimage (s: Subgroup g') (h: g →g g') : Subgroup g where
  set := s.set.preimage h
  one_mem := by
    apply Set.mem_preimage.mpr
    rw [resp_one]
    apply s.one_mem
  inv_mem := by
    intro x hx
    apply Set.mem_preimage.mpr
    rw [resp_inv]
    apply s.inv_mem
    assumption
  mul_mem := by
    intro x y hx hy
    apply Set.mem_preimage.mpr
    rw [resp_mul]
    apply s.mul_mem
    assumption
    assumption

def preimage_preimage (s: Subgroup c) (h: a →g b) (g: b →g c) :
  (s.preimage g).preimage h = s.preimage (g.comp h) := rfl

def commutator (a b: Subgroup g) : Subgroup g :=
  generated <| (Set.zip a.set b.set).image fun ⟨x, y⟩ => x⁻¹ * y⁻¹ * x * y

def cosetLeft (x: g) (a: Subgroup g) : Set α :=
  a.set.image fun y => x * y

def cosetRight (x: g) (a: Subgroup g) : Set α :=
  a.set.image fun y => y * x

def cosetLeft_eq_opp_cosetRight (x: α) (a: Subgroup g) :
  a.cosetLeft x = a.opp.cosetRight (MulOpp.mk x) := rfl

def cosetRight_eq_opp_cosetLeft (x: α) (a: Subgroup g) :
  a.cosetRight x = a.opp.cosetLeft (MulOpp.mk x) := rfl

def cosetLeft.eq_or_disjoint (A: Subgroup g) (x y : g) :
  A.cosetLeft x = A.cosetLeft y ∨ A.cosetLeft x ∩ A.cosetLeft y = ∅ := by
  apply Classical.or_iff_not_imp_right.mpr
  intro h
  have ⟨z, hx, hy⟩ := Set.nonempty_of_not_empty _ h; clear h
  obtain ⟨zx, hzx, eq⟩ := hx; subst eq
  obtain ⟨zy, hzy, eq⟩ := hy
  dsimp at eq
  ext a
  apply Iff.intro
  intro ⟨a, _, eq⟩; subst eq
  dsimp
  rw [←mul_one x, ←mul_inv_cancel zx, ←mul_assoc, eq, mul_assoc y, mul_assoc y]
  apply Set.mem_image'
  apply A.mul_mem
  apply A.mul_mem
  assumption
  apply A.inv_mem
  assumption
  assumption
  intro ⟨a, _, eq⟩; subst eq
  dsimp
  rw [←mul_one y, ←mul_inv_cancel zy, ←mul_assoc, ←eq, mul_assoc x, mul_assoc x]
  apply Set.mem_image'
  apply A.mul_mem
  apply A.mul_mem
  assumption
  apply A.inv_mem
  assumption
  assumption

def cosetRight.eq_or_disjoint (A: Subgroup g) (x y : g) :
  A.cosetRight x = A.cosetRight y ∨ A.cosetRight x ∩ A.cosetRight y = ∅ := by
  simp [cosetRight_eq_opp_cosetLeft]
  apply cosetLeft.eq_or_disjoint

def IsNormal (A: Subgroup g) : Prop :=
  ∀x y: g, y ∈ A.set -> x * y * x⁻¹ ∈ A.set

def IsNormal.inv_left {A: Subgroup g} (h: A.IsNormal) :
  ∀x y: g, y ∈ A.set -> x⁻¹ * y * x ∈ A.set := by
  intro x y ha
  conv => { rhs; rhs; rw [←inv_inv x] }
  apply h
  assumption

def IsNormal.cosetEq {A: Subgroup g} (h: A.IsNormal) : A.cosetLeft = A.cosetRight := by
  ext g a
  apply Iff.intro
  intro ⟨a, ha, eq⟩; subst eq
  apply Set.mem_image.mpr
  refine ⟨?_, ?_, ?_⟩
  exact g * a * g⁻¹
  apply h
  assumption
  rw [mul_assoc, inv_mul_cancel, mul_one]
  intro ⟨a, ha, eq⟩; subst eq
  apply Set.mem_image.mpr
  refine ⟨?_, ?_, ?_⟩
  exact g⁻¹ * a * g
  apply h.inv_left
  assumption
  rw [←mul_assoc, ←mul_assoc, mul_inv_cancel, one_mul]

def cosetLeft.setoid (A: Subgroup g) : Setoid g where
  r x y := A.cosetLeft x = A.cosetLeft y
  iseqv := {
    refl := by
      intro x
      rfl
    symm := by
      intro a b eq
      rw [eq]
    trans := by
      intro a b c ab bc
      rw [ab, bc]
  }

def cosetRight.setoid (A: Subgroup g) : Setoid g where
  r x y := A.cosetRight x = A.cosetRight y
  iseqv := {
    refl := by
      intro x
      rfl
    symm := by
      intro a b eq
      rw [eq]
    trans := by
      intro a b c ab bc
      rw [ab, bc]
  }

def rep_mem_cosetLeft {x: g} {A: Subgroup g} : x ∈ A.cosetLeft x := by
  refine ⟨1, A.one_mem, ?_⟩
  dsimp; rw [mul_one]

def IsNormal.setoid {A: Subgroup g} (_: A.IsNormal) : Setoid g :=
  cosetLeft.setoid A

def IsNormal.QuotType {A: Subgroup g} (h: A.IsNormal) := Quotient h.setoid

section

variable {A: Subgroup g} (h: A.IsNormal)

instance : One h.QuotType where
  one := .mk _ 1

instance : Inv h.QuotType where
  inv := by
    apply Quotient.lift (fun x => Quotient.mk _ (x⁻¹))
    intro a b eq
    apply Quotient.sound
    apply (cosetLeft.eq_or_disjoint _ _ _).resolve_right
    intro h'
    have ⟨a', a'_mem, eq⟩ : a ∈ cosetLeft b A := by
      rw [←eq]
      exact rep_mem_cosetLeft
    have : a⁻¹ ∈ cosetLeft b⁻¹ A := by
      subst eq
      dsimp at h'
      refine ⟨?_, ?_, ?_⟩
      exact b * a'⁻¹ * b⁻¹
      apply h
      apply A.inv_mem
      assumption
      rw [inv_mul_rev]
      dsimp
      rw [←mul_assoc, ←mul_assoc, inv_mul_cancel, one_mul]
    have : a⁻¹ ∈ cosetLeft a⁻¹ A ∩ cosetLeft b⁻¹ A := ⟨rep_mem_cosetLeft, this⟩
    rw [h'] at this
    contradiction

instance : Mul h.QuotType where
  mul := by
    apply Quotient.lift₂ (fun a b => Quotient.mk _ (a * b))
    intro a b c d ac bd
    apply Quotient.sound
    apply (cosetLeft.eq_or_disjoint _ _ _).resolve_right
    intro h'
    have ⟨a', mema', ha⟩ : a ∈ A.cosetLeft c := by
      rw [←ac]; exact rep_mem_cosetLeft
    have ⟨b', memb', hb⟩  : b ∈ A.cosetLeft d := by
      rw [←bd]; exact rep_mem_cosetLeft
    have : a * b ∈ A.cosetLeft (c * d) := by
      subst ha hb
      dsimp
      refine ⟨?_, ?_, ?_⟩
      exact (d⁻¹ * a' * d) * b'
      apply A.mul_mem
      apply h.inv_left
      assumption
      assumption
      dsimp
      rw [mul_assoc c d, mul_assoc d⁻¹, mul_assoc d⁻¹, ←mul_assoc d d⁻¹,
        mul_inv_cancel, one_mul, ←mul_assoc, ←mul_assoc, ←mul_assoc]
    have : a * b ∈ A.cosetLeft (a * b) ∩ A.cosetLeft (c * d) :=
      ⟨rep_mem_cosetLeft, this⟩
    rw [h'] at this
    contradiction

end

def IsNormal.Quot {A: Subgroup g} (h: A.IsNormal) : Group h.QuotType := by
  apply Group.ofAxiomsLeft
  · intro x
    induction x using Quot.ind with | mk x =>
    apply Quotient.sound
    rw [one_mul]
    rfl
  · intro x
    induction x using Quot.ind with | mk x =>
    apply Quotient.sound
    rw [inv_mul_cancel]
    rfl
  · intro a b c
    induction a using Quot.ind with | mk a =>
    induction b using Quot.ind with | mk b =>
    induction c using Quot.ind with | mk c =>
    apply Quotient.sound
    rw [mul_assoc]
    rfl

def IsNormal.preimage {A: Subgroup g} (h: A.IsNormal) (f: g' →g g) :
  (A.preimage f).IsNormal := by
  intro x y hy
  apply Set.mem_preimage.mpr
  rw [resp_mul, resp_mul, resp_inv]
  apply h
  assumption

def IsNormal.image {A: Subgroup g} (h: A.IsNormal) (f: g →g g') (hf: Function.Surjective f):
  (A.image f).IsNormal := by
  intro x y ⟨y, hy, eq⟩; subst eq
  have := fun x => h x y hy
  obtain ⟨x, eq⟩ := hf x; subst eq
  rw [←resp_inv, ←resp_mul, ←resp_mul]
  apply Set.mem_image'
  apply h
  assumption

end Subgroup

namespace Group

-- the only normal subgroups of a simple group are
-- the trivial group, and the entire group
def IsSimple (g: Group α) :=
  ∀s: Subgroup g, s.IsNormal -> s = ⊤ ∨ s = ⊥

-- simple groups respect the isomorphsim relation
def IsSimple.congr (g: Group α) (h: g ≃g g'):
  g.IsSimple -> g'.IsSimple := by
  intro g_simp s n
  cases g_simp _ (n.preimage h.toHom) <;> rename_i hs
  · left
    ext x
    apply Iff.intro
    intro
    trivial
    intro
    have : (s.preimage h.toHom).preimage h.symm.toHom = (⊤: Subgroup g).preimage h.symm.toHom := by rw [hs]
    rw [Subgroup.preimage_preimage, Equiv.toHom_comp_toHom, h.symm_trans] at this
    replace this : s = _ := this
    rw [this]
    trivial
  · right
    ext x
    apply Iff.intro
    intro hx
    have : (s.preimage h.toHom).preimage h.symm.toHom = (⊥: Subgroup g).preimage h.symm.toHom := by rw [hs]
    rw [Subgroup.preimage_preimage, Equiv.toHom_comp_toHom, h.symm_trans] at this
    replace this : s = _ := this
    rw [this] at hx
    replace hx: h.symm x = 1 := hx
    rw [←h.coe_symm 1, resp_one,] at hx
    rw [h.invFun_inj hx]
    rfl
    intro
    subst x
    apply s.one_mem

end Group
