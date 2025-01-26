import Math.Data.Zf.Basic
import Math.Order.Linear
import Math.Order.OrderIso
import Math.Relation.RelIso

open ZfSet

structure ZfSet.IsOrdinal (set: ZfSet): Prop where
  trans: ∀{x}, x ∈ set -> x ⊆ set
  total: ∀{x y}, x ∈ set -> y ∈ set -> x ∈ y ∨ x = y ∨ y ∈ x

def ZfSet.IsOrdinal.ofEquiv.{u, v} (a: ZfSet.{u}) (b: ZfSet.{v}) (hab: a zf= b) (g: a.IsOrdinal): b.IsOrdinal where
  trans := by
    intro x hxa z hzx
    replace hxb : b.mem x := hxa
    replace hzx : x.mem z := hzx
    have hxa := hxb.congr hab.symm .refl
    rw [ZfSet.mem.spec] at hxa
    obtain ⟨a', a'_in_a, a'_eqv_x⟩ := hxa
    have := ZfSet.sub.ofSubset (g.trans a'_in_a) z (hzx.congr a'_eqv_x.symm .refl)
    exact this.congr hab .refl
  total := by
    intro x y hxb hyb
    have ⟨x₀, x₀_in_a, x₀_eqv_x⟩ := ZfSet.mem.spec.mp <| hxb.congr hab.symm .refl
    have ⟨y₀, y₀_in_a, y₀_eqv_y⟩ := ZfSet.mem.spec.mp <| hyb.congr hab.symm .refl
    rcases g.total x₀_in_a y₀_in_a with lt | eq | gt
    left; apply lt.congr <;> assumption
    right; left
    apply eq_of_eqv
    apply x₀_eqv_x.symm.trans
    rw [eq]
    assumption
    right; right; apply gt.congr <;> assumption

@[pp_with_univ]
structure Ordinal where
  ofZfSet ::
  set: ZfSet
  trans: ∀{x}, x ∈ set -> x ⊆ set
  total: ∀{x y}, x ∈ set -> y ∈ set -> x ∈ y ∨ x = y ∨ y ∈ x

namespace Ordinal

abbrev mk (h: ZfSet.IsOrdinal s): Ordinal where
  set := s
  trans := h.trans
  total := h.total

def toIsOrdinal (o: Ordinal): IsOrdinal o.set where
  trans := o.trans
  total := o.total

instance : LE Ordinal where
  le a b := a.set ⊆ b.set

instance : LT Ordinal where
  lt a b := a.set ∈ b.set

def embedZfSet : @RelEmbedding Ordinal ZfSet (· < ·) (· ∈ ·) where
  toFun x := x.set
  inj := by
    intro x y eq; cases x; cases y; congr
  resp_rel := Iff.rfl

attribute [coe] Ordinal.set

instance : Coe Ordinal ZfSet where
  coe := Ordinal.set

instance : @Relation.IsWellFounded Ordinal (· < ·) :=
  embedZfSet.toRelHom.wf

instance : WellFoundedRelation Ordinal where
  rel a b := a < b
  wf := Relation.wellFounded _

def succ (o: Ordinal) : Ordinal where
  set := insert o.set o.set
  trans := by
    intro x mem
    rw [mem_insert] at mem
    cases mem
    subst x
    intro x mem
    rw [mem_insert]
    right; assumption
    intro y mem
    rw [mem_insert]; right
    apply o.trans
    assumption
    assumption
  total := by
    intro x y hx hy
    rw [mem_insert] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    subst x; subst y
    right; left; rfl
    subst x; right; right; assumption
    subst y; left; assumption
    rcases o.total hx hy with xy | eq | yx
    left; assumption
    right; left; assumption
    right; right; assumption

def lt_succ_self (o: Ordinal) : o < o.succ := mem_insert.mpr (.inl rfl)

def min' (a b: Ordinal) : Ordinal where
  set := a.set ∩ b.set
  trans := by
    intro x h y yx
    rw [mem_inter] at *
    exact ⟨a.trans h.left _ yx, b.trans h.right _ yx⟩
  total := by
    intro x y hx hy
    rw [mem_inter] at hx hy
    apply a.total
    exact hx.left
    exact hy.left

instance : Min Ordinal := ⟨min'⟩

def min_le_left' (a b: Ordinal) : min a b ≤ a := by
  intro x mem
  exact (mem_inter.mp mem).left

def min_le_right' (a b: Ordinal) : min a b ≤ b := by
  intro x mem
  exact (mem_inter.mp mem).right

def mem_set {a: ZfSet} (b: Ordinal) (ha: a ∈ b.set) : a.IsOrdinal where
  trans := by
    intro x hxa y hy
    have hx := b.trans ha _ hxa
    have hyb := b.trans hx _ hy
    rcases b.total ha hyb with hay | eq | hyb
    have := Relation.irrefl (rel := Relation.TransGen (· ∈ ·)) (Relation.TransGen.tail (.tail (.single hxa) hay) hy)
    contradiction
    subst y
    have := Relation.asymm (rel := (· ∈ ·)) hxa hy
    contradiction
    assumption
  total := by
    intro x y hx hy
    apply b.total
    all_goals apply b.trans <;> assumption

def _root_.ZfSet.IsOrdinal.ofMem.{u,v} (a: ZfSet.{u}) (b: ZfSet.{v}) (hab: b.mem a) (g: b.IsOrdinal): a.IsOrdinal := by
  rw [mem.spec] at hab
  obtain ⟨b', b'_in_b, b'_eqv_a⟩ := hab
  exact (mem_set (.mk g) b'_in_b).ofEquiv _ _ b'_eqv_a

def lt_of_le_of_not_le' (B A: Ordinal) : B ≤ A -> ¬A ≤ B -> B < A := by
  intro BA AB
  have ⟨x, h⟩ := Classical.not_forall.mp AB
  rw [not_imp] at h
  obtain ⟨hb, ha⟩ := h
  let S := A.set.toSet \ B.set.toSet
  have : S.Nonempty := ⟨_, hb, ha⟩
  clear hb ha x
  let x := Set.min (· ∈ ·) this
  let x_mem: x ∈ S := Set.min_mem (· ∈ ·) this
  obtain ⟨hxa, hnxb⟩ := x_mem
  let x_spec: ∀y ∈ S, ¬y ∈ x := Set.not_lt_min (· ∈ ·) this
  have x_sub_A: x ⊆ A := A.trans hxa
  have : ∅ = (A.set \ B) ∩ x -> x ⊆ B := by
    intro h
    have : toSet ∅ = toSet ((A.set \ B) ∩ x) := by rw [h]
    rw [
      toSet_inter,
      toSet_sdiff,
      Set.sdiff_eq_inter_compl, Set.inter_assoc, Set.inter_comm _ x.toSet,
      ←Set.inter_assoc,
      ←Set.sdiff_eq_inter_compl, Set.inter_of_sub_right,
      ←toSet_sdiff] at this
    replace this := toSet_inj this
    intro z hzx
    apply Classical.byContradiction
    intro hzb
    have hz : z ∈ x \ B := by
      rw [mem_sdiff]
      trivial
    rw [←this] at hz
    exact not_mem_empty _ hz
    assumption
  replace x_sub_B := this <| by
    ext z
    apply Iff.intro
    intro h; exact (not_mem_empty _ h).elim
    intro h
    rw [mem_inter, mem_sdiff] at h
    have := x_spec z ⟨h.left.left, h.left.right⟩ h.right
    contradiction
  have B_sub_x : B.set ⊆ x := by
    intro z hz
    have hza := BA _ hz
    rcases A.total hxa hza with hzx | eq | hxz
    have := B.trans hz _ hzx
    contradiction
    subst z
    contradiction
    assumption
  have := sub_antisym x_sub_B B_sub_x
  show B.set ∈ A.set
  rw [←this]
  assumption

instance : IsPartialOrder Ordinal where
  le_refl _ := ZfSet.sub_refl _
  le_trans := ZfSet.sub_trans
  le_antisymm := by
    intro a b ab ba
    apply embedZfSet.inj
    apply ZfSet.sub_antisym
    assumption
    assumption
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    intro h
    apply And.intro
    apply b.trans
    assumption
    intro g
    have := embedZfSet.inj <| ZfSet.sub_antisym (b.trans h) g
    rw [←this] at h
    exact Relation.IsIrrefl.irrefl h
    intro ⟨h, g⟩
    apply lt_of_le_of_not_le' <;> assumption

def le_total' (a b: Ordinal) : a ≤ b ∨ b ≤ a := by
  apply Classical.byContradiction
  rw [not_or]
  intro ⟨hab, hba⟩
  have ha : min a b ≤ a := min_le_left' a b
  have hb : min a b ≤ b := min_le_right' a b
  have min_lt_a  : min a b < a := lt_of_le_of_ne ha <| by
    intro h
    rw [h] at hb; contradiction
  have min_lt_b  : min a b < b := lt_of_le_of_ne hb <| by
    intro h
    rw [h] at ha; contradiction
  exact Relation.irrefl (rel := (· ∈ ·)) (mem_inter.mpr ⟨min_lt_a, min_lt_b⟩)

instance : IsLinearOrder Ordinal where
  le_antisymm := le_antisymm
  le_trans := le_trans
  lt_or_le := by
    intro a b
    rcases le_total' a b with h | h
    rcases lt_or_eq_of_le h with h | h
    left; assumption
    right; rw [h]
    right; assumption

def total' {a b: ZfSet} (ha: a.IsOrdinal) (hb: b.IsOrdinal) :
  a ∈ b ∨ a = b ∨ b ∈ a := by
  rcases lt_trichotomy (Ordinal.mk ha) (Ordinal.mk hb) with lt | eq | gt
  left; assumption
  right; left; apply Ordinal.ofZfSet.inj eq
  right; right; assumption

def max' (a b: Ordinal) : Ordinal where
  set := a.set ∪ b.set
  trans := by
    intro x h y yx
    rw [mem_union] at *
    cases h
    left
    apply a.trans
    assumption
    assumption
    right
    apply b.trans
    assumption
    assumption
  total := by
    intro x y hx hy
    rw [mem_union] at hx hy
    apply total'
    rcases hx with hx | hx
    apply a.mem_set
    assumption
    apply b.mem_set
    assumption
    rcases hy with hy | hy
    apply a.mem_set
    assumption
    apply b.mem_set
    assumption

instance : Max Ordinal := ⟨max'⟩

instance : IsLinearMinMaxOrder Ordinal where
  min_iff_le_left := by
    intro a b
    apply Iff.intro
    intro h
    apply embedZfSet.inj
    show a.set ∩ b.set = a.set
    apply toSet_inj
    rw [toSet_inter, Set.inter_of_sub_left]
    assumption
    intro h
    rw [←h]
    apply inter_sub_right
  min_iff_le_right := by
    intro a b
    apply Iff.intro
    intro h
    apply embedZfSet.inj
    show a.set ∩ b.set = b.set
    apply toSet_inj
    rw [toSet_inter, Set.inter_of_sub_right]
    assumption
    intro h
    rw [←h]
    apply inter_sub_left
  max_iff_le_left := by
    intro a b
    apply Iff.intro
    intro h
    apply embedZfSet.inj
    show a.set ∪ b.set = b.set
    apply toSet_inj
    rw [toSet_union, Set.union_of_sub_left]
    assumption
    intro h
    rw [←h]
    apply left_sub_union
  max_iff_le_right := by
    intro a b
    apply Iff.intro
    intro h
    apply embedZfSet.inj
    show a.set ∪ b.set = a.set
    apply toSet_inj
    rw [toSet_union, Set.union_of_sub_right]
    assumption
    intro h
    rw [←h]
    apply right_sub_union

def zero : Ordinal where
  set := ∅
  trans := by
    intro _ h; exact (not_mem_empty _ h).elim
  total := by
    intro _ _ h; exact (not_mem_empty _ h).elim

def ofNat (n: Nat) : Ordinal where
  set := .ofNat n
  trans := by
    intro x hx y hy
    rw [mem_ofNat] at hx
    obtain ⟨x, xLt, eq⟩ := hx; subst eq
    rw [mem_ofNat] at hy
    obtain ⟨y, yLt, eq⟩ := hy; subst eq
    rw [mem_ofNat]
    refine ⟨y, ?_, rfl⟩
    apply Nat.lt_trans <;> assumption
  total := by
    intro x y hx hy
    rw [mem_ofNat] at hx hy
    obtain ⟨x, xLt, eq⟩ := hx; subst eq
    obtain ⟨y, yLt, eq⟩ := hy; subst eq
    rw [ofNat_mem_ofNat, ofNat_mem_ofNat, ofNat_inj]
    apply Nat.lt_trichotomy

def lift (o: Ordinal.{u}): Ordinal.{max u v} where
  set := o.set.lift
  trans := by
    intro x hxo
    rw [mem_lift, mem.spec] at hxo
    obtain ⟨o', o'_in_o, o'_eqv_x⟩ := hxo
    rw [sub_lift]
    intro y hy
    have := (hy.congr o'_eqv_x.symm .refl)
    exact sub.ofSubset (o.trans o'_in_o) _ this
  total := by
    intro x y memx memy
    rw [mem_lift] at memx memy
    have hx := IsOrdinal.ofMem _ _ memx o.toIsOrdinal
    have hy := IsOrdinal.ofMem _ _ memy o.toIsOrdinal
    apply total'
    assumption
    assumption

instance : OfNat Ordinal.{u} n := ⟨ofNat n⟩

def zero_le (o: Ordinal) : 0 ≤ o := empty_sub _

def IsLimit (o: Ordinal) : Prop := ∀x: Ordinal, o ≠ x.succ
def IsSuccLimit (o: Ordinal) : Prop := 0 < o ∧ o.IsLimit
def IsLimit.zero : IsLimit 0 := by
  intro x h
  have := lt_succ_self x
  rw [←h] at this
  have := not_lt_of_le (zero_le x)
  contradiction

protected def sSup.{u} (s: ZfSet.{u}) (h: ∀x ∈ s, IsOrdinal x) : Ordinal where
  set := ⋃ s
  trans := by
    intro x hx y hy
    rw [mem_sUnion] at *
    obtain ⟨s', hs', x_in_s'⟩ := hx
    have := (h _ hs').trans x_in_s' _ hy
    exists s'
  total := by
    intro x y hx hy
    rw [mem_sUnion] at hx hy
    apply total'
    obtain ⟨s', hs', hx⟩ := hx
    apply mem_set (.mk _) hx
    apply h
    assumption
    obtain ⟨s', hs', hy⟩ := hy
    apply mem_set (.mk _) hy
    apply h
    assumption

protected def sInf.{u} (s: ZfSet.{u}) (sne: s.Nonempty) (h: ∀x ∈ s, IsOrdinal x) : Ordinal where
  set := ⋂ s
  trans := by
    intro x hx
    rw [mem_sInter] at hx
    intro y hy
    rw [mem_sInter]
    intro z hz
    have x_in_z := hx z hz
    apply (h _ hz).trans
    assumption
    assumption
    assumption
    assumption
  total := by
    intro x y hx hy
    have ⟨z, z_in_s⟩ := sne
    rw [mem_sInter] at hx hy
    apply total'
    apply mem_set (.mk _) <| hx z _
    apply h; assumption
    assumption
    apply mem_set (.mk _) <| hy z _
    apply h; assumption
    assumption
    assumption
    assumption

def mem_le_sSup (s: ZfSet) {hs: ∀x ∈ s, IsOrdinal x} (x: Ordinal) (h: x.set ∈ s) : x ≤ Ordinal.sSup s hs := by
  intro z hx
  unfold Ordinal.sSup
  rw [mem_sUnion]
  exists x

def sSup_le (s: ZfSet) {hs: ∀x ∈ s, IsOrdinal x} (k: Ordinal) (h: ∀x ∈ s, x ⊆ k.set) : Ordinal.sSup s hs ≤ k := by
  intro x hz
  erw [mem_sUnion] at hz
  obtain ⟨s', s'_in_s, x_in_s'⟩ := hz
  apply h
  assumption
  assumption

def sInf_le_mem (s: ZfSet) {hs: ∀x ∈ s, IsOrdinal x} (x: Ordinal) (h: x.set ∈ s) : Ordinal.sInf s ⟨_, h⟩ hs ≤ x := by
  intro z hz
  unfold Ordinal.sInf at hz
  rw [mem_sInter] at hz
  apply hz
  assumption
  exact ⟨_, h⟩

def le_sInf (s: ZfSet) (h: s.Nonempty) {hs: ∀x ∈ s, IsOrdinal x} (k: Ordinal) (g: ∀x ∈ s, k.set ⊆ x) : k ≤ Ordinal.sInf s h hs := by
  intro x memk
  erw [mem_sInter h]
  intro s' hs'
  have s'_ord := hs _ hs'
  exact g _ hs' _ memk

protected noncomputable def iSup (f: ι -> Ordinal) : Ordinal :=
  Ordinal.sSup (ZfSet.range (fun x => (f x).set)) <| by
    intro x mem
    rw [mem_range] at mem
    obtain ⟨i, eq⟩ := mem
    subst x
    apply Ordinal.toIsOrdinal

def omega : Ordinal where
  set := .omega
  trans := by
    intro x hx y hy
    rw [mem_omega] at hx; obtain ⟨n, eq⟩ := hx; subst eq
    rw [mem_ofNat] at hy; obtain ⟨m, _, eq⟩ := hy; subst eq
    exact ofNat_mem_omega
  total := by
    intro x y hx hy
    rw [mem_omega] at hx hy
    obtain ⟨x, eq⟩ := hx; subst eq
    obtain ⟨y, eq⟩ := hy; subst eq
    rw [ofNat_mem_ofNat, ofNat_mem_ofNat, ofNat_inj]
    apply Nat.lt_trichotomy

scoped notation "ω" => omega

def lt_omega : ∀{x}, x < ω ↔ ∃n, x = ofNat n := by
  intro x
  apply Iff.intro
  intro h
  replace h: x.set ∈ omega.set := h
  erw [ZfSet.mem_omega] at h
  obtain ⟨n, eq⟩ := h
  exists n
  apply embedZfSet.inj
  assumption
  intro ⟨n, eq⟩
  rw [eq]
  apply ofNat_mem_omega

def ofNat_lt_omega : ofNat n < omega := ofNat_mem_omega

def IsSuccLimit.omega : IsSuccLimit ω := by
  apply And.intro ofNat_lt_omega
  intro x h
  have := lt_succ_self x
  rw [←h] at this
  rw [lt_omega] at this
  obtain ⟨n, eq⟩ := this
  subst x
  replace h: ω = ofNat (n + 1) := h
  have : ofNat (n + 2) < ω := lt_omega.mpr ⟨_, rfl⟩
  rw [h] at this
  exact lt_asymm (lt_succ_self (ofNat (n + 1))) this

def IsLimit.omega : IsLimit ω := IsSuccLimit.omega.right

def not_between_succ {a b: Ordinal} : b < a -> a < b.succ -> False := by
  intro ba abs
  have : a.set ∈ insert b.set b.set := abs
  rw [mem_insert] at this
  rcases this with h | h
  cases embedZfSet.inj h
  exact lt_irrefl ba
  exact lt_asymm ba h

def le_of_lt_succ {a b: Ordinal} : a < b.succ -> a ≤ b := by
  intro h x hx
  have xord := mem_set _ hx
  let x' := mk xord
  have : x ∈ insert _ _ := lt_trans (a := x') hx h
  rw [mem_insert] at this
  cases this
  subst x
  have := not_between_succ hx h
  contradiction
  assumption

def lt_succ_of_le {a b: Ordinal} : a ≤ b -> a < b.succ := by
  intro h
  apply lt_of_le_of_lt h
  apply lt_succ_self

def lt_succ {a b: Ordinal} : a < b.succ ↔ a ≤ b := by
  apply Iff.intro
  apply le_of_lt_succ
  apply lt_succ_of_le

def succ_le_of_lt {a b: Ordinal} : a < b -> a.succ ≤ b := by
  intro h x mem
  rw [succ, mem_insert] at mem
  cases mem; subst x
  assumption
  apply b.trans
  assumption
  assumption

def lt_of_succ_le {a b: Ordinal} : a.succ ≤ b -> a < b := by
  intro h
  apply lt_of_not_le
  intro g
  exact not_lt_of_le (le_trans h g) (lt_succ_self _)

def succ_le {a b: Ordinal} : a.succ ≤ b ↔ a < b := by
  apply Iff.intro
  apply lt_of_succ_le
  apply succ_le_of_lt

def succ_lt_succ {a b: Ordinal} : a < b ↔ a.succ < b.succ := by
  rw [lt_succ, succ_le]
def succ_le_succ {a b: Ordinal} : a ≤ b ↔ a.succ ≤ b.succ := by
  rw [succ_le, lt_succ]

def succ.inj : Function.Injective succ := by
  intro a b eq
  apply le_antisymm
  apply le_of_lt_succ
  rw [←eq]; apply lt_succ_self
  apply le_of_lt_succ
  rw [eq]; apply lt_succ_self

open Classical in
noncomputable
def transfiniteRecursion
  {motive: Ordinal.{u} -> Sort u}
  (zero: motive 0)
  (limit: ∀o: Ordinal, o.IsSuccLimit -> (∀x, x < o -> motive x) -> motive o)
  (succ: ∀o, motive o -> motive o.succ) (o: Ordinal): motive o :=
  if h:0 = o then
    h ▸ zero
  else if g:∃o': Ordinal, o = o'.succ then
    Classical.choose_spec g ▸ (succ _ (transfiniteRecursion zero limit succ _))
  else
    limit _ (by
      rw [not_exists] at g
      apply And.intro
      apply lt_of_le_of_ne
      apply zero_le
      assumption
      assumption) (fun x h => (transfiniteRecursion zero limit succ x))
termination_by o
decreasing_by
  conv => { rhs; rw [Classical.choose_spec g] }
  apply lt_succ_self
  assumption

section

variable {motive: Ordinal.{u} -> Sort u}
  {zero: motive 0}
  {limit: ∀o: Ordinal, o.IsSuccLimit -> (∀x, x < o -> motive x) -> motive o}
  {succ: ∀o, motive o -> motive o.succ}

def transfiniteRecursion_zero :
  transfiniteRecursion zero limit succ 0 = zero := by
  rw [transfiniteRecursion, dif_pos rfl]

def transfiniteRecursion_succ (o: Ordinal) :
  transfiniteRecursion zero limit succ o.succ = (succ o (transfiniteRecursion zero limit succ o)) := by
  rw [transfiniteRecursion, dif_neg, dif_pos ⟨_, rfl⟩]
  apply cast_eq_of_heq'
  have : ∃ o': Ordinal, o.succ = o'.succ := ⟨_, rfl⟩
  have : Ordinal.succ (Classical.choose this) = o.succ := by
    rw [←Classical.choose_spec this]
  rw [Ordinal.succ.inj this]
  apply IsLimit.zero

def transfiniteRecursion_limit (o: Ordinal) (h: o.IsSuccLimit) :
  transfiniteRecursion zero limit succ o = limit o h (fun x _ => transfiniteRecursion zero limit succ x) := by
  rw [transfiniteRecursion, dif_neg, dif_neg]
  rw [not_exists]
  apply h.right
  intro h; subst o
  exact lt_irrefl h.left

end

end Ordinal
