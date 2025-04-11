import Math.Data.Free.Module
import Math.Data.Set.Like

def LinearSpan (R M: Type*) (s: Set M) [Zero R] [DecidableEq M] :=
  FreeModule R s

namespace LinearSpan

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M] {s: Set M}

instance : Zero (LinearSpan R M s) :=
  inferInstanceAs (Zero (FreeModule _ _))
instance : Add (LinearSpan R M s) :=
  inferInstanceAs (Add (FreeModule _ _))
instance : SMul ℕ (LinearSpan R M s) :=
  inferInstanceAs (SMul ℕ (FreeModule _ _))
instance : SMul R (LinearSpan R M s) :=
  inferInstanceAs (SMul R (FreeModule _ _))

instance : IsAddMonoid (LinearSpan R M s) :=
  inferInstanceAs (IsAddMonoid (FreeModule _ _))
instance : IsAddCommMagma (LinearSpan R M s) :=
  inferInstanceAs (IsAddCommMagma (FreeModule _ _))
instance : IsModule R (LinearSpan R M s) :=
  inferInstanceAs (IsModule R (FreeModule _ _))

instance : FunLike (LinearSpan R M s) s R := inferInstanceAs (FunLike (Finsupp s R _) s R)

def valHom : LinearSpan R M s →ₗ[R] M := FreeModule.lift Subtype.val

@[coe]
abbrev val (f: LinearSpan R M s) := valHom f

@[simp]
def zero_val : (0 : LinearSpan R M s).val = 0 := by
  rw [val, map_zero]

@[simp]
def add_val (a b: LinearSpan R M s) : (a + b).val = a.val + b.val := map_add _

@[simp]
def smul_val (r: R) (a: LinearSpan R M s) : (r • a).val = r • a.val := map_smul _

def ι (R: Type*) [SemiringOps R] [IsSemiring R] (m: M) (hm: m ∈ s) : LinearSpan R M s := FreeModule.ι R ⟨m, hm⟩

def single (r: R) (m: M) (hm: m ∈ s) : LinearSpan R M s :=
  r • ι R m hm

def apply_ι {m: M} {hm: m ∈ s} {v: s} : ι R m hm v = if v = ⟨m, hm⟩ then 1 else 0 := rfl
def apply_single {r: R} {m: M} {hm: m ∈ s} {v: s} : single r m hm v = if v = ⟨m, hm⟩ then r else 0 := by
  rw [single]
  show r • ι R m hm v = _
  rw [apply_ι]
  split <;> simp

@[simp]
def valHom_ι (m: M) (hm: m ∈ s) : valHom (ι R m hm) = m := by
  unfold ι
  rw [valHom]
  erw [FreeModule.apply_lift_ι]

@[simp]
def apply_valHom_single (r: R) (m: M) (hm: m ∈ s) : valHom (single r m hm) = r • m := by
  unfold single
  rw [map_smul, valHom_ι]

@[simp]
def single_val (r: R) (m: M) (hm: m ∈ s) : (single r m hm).val = r • m := apply_valHom_single _ _ hm

instance : CoeTC (LinearSpan R M s) M := ⟨valHom⟩

@[simp] def apply_add (a b: LinearSpan R M s) (m: s) : (a + b) m = a m + b m := rfl
@[simp] def apply_nsmul (a: LinearSpan R M s) (n: ℕ) (m: s) : (n • a) m = n • a m := rfl
@[simp] def apply_smul (a: LinearSpan R M s) (n: R) (m: s) : (n • a) m = n • a m := rfl

@[ext]
def ext (a b: LinearSpan R M s) : (∀m, a m = b m) -> a = b :=
  Finsupp.ext _ _

@[induction_eliminator]
def induction {motive: LinearSpan R M s -> Prop}
  (zero: motive 0)
  (ι: ∀m hm, motive (ι R m hm))
  (smul: ∀(r: R) a, r ≠ 0 -> motive a -> motive (r • a))
  (add: ∀a b,
    motive a ->
    motive b ->
    (∀x, a x + b x = 0 -> a x = 0 ∧ b x = 0) ->
    Set.support a ∩ Set.support b = ∅ ->
    motive (a + b)):
    ∀l, motive l := by
    intro l
    induction l using FreeModule.induction with
    | zero => apply zero
    | ι => apply ι
    | smul => apply smul <;> assumption
    | add => apply add <;> assumption

-- @[induction_eliminator]
-- def induction {motive: LinearSpan R M s -> Prop}
--   (zero: motive 0)
--   (single: ∀r m hm, r ≠ 0 -> motive (single r m hm))
--   (add: ∀a b,
--     motive a ->
--     motive b ->
--     Set.support (a + b) = Set.support a ∪ Set.support b ->
--     (a + b = 0 -> a = 0 ∧ b = 0) ->
--     motive (a + b)):
--     ∀l, motive l := by
--     apply Finsupp.induction zero
--     intros m r
--     by_cases hr:r = 0
--     show motive (LinearSpan.single _ _ _)
--     rw [hr, show LinearSpan.single (0: R) m.val _ = 0 from ?_]
--     apply zero
--     ext; rw [apply_single]; split <;> rfl
--     apply single
--     assumption
--     intro a b ha hb h
--     apply add
--     assumption
--     assumption
--     ext m
--     simp [Set.mem_support, Set.mem_union]
--     rw [Classical.not_iff_not, not_or, Classical.not_not, Classical.not_not, Classical.not_not]
--     apply Iff.intro
--     apply h
--     intro ⟨h, g⟩
--     show a m + b m = 0
--     erw [h, g, add_zero]
--     intro g
--     apply And.intro
--     ext m
--     exact (h m (by
--       show (a + b) m = 0
--       rw [g]; rfl)).left
--     ext m
--     exact (h m (by
--       show (a + b) m = 0
--       rw [g]; rfl)).right

def castSuperset (s t: Set M) (h: s ⊆ t) (f: LinearSpan R M s) : LinearSpan R M t := by
  apply FreeModule.lift (fun x => ?_) f
  apply ι R x.val
  apply h
  apply x.property

def castSuperset_val (s t: Set M) (h: s ⊆ t) (f: LinearSpan R M s) : (castSuperset s t h f).val = f.val := by
  unfold val
  unfold valHom
  unfold castSuperset
  erw [←LinearMap.apply_comp, FreeModule.map_comp_lift, Function.comp_def]
  conv => {
    lhs; arg 1; arg 2; intro x
    erw [FreeModule.apply_lift_ι]
  }
  simp
  rfl

def exists_subset_of_support [IsNontrivial R] [NoZeroDivisors R] (C: LinearSpan R M s) (h: Set.support ⇑C ⊆ t.preimage Subtype.val) :
  ∃S: LinearSpan R M t, (C: M) = S ∧ ∀(m: M) (hs: m ∈ s) (ht: m ∈ t), C ⟨m, hs⟩ = S ⟨m, ht⟩ := by
  induction C with
  | zero =>
    exists 0
    apply And.intro
    rw [map_zero, map_zero]
    intros; rfl
  | smul r a hr ih =>
    obtain ⟨S, hS, gS⟩ := ih (Set.sub_trans (by
      intro x hx g
      cases of_mul_eq_zero g
      contradiction
      contradiction) h)
    exists r • S
    apply And.intro
    rw [map_smul, map_smul, hS]
    intro m hs ht
    show r * _ = r * _
    rw [gS]
  | add a b iha ihb hadd hinter =>
    obtain ⟨Sa, hSa, gSa⟩ := iha (Set.sub_trans (by
      intro x hx g
      cases hadd _ g
      contradiction) h)
    obtain ⟨Sb, hSb, gSb⟩ := ihb (Set.sub_trans (by
      intro x hx g
      cases hadd _ g
      contradiction) h)
    exists Sa + Sb
    apply And.intro
    rw [map_add, map_add, hSa, hSb]
    intro m hs ht
    rw [apply_add, apply_add, gSa, gSb]
  | ι m hm =>
    have := h ⟨m, hm⟩
    rw [Set.mem_support, apply_ι] at this
    simp at this
    have : m ∈ t := this (zero_ne_one _).symm
    exists ι R m this
    apply And.intro
    rw [valHom_ι, valHom_ι]
    intro v hs ht
    rw [apply_ι, apply_ι]
    simp

def eraseHom {s: Set M} (m: M) : LinearSpan R M s →ₗ[R] LinearSpan R M (s \ {m}: Set M) := by
  apply FreeModule.lift (fun x => ?_)
  refine if hx:x.val = m then ?_ else ?_
  exact 0
  apply ι R x.val
  apply And.intro
  apply x.property
  assumption

def eraseHom_ι {s: Set M} (m v: M) (hm: m ∈ s) : eraseHom v (ι R m hm) = if hv:m = v then 0 else ι R m (by
  apply And.intro
  assumption
  assumption) := by
  unfold eraseHom ι
  erw [FreeModule.apply_lift_ι]

def erase {s: Set M} (f: LinearSpan R M s) (m: M) : LinearSpan R M (s \ {m}: Set M) :=
  eraseHom m f

def erase_zero {s: Set M} : erase (R := R) (s := s) 0 m = 0 :=
  map_zero (eraseHom m)
def erase_smul {s: Set M} (r: R) (a: LinearSpan R M s) : erase (r • a) m = r • erase a m :=
  map_smul (eraseHom m)
def erase_add {s: Set M} (a b: LinearSpan R M s) : erase (a + b) m = erase a m + erase b m :=
  map_add (eraseHom m)
def erase_ι {s: Set M} (m v: M) (hm: m ∈ s) : erase (ι R m hm) v = if hv:m = v then 0 else ι R m (by
  apply And.intro
  assumption
  assumption) := by
  apply eraseHom_ι

def erase_val {s: Set M} (f: LinearSpan R M s) (m: M) (hm: m ∈ s) : (erase f m: M) + f ⟨m, hm⟩ • m = f := by
  unfold erase
  induction f with
  | zero =>
    simp [map_zero]
    apply zero_smul
  | ι v hv =>
    simp
    rw [eraseHom_ι]
    split
    subst v
    simp [map_zero, apply_ι]
    simp [map_zero, apply_ι]
    rw [if_neg]; simp
    apply Ne.symm; assumption
  | smul r a hr ih  =>
    simp [map_smul, mul_smul]
    rw [←smul_add, ih]
  | add a b iha ihb =>
    simp [map_add, apply_add, add_smul]
    rw [add_assoc, add_left_comm _ (a ⟨m, hm⟩ • m),
      ←add_assoc, iha, ihb]

def apply_erase_mem {s: Set M} (f: LinearSpan R M s) {m: M} (x: M) (hx: x ∈ s \ {m}) : (f.erase m) ⟨x, hx⟩ = f ⟨x, hx.left⟩ := by
  induction f with
  | zero =>
    rw [erase_zero]
    rfl
  | ι v hv =>
    rw [erase_ι, apply_ι]
    split
    split <;> rename_i g
    cases g; subst x
    have := hx.right
    contradiction
    rfl
    rw [apply_ι]
    split <;> rename_i g; rw [if_pos]
    cases g; rfl
    rw [if_neg]
    intro h; apply g; cases h
    rfl
  | smul _ _ _ ih =>
    rw [erase_smul, apply_smul, ih]
    rfl
  | add a b iha ihb =>
    rw [erase_add, apply_add, iha, ihb]
    rfl

def cast {s t: Set M} (h: s = t) (f: LinearSpan R M s) : LinearSpan R M t := h ▸ f
def cast_val {s t: Set M} (h: s = t) (f: LinearSpan R M s) : (f.cast h: M) = f := by
  cases h
  rfl

def apply_cast_mem {s t: Set M} (h: s = t) (f: LinearSpan R M s) (x: M) (hx: x ∈ s) : (f.cast h) ⟨x, h ▸ hx⟩ = f ⟨x, hx⟩ := by
  cases h
  rfl

end LinearSpan

namespace LinearSpan

variable {R M: Type*} [RingOps R] [IsRing R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
   [DecidableEq M] {s: Set M}

instance : Neg (LinearSpan R M s) :=
  inferInstanceAs (Neg (FreeModule _ _))
instance : Sub (LinearSpan R M s) :=
  inferInstanceAs (Sub (FreeModule _ _))
instance : SMul ℤ (LinearSpan R M s) :=
  inferInstanceAs (SMul ℤ (FreeModule _ _))
instance : IsAddGroup (LinearSpan R M s) :=
  inferInstanceAs (IsAddGroup (FreeModule _ _))

@[simp] def apply_sub (a b: LinearSpan R M s) (m: s) : (a - b) m = a m - b m := rfl
@[simp] def apply_neg (a: LinearSpan R M s) (m: s) : (-a) m = -a m := rfl
@[simp] def apply_zsmul (a: LinearSpan R M s) (n: ℤ) (m: s) : (n • a) m = n • a m := rfl

instance : Subsingleton (LinearSpan R M ∅) where
  allEq a b := by
    ext m; have := m.property
    contradiction

end LinearSpan
