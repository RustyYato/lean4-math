import Math.Data.Free.Module
import Math.Data.Set.Like

def LinearSpan (R M: Type*) (s: Set M) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M] [DecidableEq M] :=
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

def single (r: R) (m: M) (hm: m ∈ s) : LinearSpan R M s := Finsupp.single ⟨m, hm⟩ r

@[simp]
def single_valHom (r: R) (m: M) (hm: m ∈ s) : valHom (single r m hm) = r • m := by
  apply FreeModule.apply_lift_single

@[simp]
def single_val (r: R) (m: M) (hm: m ∈ s) : (single r m hm).val = r • m := single_valHom _ _ hm

instance : CoeTC (LinearSpan R M s) M := ⟨valHom⟩
instance : FunLike (LinearSpan R M s) s R := inferInstanceAs (FunLike (Finsupp s R _) s R)

@[simp] def apply_add (a b: LinearSpan R M s) (m: s) : (a + b) m = a m + b m := rfl
@[simp] def apply_nsmul (a: LinearSpan R M s) (n: ℕ) (m: s) : (n • a) m = n • a m := rfl
@[simp] def apply_smul (a: LinearSpan R M s) (n: R) (m: s) : (n • a) m = n • a m := rfl

def apply_single {m: M} {r: R} (x: s) (hm: m ∈ s) : single r m hm x = if x = ⟨m, hm⟩  then r else 0 := rfl

def mem_support_single {r: R} {m: M} {x: s} {hm: m ∈ s} : x ∈ Set.support (single r m hm) -> r ≠ 0 ∧ x.val = m := by
  rintro h
  rw [Set.mem_support, apply_single] at h
  split at h
  apply And.intro
  trivial
  subst x; rfl
  contradiction

def of_empty_support (a: LinearSpan R M s) :
  Set.support a = ∅ -> a = 0 := by
  intro supp_eq
  apply Finsupp.ext
  intro m
  apply Classical.byContradiction
  intro hm
  suffices m ∈ Set.support a by
    rw [supp_eq] at this
    contradiction
  rwa [Set.mem_support]

@[ext]
def ext (a b: LinearSpan R M s) : (∀m, a m = b m) -> a = b :=
  Finsupp.ext _ _

@[induction_eliminator]
def induction {motive: LinearSpan R M s -> Prop}
  (zero: motive 0)
  (single: ∀r m hm, r ≠ 0 -> motive (single r m hm))
  (add: ∀a b,
    motive a ->
    motive b ->
    Set.support (a + b) = Set.support a ∪ Set.support b ->
    (a + b = 0 -> a = 0 ∧ b = 0) ->
    motive (a + b)):
    ∀l, motive l := by
    apply Finsupp.induction zero
    intros m r
    by_cases hr:r = 0
    show motive (LinearSpan.single _ _ _)
    rw [hr, show LinearSpan.single (0: R) m.val _ = 0 from ?_]
    apply zero
    ext; rw [apply_single]; split <;> rfl
    apply single
    assumption
    intro a b ha hb h
    apply add
    assumption
    assumption
    ext m
    simp [Set.mem_support, Set.mem_union]
    rw [Classical.not_iff_not, not_or, Classical.not_not, Classical.not_not, Classical.not_not]
    apply Iff.intro
    apply h
    intro ⟨h, g⟩
    show a m + b m = 0
    erw [h, g, add_zero]
    intro g
    apply And.intro
    ext m
    exact (h m (by
      show (a + b) m = 0
      rw [g]; rfl)).left
    ext m
    exact (h m (by
      show (a + b) m = 0
      rw [g]; rfl)).right

def support_single (r: R) (m: M) (hm: m ∈ s) : Set.support (single r m hm) = ∅ ∨ Set.support (single r m hm) = {⟨m, hm⟩} := by
  by_cases h:r = 0
  subst r
  left;
  apply Set.ext_empty
  intro x hx
  rw [Set.mem_support, apply_single] at hx
  split at hx <;> contradiction
  right
  ext
  simp [Set.mem_support, apply_single]
  intro; assumption

def castSuperset (s t: Set M) (h: s ⊆ t) (f: LinearSpan R M s) : LinearSpan R M t := by
  apply FreeModule.lift (fun x => ?_) f
  apply LinearSpan.single 1 x.val
  apply h
  apply x.property

def castSuperset_val (s t: Set M) (h: s ⊆ t) (f: LinearSpan R M s) : (castSuperset s t h f).val = f.val := by
  unfold val
  unfold valHom
  unfold castSuperset
  erw [←LinearMap.apply_comp, FreeModule.lift_lift]
  induction f with
  | zero => rfl
  | single r m hm hr => erw [FreeModule.apply_lift_single]
  | add a b iha ihb h g => simp; rw [map_add, map_add, iha, ihb]

def erase {s: Set M} (f: LinearSpan R M s) (m: M) : LinearSpan R M (s \ {m}: Set M) := by
  apply FreeModule.lift (fun x => ?_) f
  refine if hx:x.val = m then ?_ else ?_
  exact 0
  apply LinearSpan.single 1 x.val
  apply And.intro
  apply x.property
  assumption

def erase_val {s: Set M} (f: LinearSpan R M s) (m: M) (hm: m ∈ s) : (erase f m: M) + f ⟨m, hm⟩ • m = f := by
  induction f with
  | zero =>
    unfold valHom erase
    show _ + 0  • m = _
    simp
    repeat rw [map_zero]
  | single r v hv hr =>
    simp [single_valHom, apply_single]
    unfold valHom erase
    erw [FreeModule.apply_lift_single]
    split
    simp
    rw [if_pos]
    simp [map_zero]
    subst m; rfl
    symm; assumption
    simp
    erw [map_smul, FreeModule.apply_lift_single]
    rw [if_neg]
    simp
    apply Ne.symm
    assumption
  | add a b iha ihb h g =>
    rw [map_add]
    unfold valHom erase
    repeat rw [map_add]
    rw [Finsupp.apply_add, add_smul]
    rw [add_assoc, add_left_comm _ (a _ • m), ←add_assoc]
    erw [iha, ihb]
    rfl

def apply_erase_mem {s: Set M} (f: LinearSpan R M s) {m: M} (x: M) (hx: x ∈ s \ {m}) : (f.erase m) ⟨x, hx⟩ = f ⟨x, hx.left⟩ := by
  unfold erase

  sorry

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

end LinearSpan
