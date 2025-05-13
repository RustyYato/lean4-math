import Math.Topology.Order

namespace Topology

variable [t₁: Topology α] [t₂: Topology β] [t₃: Topology γ] [t₄: Topology X] [t₅: Topology Y] [t₆: Topology Z]

instance topo_product : Topology (α × β) := induced Prod.fst t₁ ⊓ induced Prod.snd t₂
instance topo_sum : Topology (α ⊕ β) := coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance topo_sigma {ι : Type*} {X : ι → Type v} [t₂: ∀i: ι, Topology (X i)] : Topology (Σi: ι, X i) :=
  ⨆i, coinduced (Sigma.mk i) (t₂ i)

instance topo_pi {ι : Type*} {Y : ι → Type v} [t₂:  ∀i: ι, Topology (Y i)] : Topology (∀i: ι, Y i) :=
  ⨅i, induced (fun f => f i) (t₂ i)

instance topo_quot [s: Setoid α] [Topology α] : Topology (Quotient s) :=
  coinduced (Quotient.mk s) inferInstance

instance : IsContinuous (fun x: α × β => x.fst) where
  isOpen_preimage := by
    intro s so
    apply Generate.IsOpen.of
    apply Set.mem_union.mpr
    left; refine ⟨s, ?_, rfl⟩
    assumption

instance : IsContinuous (fun x: α × β => x.snd) where
  isOpen_preimage := by
    intro s so
    apply Generate.IsOpen.of
    apply Set.mem_union.mpr
    right; refine ⟨s, ?_, rfl⟩
    assumption

instance IsContinuous.Prod.fst : IsContinuous (Prod.fst: α × β -> α) := inferInstance
instance IsContinuous.Prod.snd : IsContinuous (Prod.snd: α × β -> β) := inferInstance

instance : IsContinuous (Sum.inl (α := α) (β := β)) where
  isOpen_preimage := by
    intro s so
    exact so.left

instance : IsContinuous (Sum.inr (α := α) (β := β)) where
  isOpen_preimage := by
    intro s so
    exact so.right

instance [s: Setoid α] : IsContinuous (Quotient.mk s) where
  isOpen_preimage := by
    intro s so
    assumption

@[continuity]
def infer_continuous (f: α -> β) [IsContinuous f] : IsContinuous f := inferInstance

@[simp]
def continuous_prod_mk {f : X → Y} {g : X → Z} :
    (IsContinuous fun x => (f x, g x)) ↔ IsContinuous f ∧ IsContinuous g :=
  (@continuous_min_rng X (Y × Z) _ _ (Topology.induced Prod.fst _)
    (Topology.induced Prod.snd _)).trans <|
    continuous_induced_rng.and continuous_induced_rng

@[continuity]
def IsContinuous.prod_mk {f : Z → X} {g : Z → Y} (hf : IsContinuous f) (hg : IsContinuous g) :
    IsContinuous fun x => (f x, g x) :=
  continuous_prod_mk.2 ⟨hf, hg⟩

@[continuity]
def IsContinuous.prod_fst' {f : X → Y} (hf : IsContinuous f) :
    IsContinuous fun x: X × Z => f x.fst := by
    apply IsContinuous.comp

@[continuity]
def IsContinuous.prod_snd' {f : X → Y} (hf : IsContinuous f) :
    IsContinuous fun x: Z × X => f x.snd := by
    apply IsContinuous.comp

@[continuity]
def IsContinuous.prod_fst {f : Z → X × Y} (hf : IsContinuous f) :
    IsContinuous fun x => (f x).fst := by
    apply IsContinuous.comp

@[continuity]
def IsContinuous.prod_snd {f : Z → X × Y} (hf : IsContinuous f) :
    IsContinuous fun x => (f x).snd := by
    apply IsContinuous.comp

instance {f : Z → X} {g : Z → Y} [hf : IsContinuous f] [hg : IsContinuous g] :
  IsContinuous fun x => (f x, g x) := IsContinuous.prod_mk hf hg

@[continuity]
def IsContinuous.subtype_mk
  {P: α -> Prop} {f : Z → α} (hf : IsContinuous f) (prf: ∀x, P (f x)) :
  IsContinuous fun x: Z => (Subtype.mk (f x) (prf x)) where
  isOpen_preimage := by
    intro S hS
    obtain ⟨S, hS, rfl⟩ := hS
    exact IsOpen.preimage f S hS

@[continuity]
instance IsContinuous.subtype_val' {P: α -> Prop} : IsContinuous (Subtype.val (p := P)) where
  isOpen_preimage := by
    intro S hS
    exists S

@[continuity]
instance IsContinuous.subtype_val {P: α -> Prop} (f: β -> Subtype P) [IsContinuous f] : IsContinuous (fun x => (f x).val) := by
  apply IsContinuous.comp

def IsContinuous.cast [ta: Topology α] [tb: Topology β] [Topology γ]
  (heq: HEq ta tb)
  (h: α = β) (f: β -> γ) (hf: IsContinuous f) : IsContinuous (fun x: α => f (cast h x)) := by
    cases h; cases heq
    assumption

@[continuity]
def IsContinuous.Prod.mk (x : α) : IsContinuous fun y : β => (x, y) :=
  prod_mk (const x) id'

@[continuity]
def IsContinuous.Prod.mk_left (y : Y) : IsContinuous fun x : X => (x, y) :=
  IsContinuous.id.prod_mk (IsContinuous.const _)

@[continuity]
def IsContinuous.uncurry_left {f : α → β → γ} (x : α) (h : IsContinuous (Function.uncurry f)) :
    IsContinuous (f x) := (IsContinuous.Prod.mk x).comp' h
@[continuity]
def IsContinuous.uncurry_right {f : α → β → γ} (x : β) (h : IsContinuous (Function.uncurry f)) :
    IsContinuous (f · x) := (IsContinuous.Prod.mk_left x).comp' h

@[continuity]
def continuous_curry {g : X × Y → Z} (x : X) (h : IsContinuous g) : IsContinuous (Function.curry g x) :=
  IsContinuous.uncurry_left x h

def IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s.prod t) :=
  (hs.preimage Prod.fst).inter (ht.preimage Prod.snd)

def IsContinuous.push_discrete [Discrete α'] (f: α' × β -> γ) (hf: ∀x, IsContinuous (fun b => f (x, b))) : IsContinuous f where
  isOpen_preimage := by
    intro S hS
    rename_i h
    let f' (a: α') (b: β) : γ := f (a, b)
    have : ∀a, IsContinuous (f' a) := by continuity
    let pre_f' (a: α'): Set β := S.preimage (f' a)
    have pre_f'_open (a: α') : IsOpen (pre_f' a) := IsOpen.preimage (f' a) S hS
    rw [show S.preimage f = ⨆a: α', Set.prod {a} (pre_f' a) from ?_]
    apply IsOpen.sUnion
    rintro _ ⟨a, rfl⟩
    simp
    apply IsOpen.prod
    apply IsOpen.discrete
    apply pre_f'_open
    ext x
    simp [Set.mem_preimage, iSup, Set.mem_sUnion, Set.mem_range]
    apply Iff.intro
    intro hx
    refine ⟨_, ⟨?_, rfl⟩, ?_⟩
    exact x.1
    simp
    assumption
    intro ⟨_, ⟨a, rfl⟩, hx⟩
    simp at hx
    obtain ⟨rfl, hx⟩ := hx
    assumption

end Topology
