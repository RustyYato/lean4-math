import Math.Topology.Order

namespace Topology

variable [t₁: Topology α] [t₂: Topology β] [t₃: Topology γ] [t₄: Topology X] [t₅: Topology Y] [t₆: Topology Z]

instance topo_product : Topology (α × β) := induced Prod.fst t₁ ⊓ induced Prod.snd t₂
instance topo_sum : Topology (α ⊕ β) := coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance topo_sigma {ι : Type*} {X : ι → Type v} [t₂: ∀i: ι, Topology (X i)] : Topology (Σi: ι, X i) :=
  iSup fun i => coinduced (Sigma.mk i) (t₂ i)

instance topo_pi {ι : Type*} {Y : ι → Type v} [t₂:  ∀i: ι, Topology (Y i)] : Topology (∀i: ι, Y i) :=
  iInf fun i => induced (fun f => f i) (t₂ i)

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

def continuous_prod_mk {f : X → Y} {g : X → Z} :
    (IsContinuous fun x => (f x, g x)) ↔ IsContinuous f ∧ IsContinuous g :=
  (@continuous_inf_rng X (Y × Z) _ _ (Topology.induced Prod.fst _)
    (Topology.induced Prod.snd _)).trans <|
    continuous_induced_rng.and continuous_induced_rng

def IsContinuous.prod_mk {f : Z → X} {g : Z → Y} (hf : IsContinuous f) (hg : IsContinuous g) :
    IsContinuous fun x => (f x, g x) :=
  continuous_prod_mk.2 ⟨hf, hg⟩

def IsContinuous.Prod.mk (x : α) : IsContinuous fun y : β => (x, y) :=
  (IsContinuous.const _).prod_mk IsContinuous.id

def IsContinuous.Prod.mk_left (y : Y) : IsContinuous fun x : X => (x, y) :=
  IsContinuous.id.prod_mk (IsContinuous.const _)

def IsContinuous.uncurry_left {f : α → β → γ} (x : α) (h : IsContinuous (Function.uncurry f)) :
    IsContinuous (f x) := (IsContinuous.Prod.mk x).comp' h
def IsContinuous.uncurry_right {f : α → β → γ} (x : β) (h : IsContinuous (Function.uncurry f)) :
    IsContinuous (f · x) := (IsContinuous.Prod.mk_left x).comp' h

def continuous_curry {g : X × Y → Z} (x : X) (h : IsContinuous g) : IsContinuous (Function.curry g x) :=
  IsContinuous.uncurry_left x h

def IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s.prod t) :=
  (hs.preimage Prod.fst).inter (ht.preimage Prod.snd)

end Topology
