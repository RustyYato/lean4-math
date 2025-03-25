import Math.Topology.Order

namespace Topology

variable [t₁: Topology α] [t₂: Topology β] [t₃: Topology γ] [t₄: Topology X] [t₅: Topology Y] [t₆: Topology Z]

instance topo_product : Topology (α × β) := induced Prod.fst t₁ ⊓ induced Prod.snd t₂
instance topo_sum : Topology (α ⊕ β) := coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance topo_sigma {ι : Type*} {X : ι → Type v} [t₂: ∀i: ι, Topology (X i)] : Topology (Sigma X) :=
  iSup fun i => coinduced (Sigma.mk i) (t₂ i)

instance pi_topo {ι : Type*} {Y : ι → Type v} [t₂:  ∀i: ι, Topology (Y i)] : Topology (∀i: ι, Y i) :=
  iInf fun  i => induced (fun f => f i) (t₂ i)

instance : IsContinuous (fun x: α × β => x.fst) where
  isOpen_preimage := by
    intro s so
    apply Generate.IsOpen.of
    apply Set.mem_sUnion.mpr
    refine ⟨_, ⟨_, Set.mem_pair.mpr (.inl rfl), rfl⟩, ?_⟩
    refine ⟨s, ?_, ?_⟩
    assumption
    rfl

instance : IsContinuous (fun x: α × β => x.snd) where
  isOpen_preimage := by
    intro s so
    apply Generate.IsOpen.of
    apply Set.mem_sUnion.mpr
    refine ⟨_, ⟨_, Set.mem_pair.mpr (.inr rfl), rfl⟩, ?_⟩
    refine ⟨s, ?_, ?_⟩
    assumption
    rfl

instance : IsContinuous (Sum.inl (α := α) (β := β)) where
  isOpen_preimage := by
    intro s so
    exact Set.mem_sInter.mp so _ ⟨_, Set.mem_pair.mpr (.inl rfl), rfl⟩

instance : IsContinuous (Sum.inr (α := α) (β := β)) where
  isOpen_preimage := by
    intro s so
    exact Set.mem_sInter.mp so _ ⟨_, Set.mem_pair.mpr (.inr rfl), rfl⟩

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

-- instance : IsContinuous (fun (x: α) (y: β) => (x, y)) := by
--   -- have := (continuous_prod_mk (f := @id α) (g := id)).mpr

--   -- isOpen_preimage := by
--   --   intro s so
--   --   sorry
--     -- apply Generate.IsOpen.of
--     -- apply Set.mem_sUnion.mpr
--     -- refine ⟨_, ⟨_, Set.mem_pair.mpr (.inr rfl), rfl⟩, ?_⟩
--     -- refine ⟨s, ?_, ?_⟩
--     -- assumption
--     -- rfl

-- instance (f: γ -> α) (g: γ -> β) [IsContinuous f] [IsContinuous g] : IsContinuous (fun x => (f x, g x)) where
--   isOpen_preimage := by
--     intro s so
--     sorry
--     -- apply Generate.IsOpen.of
--     -- apply Set.mem_sUnion.mpr
--     -- refine ⟨_, ⟨_, Set.mem_pair.mpr (.inr rfl), rfl⟩, ?_⟩
--     -- refine ⟨s, ?_, ?_⟩
--     -- assumption
--     -- rfl

-- def comp₂ (f: α -> β -> γ) (g₀: α₀ -> α) (g₁: α₀ -> β) [IsContinuous f] [IsContinuous g₀] [IsContinuous g₁] : IsContinuous (fun x => f (g₀ x) (g₁ x)) := by
--   continuous_prod_mk.2 ⟨hf, hg⟩



-- instance
--   (f: α -> β -> α × β)
--   [ha: ∀a, IsContinuous (f a)]
--   [hb: ∀b, IsContinuous (f · b)] : IsContinuous (fun x: α × β => f x.1 x.2) where
--   isOpen_preimage := by
--     intro s so
--     induction so with
--     | univ => apply IsOpen.univ
--     | inter =>
--       rw [Set.preimage_inter]
--       apply IsOpen.inter
--       assumption
--       assumption
--     | sUnion _ ih =>
--       rw [Set.preimage_sUnion]
--       apply IsOpen.sUnion
--       intro _ ⟨x, h, eq⟩
--       subst eq
--       exact ih x h
--     | of mem =>
--       apply Generate.IsOpen.of
--       apply Set.mem_sUnion.mpr
--       obtain ⟨S, ⟨T, T_mem, eq⟩, x_open⟩ := mem
--       subst S
--       cases Set.mem_pair.mp T_mem <;> subst T
--       refine ⟨_, ⟨_, Set.mem_pair.mpr (.inl rfl), rfl⟩, ?_⟩
--       obtain ⟨as, as_open, eq⟩ := x_open; subst eq
--       rw [Set.preimage_preimage, Function.comp_def]
--       refine ⟨?_, ?_, ?_⟩






--       sorry
    -- refine ⟨s, ?_, ?_⟩
    -- assumption
    -- rfl

-- def IsOpen.prod (s: Set (α × β)) : IsOpen s ↔ IsOpen (s.image Prod.fst) ∧ IsOpen (s.image Prod.snd) := by
--   apply flip Iff.intro
--   intro ⟨h, g⟩
--   apply Generate.IsOpen.of
--   apply Set.mem_sUnion.mpr
--   -- exists s

--   rfl
  -- IsOpen s := Topology.IsOpen (s.image Prod.fst) ∧ Topology.IsOpen (s.image Prod.snd)
  -- univ_open := by
  --   apply And.intro
  --   by_cases h:Nonempty β
  --   suffices Set.image ⊤ Prod.fst = ⊤ by
  --     rw [this]; apply IsOpen.univ
  --   obtain ⟨b⟩ := h
  --   apply Set.ext_univ
  --   intro a; exists ⟨a, b⟩
  --   suffices Set.image ⊤ Prod.fst = ∅ by
  --     rw [this]; apply IsOpen.empty
  --   apply Set.ext_empty
  --   intro a ⟨x, _, mem⟩
  --   exact h ⟨x.snd⟩

  --   by_cases h:Nonempty α
  --   suffices Set.image ⊤ Prod.snd = ⊤ by
  --     rw [this]; apply IsOpen.univ
  --   obtain ⟨a⟩ := h
  --   apply Set.ext_univ
  --   intro b; exists ⟨a, b⟩
  --   suffices Set.image ⊤ Prod.snd = ∅ by
  --     rw [this]; apply IsOpen.empty
  --   apply Set.ext_empty
  --   intro a ⟨x, _, mem⟩
  --   exact h ⟨x.fst⟩
  -- inter_open := by
  --   intro x y ⟨hax, hbx⟩ ⟨hay, hby⟩
  --   apply And.intro
  --   rw [Set.image_inter]
  --   apply IsOpen.inter

  --   sorry


end Topology
