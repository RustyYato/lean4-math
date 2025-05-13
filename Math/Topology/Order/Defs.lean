import Math.Topology.Constructions

namespace Topology

section

class IsOrderClosed (α : Type*) [Topology α] [LE α] : Prop where
  /-- The set `{ (x, y) | x ≤ y }` is a closed set. -/
  isClosed_le_prod : IsClosed (Set.mk fun p : α × α => p.1 ≤ p.2)

def isClosed_le_prod (α : Type*) [Topology α] [LE α] [IsOrderClosed α] := IsOrderClosed.isClosed_le_prod (α := α)

variable [Topology α] [LE α] [IsOrderClosed α]

def isClosed_le [Topology β] {f g : β → α} (hf : IsContinuous f) (hg : IsContinuous g) :
    IsClosed (Set.mk fun b => f b ≤ g b) := by
  show IsClosed <| (Set.mk fun x: α × α => x.1 ≤ x.2).preimage (fun x: β => (f x, g x))
  apply IsClosed.preimage
  apply isClosed_le_prod

instance {P: α -> Prop} : Topology.IsOrderClosed (Subtype P) where
  isClosed_le_prod := by
    show IsClosed <| (Set.mk fun p: α × α => p.fst ≤ p.snd).preimage (fun x: (Subtype P) × (Subtype P) => (x.1.val, x.2.val))
    apply Generate.IsOpen.map _ (isClosed_le_prod α)
    intro s hs
    apply Generate.IsOpen.of
    rcases hs with hs | hs
    left; obtain ⟨t, topen, rfl⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    exact t.preimage Subtype.val
    apply IsOpen.preimage
    assumption
    rfl
    right; obtain ⟨t, topen, rfl⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    exact t.preimage Subtype.val
    apply IsOpen.preimage
    assumption
    rfl

end

section

def ofOrder {α: Type*} [LT α] := Topology.generate (Set.mk fun s: Set α => ∃a, s = Set.Ioi a ∨ s = Set.Iio a)

class IsOrderTopology (α : Type*) [h: Topology α] [LT α] where
  generated_from_intervals: h = ofOrder

protected def ofOrder.IsOrderTopology [LT α] : @IsOrderTopology α ofOrder _ :=
  let _topo : Topology α := ofOrder
  { generated_from_intervals := rfl }

variable [Topology α] [LT α] [LE α] [t : IsOrderTopology α] [IsPreOrder α]

def isOpen_iff_generate_intervals {s : Set α} :
    IsOpen s ↔ Generate.IsOpen (Set.mk fun s => ∃a, s = Set.Ioi a ∨ s = Set.Iio a) s := by
  rw [t.generated_from_intervals]; rfl

def iio_open (a: α) : IsOpen (Set.Iio a) := by
  rw [isOpen_iff_generate_intervals]
  apply Generate.IsOpen.of
  exists a
  right; rfl

def ioi_open (a: α) : IsOpen (Set.Ioi a) := by
  rw [isOpen_iff_generate_intervals]
  apply Generate.IsOpen.of
  exists a
  left; rfl

def ioo_open (a b: α) : IsOpen (Set.Ioo a b) := by
  apply IsOpen.inter
  apply ioi_open
  apply iio_open

variable [IsLinearOrder α]

def ici_closed (a: α) : IsClosed (Set.Ici a) := by
  show IsOpen _
  rw [show (Set.Ici a)ᶜ = Set.Iio a from ?_]
  apply iio_open
  ext x
  simp [Set.mem_compl, not_le]

def iic_closed (a: α) : IsClosed (Set.Iic a) := by
  show IsOpen _
  rw [show (Set.Iic a)ᶜ = Set.Ioi a from ?_]
  apply ioi_open
  ext x
  simp [Set.mem_compl, not_le]

def icc_closed (a b: α) : IsClosed (Set.Icc a b) := by
  show IsOpen _
  rw [show (Set.Icc a b)ᶜ = Set.Iio a ∪ Set.Ioi b from ?_]
  apply IsOpen.union
  apply iio_open
  apply ioi_open
  ext x
  simp [Set.mem_compl, Set.mem_union, not_le, ←not_lt]
  apply Classical.or_iff_not_imp_left.symm

end

end Topology
