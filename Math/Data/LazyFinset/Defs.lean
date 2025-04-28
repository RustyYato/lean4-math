import Math.Data.LazyMultiset.Defs

structure LazyFinset (α: Type*) where
  ofMultiset ::
  toMultiset : LazyMultiset α
  nodup: toMultiset.Nodup

namespace LazyFinset

def ofList (list: LazyList α) (h: list.Nodup) : LazyFinset α where
  toMultiset := .ofList list
  nodup := h

def mem (a: α) (s: LazyFinset α) := s.toMultiset.mem a

def toMultiset.inj : Function.Injective (toMultiset (α := α)) :=
  by intro x y h;cases x; congr

def toMultiset_inj {as bs: LazyFinset α} : as.toMultiset = bs.toMultiset ↔ as = bs :=
  Function.Injective.eq_iff toMultiset.inj

def map (f: α ↪ β) (s: LazyFinset α) : LazyFinset β where
  toMultiset := s.toMultiset.map f
  nodup := by
    apply LazyMultiset.nodup_map
    exact f.inj
    exact s.nodup

def append (as bs: LazyFinset α) (nocomm: ∀x, as.mem x -> bs.mem x -> False) : LazyFinset α where
  toMultiset := as.toMultiset ++ bs.toMultiset
  nodup := by
    apply LazyMultiset.nodup_append
    exact as.nodup
    exact bs.nodup
    assumption

def flatMap (f: α ↪ LazyFinset β) (as: LazyFinset α) (h: ∀a b, as.mem a -> as.mem b -> ∀x, (f a).mem x -> (f b).mem x -> f a = f b) : LazyFinset β where
  toMultiset := as.toMultiset.flatMap (fun x => (f x).toMultiset)
  nodup := by
    apply LazyMultiset.nodup_flatMap
    apply Function.Injective.comp
    apply toMultiset.inj
    exact f.inj
    exact as.nodup
    · intro a g
      apply LazyFinset.nodup
    · intro a b ha hb x hxa hxb
      congr 1
      apply h
      repeat assumption

def card (s: LazyFinset α) : ℕ := s.toMultiset.size

instance : Membership α (LazyFinset α) where
  mem s a := s.mem a

@[ext]
def ext {α: Type*} (a b: LazyFinset α) (h: ∀x, x ∈ a ↔ x ∈ b) : a = b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  congr
  replace h : ∀x, a.mem x ↔ b.mem x := h
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons b bs =>
      have := h b
      simp at this
  | cons a as ih =>
    have := h a
    simp at this
    simp [LazyMultiset.mem_iff_eq_cons] at this
    obtain ⟨b, rfl⟩ := this
    congr
    apply ih
    exact LazyMultiset.nodup_cons_tail ha
    exact LazyMultiset.nodup_cons_tail hb
    intro x
    apply Iff.intro
    · intro hx
      have := (h x).mp (by simp [hx])
      simp at this
      apply this.resolve_left
      rintro rfl
      have := LazyMultiset.nodup_cons_head ha
      contradiction
    · intro hx
      have := (h x).mpr (by simp [hx])
      simp at this
      apply this.resolve_left
      rintro rfl
      have := LazyMultiset.nodup_cons_head hb
      contradiction

end LazyFinset
