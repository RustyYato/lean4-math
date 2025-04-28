import Math.Data.LazyMultiset.Defs

structure LazyFinset (α: Sort*) where
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
  toMultiset := as.toMultiset.append bs.toMultiset
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

end LazyFinset
