import Math.Order.Hom.Defs
import Math.Order.OrderIso

def OrderHom.ofMinHom
  [LE α] [LT α] [Min α] [IsSemiLatticeMin α]
  [LE β] [LT β] [Min β] [IsSemiLatticeMin β]
  [FunLike F α β] [IsMinHom F α β]
  (f: F) : α →o β where
  toFun := f
  resp_rel h := by
    apply min_eq_left.mp
    rw [←map_min]
    congr
    apply min_eq_left.mpr
    assumption

def OrderHom.ofMaxHom
  [LE α] [LT α] [Max α] [IsSemiLatticeMax α]
  [LE β] [LT β] [Max β] [IsSemiLatticeMax β]
  [FunLike F α β] [IsMaxHom F α β]
  (f: F) : α →o β where
  toFun := f
  resp_rel h := by
    apply max_eq_left.mp
    rw [←map_max]
    congr
    apply max_eq_left.mpr
    assumption
