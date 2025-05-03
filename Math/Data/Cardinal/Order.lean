import Math.Data.Ordinal.Card

namespace Cardinal

instance : IsLinearOrder Cardinal := ord.instIsLinearOrder
instance : @Relation.IsWellOrder Cardinal (· < ·) := remb_ord_lt.lift_wo

end Cardinal
