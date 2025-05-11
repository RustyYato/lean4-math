import Math.Algebra.Semigroup.Defs
import Math.Data.Ordinal.Defs

namespace Ordinal

instance : IsAddZeroClass Ordinal where
  zero_add a := by
    cases a with | _ a rela =>
    apply sound
    infer_instance
    simp
    apply RelIso.trans
    apply RelIso.congrSumLex
    apply rel_ulift_eqv
    rfl
    symm
    exact {
      toFun := .inr
      invFun
      | .inl x => nomatch x
      | .inr x => x
      leftInv _ := rfl
      rightInv
      | .inl x => nomatch x
      | .inr x => rfl
      resp_rel := by simp [resp_rel]
    }
  add_zero a := by
    cases a
    apply sound
    infer_instance
    simp
    apply RelIso.trans
    apply RelIso.congrSumLex
    rfl
    apply rel_ulift_eqv
    symm
    exact {
      toFun := .inl
      invFun
      | .inr x => nomatch x
      | .inl x => x
      leftInv _ := rfl
      rightInv
      | .inr x => nomatch x
      | .inl x => rfl
      resp_rel := by simp [resp_rel]
    }


end Ordinal
