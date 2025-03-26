import Math.Topology.Basic
import Math.Data.Real.MetricSpace
import Math.Data.NNReal.Basic

instance : Topology ℝ≥0 := inferInstanceAs (Topology (Subtype _))

instance instContNNℝnpow (n: ℕ) : Topology.IsContinuous (fun x: ℝ≥0 => x ^ n) where
  isOpen_preimage := by
    rintro _ ⟨S, hS, rfl⟩
    refine ⟨_, hS.preimage (· ^ n), ?_⟩
    rfl
