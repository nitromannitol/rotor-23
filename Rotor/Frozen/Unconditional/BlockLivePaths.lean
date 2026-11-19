import Rotor.Frozen.Shape.BlockLivePaths
import Rotor.External.LSSProved

/-! # Unconditional block live-path criterion -/

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.block_live_paths_unconditional (P : DoublyPeriodic G)
    (π : Mechanism G) [Infinite V] (hG : G.Connected) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L₀ : ℕ, 1 ≤ L₀ ∧
      ∀ (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)],
      ∀ L : ℕ, L₀ ≤ L →
        (⨆ z : ℤ × ℤ, productLaw ν (blockEvent π P L z)) < ENNReal.ofReal ε →
        ∃ η : ℝ, 0 < η ∧ Criterion π (productLaw ν) η ∧
          ∃ δ : ℝ, 0 < δ ∧
            ∀ (ν' : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν' v)],
              (∀ v, tvDist (ν' v) (ν v) ≤ δ) → Criterion π (productLaw ν') η
-- FROZEN-STATEMENT-END
:= Rotor.Frozen.block_live_paths Rotor.External.lss_holds P π hG
