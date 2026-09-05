/-
The law of the initial rotors: independent and uniform at every site,
`rotor.tex:228-233` ("Suppose that the initial rotors are independent and
uniform among the directed edges out of each vertex") and `rotor.tex:1455-1459`
("`ℙ_0` is their product law").

  M-004  The sample space is `RotorConfig = ℤ × ℤ → Fin 4` with the product
         σ-algebra, and `ℙ₀` is Mathlib's countable product measure
         `Measure.infinitePi` of the uniform law on `Fin 4`.  Almost-sure
         statements are `∀ᵐ ρ ∂ℙ₀`.
-/
import Rotor.Basic

open MeasureTheory ProbabilityTheory

namespace Rotor

/-- The uniform law of a single rotor on the four directions. -/
noncomputable def uniformDir : Measure Dir := (PMF.uniformOfFintype Dir).toMeasure

instance : IsProbabilityMeasure uniformDir := PMF.toMeasure.isProbabilityMeasure _

/-- `ℙ₀`: the product law of independent uniform initial rotors (ruling M-004). -/
noncomputable def P0 : Measure RotorConfig := Measure.infinitePi (fun _ : Site => uniformDir)

instance : IsProbabilityMeasure P0 := by
  unfold P0; infer_instance

end Rotor
