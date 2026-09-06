/-
The law of the initial rotors.

`rotor.tex:228-233`: "Suppose that the initial rotors are independent and
uniform among the directed edges out of each vertex."  `rotor.tex:1215-1217`:
"Denote the law of the initial rotor at each vertex `x` by `ν_x` and write `ℙ_0`
for the resulting product law."  `rotor.tex:1455-1459`: on the square lattice
`ℙ_0` is the product of uniform laws.

- The sample space is `Config G = ∀ v, G.neighborSet v` with the product
  σ-algebra, each finite factor carrying the discrete σ-algebra, and a
  product law is Mathlib's countable product `Measure.infinitePi` of the
  one-vertex laws.  Almost-sure statements are `∀ᵐ ρ ∂μ`.  CONFIRMED.
-/
import Rotor.Model
import Rotor.Basic

open MeasureTheory ProbabilityTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

/-- The discrete σ-algebra on the finite set of directed edges out of `v`. -/
instance (priority := high) neighborSet.measurableSpace (v : V) :
    MeasurableSpace (G.neighborSet v) := ⊤

instance (v : V) : DiscreteMeasurableSpace (G.neighborSet v) :=
  ⟨fun _ => trivial⟩

/-- The product law `ℙ_0` of independent initial rotors with one-vertex laws
`ν v` (`rotor.tex:1215-1217`). -/
noncomputable def productLaw (ν : ∀ v : V, Measure (G.neighborSet v))
    [∀ v, IsProbabilityMeasure (ν v)] : Measure (Config G) :=
  Measure.infinitePi ν

instance (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)] :
    IsProbabilityMeasure (productLaw ν) := by
  unfold productLaw; infer_instance

/-- The uniform law on the directed edges out of `v`; `π.nonempty` supplies the
neighbor the uniform distribution needs. -/
noncomputable def uniformAt (π : Mechanism G) (v : V) : Measure (G.neighborSet v) :=
  haveI := π.nonempty v
  (PMF.uniformOfFintype (G.neighborSet v)).toMeasure

instance (π : Mechanism G) (v : V) : IsProbabilityMeasure (uniformAt π v) := by
  haveI := π.nonempty v
  unfold uniformAt; infer_instance

/-- The law of independent uniform initial rotors, `rotor.tex:228-233`. -/
noncomputable def uniformLaw (π : Mechanism G) : Measure (Config G) :=
  productLaw (uniformAt π)

instance (π : Mechanism G) : IsProbabilityMeasure (uniformLaw π) := by
  unfold uniformLaw; infer_instance

namespace Z2

/-- The uniform law of a single rotor on the four directions. -/
noncomputable def uniformDir : Measure Dir := (PMF.uniformOfFintype Dir).toMeasure

instance : IsProbabilityMeasure uniformDir := PMF.toMeasure.isProbabilityMeasure _

/-- `ℙ₀` on the concrete square-lattice model: independent uniform rotors. -/
noncomputable def P0 : Measure RotorConfig := Measure.infinitePi (fun _ : Site => uniformDir)

instance : IsProbabilityMeasure P0 := by
  unfold P0; infer_instance

end Z2

end Rotor
