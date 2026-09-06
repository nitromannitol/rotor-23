/-
Independence under product laws: the coordinates of `Measure.infinitePi` are independent, and
functions of disjoint finite sets of coordinates are independent.  Support for
`lem:block-live-paths` (the `2`-dependence of the block field).
-/
import Rotor.Law

open MeasureTheory ProbabilityTheory

namespace Rotor

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- The coordinates of a product law are independent. -/
theorem iIndepFun_eval_infinitePi :
    iIndepFun (fun i (ω : ∀ i, X i) => ω i) (Measure.infinitePi μ) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  have : (fun (ω : ∀ i, X i) i => ω i) = id := rfl
  rw [this, Measure.map_id]
  congr
  funext i
  exact (Measure.infinitePi_map_eval μ i).symm

/-- Functions of disjoint finite sets of coordinates are independent. -/
theorem indepFun_of_disjoint {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (S T : Finset ι) (hST : Disjoint S T)
    (F : (∀ i : S, X i) → β) (hF : Measurable F) (G : (∀ i : T, X i) → γ) (hG : Measurable G) :
    IndepFun (fun ω : ∀ i, X i => F (fun i : S => ω i)) (fun ω => G (fun i : T => ω i))
      (Measure.infinitePi μ) := by
  have h := (iIndepFun_eval_infinitePi μ).indepFun_finset S T hST (fun i => measurable_pi_apply i)
  exact h.comp hF hG

end Rotor
