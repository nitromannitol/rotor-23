import Rotor.Support.Extinction
import Rotor.Support.PathReductionI

/-!
Proposition 4.1, `prop:subcubic-recurrence` (`rotor.tex:1342-1376`): on an infinite
connected graph of maximum degree three with independent uniform rotors, almost surely there
is no infinite live path.  An infinite live path starting with `o → x` forces the exploration
from `o → x` to reach infinitely many vertices (`exists_hist_length_ge`), which has
probability zero (`measure_reach_all`); there are countably many directed edges.
-/

open MeasureTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

/-- Proposition 4.1. -/
theorem subcubic_recurrence_proof (hG : G.Connected) (h3 : ∀ v : V, G.degree v ≤ 3) :
    ∀ᵐ ρ ∂(uniformLaw π), ¬ HasInfLivePath π ρ := by
  haveI := countable_of_connected hG
  rw [ae_iff]
  simp only [not_not]
  refine measure_mono_null (t := ⋃ e : V × V,
    {ρ : Config G | G.Adj e.1 e.2 ∧ ∀ j, Reach π e.1 e.2 j ρ}) ?_ (measure_iUnion_null fun e => ?_)
  · rintro ρ ⟨y, hpath, hlive⟩
    rw [Set.mem_iUnion]
    refine ⟨(y 0, y 1), hpath.2 0, fun j => ?_⟩
    exact exists_hist_length_ge π (y 0) (y 1) ρ (hpath.2 0) hpath hlive rfl rfl j
  · by_cases hadj : G.Adj e.1 e.2
    · exact measure_mono_null (fun ρ hρ => hρ.2) (measure_reach_all hadj h3)
    · have : {ρ : Config G | G.Adj e.1 e.2 ∧ ∀ j, Reach π e.1 e.2 j ρ} = ∅ :=
        Set.eq_empty_of_forall_notMem (fun ρ hρ => hadj hρ.1)
      rw [this, measure_empty]

end Rotor
