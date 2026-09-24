import Rotor.Support.PendantProb
import Rotor.Support.PendantCircuit
import Rotor.Support.ShiftAut
import Rotor.External.OneCircuit
import Rotor.External.AngelHolroyd

/-!
Assembly of Proposition 1.3 (`prop:pendant-counterexample`, `rotor.tex:2229-2290`).  If the
induced walk on `ℤ²` returns to `o`, the excursion argument (`excursion_core`) puts the
configuration in the bad event, whose probability is at most `1/64` for `M ≥ 50331645`
(`measure_badEvent_lt_one`).  A configuration outside the bad event never returns, so the walk
on `G_M` from `o` is not recurrent (`not_recurrent_of_no_return`).  Recurrence does not depend
on the starting vertex (`External.RecurrentOfRecurrent`), so the recurrence event is
shift-invariant, and ergodicity of the uniform law (`uniformLaw_recurrent_eq_zero`) makes its
probability zero: the walk is almost surely transient from every vertex.
-/

open Finset MeasureTheory ENNReal

namespace Rotor

variable (M : ℕ)

/-- A return of the induced walk puts the configuration in the bad event. -/
theorem mem_badEvent_of_return (hFLP : External.OneCircuit (pendantGraph M))
    (ρ : Config (pendantGraph M)) (o : Site) (h : ∃ s, 1 ≤ s ∧ Ysq M ρ o s = o) :
    ρ ∈ badEvent M o := by
  classical
  have hr : 1 ≤ Nat.find h ∧ Ysq M ρ o (Nat.find h) = o := Nat.find_spec h
  have hmin : ∀ s, 1 ≤ s → s < Nat.find h → Ysq M ρ o s ≠ o :=
    fun s hs hsr heq => Nat.find_min h hsr ⟨hs, heq⟩
  have hfr : FirstReturn (induce M ρ) o (Nat.find h) :=
    ⟨hr.1, hr.2, hmin, fun a b hab hb =>
      induced_traversal_injective M ρ o hFLP hmin hab (by omega)⟩
  obtain ⟨U, hK, hU⟩ := excursion_core (induce M ρ) o (Nat.find h) hfr
  exact ⟨U, hK, hU⟩

theorem recurrent_subset_badEvent (hFLP : External.OneCircuit (pendantGraph M)) (o : Site) :
    {ρ : Config (pendantGraph M) | Recurrent (pendantMech M) ρ (.inl o)} ⊆ badEvent M o := by
  intro ρ hρ
  by_contra hbad
  refine not_recurrent_of_no_return M ρ o (fun s hs heq => ?_) hρ
  exact hbad (mem_badEvent_of_return M hFLP ρ o ⟨s, hs, heq⟩)

theorem measure_recurrent_lt_one (hFLP : External.OneCircuit (pendantGraph M))
    (hM : 50331645 ≤ M) (o : Site) :
    uniformLaw (pendantMech M) {ρ | Recurrent (pendantMech M) ρ (.inl o)} < 1 :=
  (measure_mono (recurrent_subset_badEvent M hFLP o)).trans_lt (measure_badEvent_lt_one M hM o)

/-- Proposition 1.3. -/
theorem pendant_counterexample_proof
    (hFLP : ∀ M : ℕ, External.OneCircuit (pendantGraph M))
    (hAH : ∀ M : ℕ, External.RecurrentOfRecurrent (pendantGraph M)) :
    ∀ M : ℕ, 50331645 ≤ M → ∀ o : PVertex M,
      ∀ᵐ ρ ∂(uniformLaw (pendantMech M)), ¬ Recurrent (pendantMech M) ρ o := by
  intro M hM o
  rw [ae_iff]
  simp only [not_not]
  have h0 := (pendantPeriodic M).uniformLaw_recurrent_eq_zero (pendantGraph_connected M) (hAH M)
    (pendantPeriodic_periodic M) (Sum.inl (0 : Site))
    (measure_recurrent_lt_one M (hFLP M) hM 0)
  refine measure_mono_null (fun ρ hρ => ?_) h0
  exact hAH M (pendantMech M) inferInstance (pendantGraph_connected M) ρ o _ hρ

end Rotor
