import Rotor.Support.Equivariance
import Rotor.Support.ProductErgodic
import Rotor.Support.WalkMeasurable
import Rotor.External.AngelHolroyd

/-!
The lattice shift of a doubly periodic graph with a periodic mechanism is a mechanism
automorphism, so recurrence from `shift z o` for the shifted configuration is recurrence from
`o` for the original one.  With recurrence independent of the starting vertex (Angel-Holroyd,
`External.RecurrentOfRecurrent`), the recurrence event is shift-invariant, and ergodicity of
the uniform law makes its probability `0` or `1` (`ledger/ERRATA.md`, E-001).
-/

open MeasureTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (P : DoublyPeriodic G)
variable {π : Mechanism G}

namespace DoublyPeriodic

/-- The lattice shift as a mechanism automorphism. -/
def shiftAut (hπ : P.Periodic π) (z : ℤ × ℤ) : MechAut π where
  σ := P.shiftVEquiv z
  adj := fun u v => P.adj_shift z u v
  next := fun v a => congrArg Subtype.val (hπ z v a)

omit [DecidableEq V] [G.LocallyFinite] in
theorem shiftAut_act (hπ : P.Periodic π) (z : ℤ × ℤ) (ρ : Config G) :
    (P.shiftAut hπ z).act ρ = P.shiftConfig z ρ := by
  funext v
  apply Subtype.ext
  rfl

omit [G.LocallyFinite] in
theorem recurrent_shiftConfig (hπ : P.Periodic π) (z : ℤ × ℤ) (ρ : Config G) (o : V) :
    Recurrent π (P.shiftConfig z ρ) (P.shift z o) ↔ Recurrent π ρ o := by
  rw [← P.shiftAut_act hπ z]
  exact (P.shiftAut hπ z).recurrent_act ρ o

omit [G.LocallyFinite] in
theorem shiftConfig_preimage_recurrent [Infinite V] (hG : G.Connected)
    (hAH : External.RecurrentOfRecurrent G) (hπ : P.Periodic π) (z : ℤ × ℤ) (o : V) :
    P.shiftConfig z ⁻¹' {ρ | Recurrent π ρ o} = {ρ | Recurrent π ρ o} := by
  ext ρ
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro h
    exact (P.recurrent_shiftConfig hπ z ρ o).1 (hAH π inferInstance hG _ _ _ h)
  · intro h
    exact hAH π inferInstance hG _ _ _ ((P.recurrent_shiftConfig hπ z ρ o).2 h)

/-- Ergodicity: a recurrence probability below one is zero. -/
theorem uniformLaw_recurrent_eq_zero [Countable V] [Infinite V] (hG : G.Connected)
    (hAH : External.RecurrentOfRecurrent G) (hπ : P.Periodic π) (o : V)
    (h : uniformLaw π {ρ | Recurrent π ρ o} < 1) : uniformLaw π {ρ | Recurrent π ρ o} = 0 := by
  rcases P.uniformLaw_ergodic π _ (measurableSet_recurrent π o)
      (fun z => P.shiftConfig_preimage_recurrent hG hAH hπ z o) with h0 | h1
  · exact h0
  · exact absurd h1 h.ne

end DoublyPeriodic

end Rotor
