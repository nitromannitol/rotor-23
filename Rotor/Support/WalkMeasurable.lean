import Rotor.Support.WalkBasics
import Rotor.Law

/-!
Measurability of the rotor walk in the initial configuration: the position `X_t` and every
rotor `ρ_t(v)` are measurable functions of `ρ`, by induction on `t`, and therefore the
recurrence event `{ρ : Recurrent π ρ o}` is measurable (a countable intersection of countable
unions of such level sets).  Used for the pendant counterexample, where ergodicity turns a
recurrence probability below one into zero.
-/

open MeasureTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [Countable V]
variable (π : Mechanism G) (o : V)

theorem measurableSet_X_rot : ∀ t : ℕ,
    (∀ x : V, MeasurableSet {ρ : Config G | X π ρ o t = x}) ∧
    (∀ (v : V) (a : G.neighborSet v), MeasurableSet {ρ : Config G | rot π ρ o t v = a})
  | 0 => by
    refine ⟨fun x => ?_, fun v a => ?_⟩
    · have hX : ∀ ρ : Config G, X π ρ o 0 = o := fun _ => rfl
      by_cases h : o = x
      · simp [h]
      · simp [hX, h]
    · exact measurable_pi_apply v (MeasurableSet.singleton a)
  | t + 1 => by
    obtain ⟨hX, hrot⟩ := measurableSet_X_rot t
    refine ⟨fun x => ?_, fun v a => ?_⟩
    · have : {ρ : Config G | X π ρ o (t + 1) = x} =
          ⋃ v : V, ⋃ a : G.neighborSet v, ⋃ (_ : (π.next v a).1 = x),
            ({ρ | X π ρ o t = v} ∩ {ρ | rot π ρ o t v = a}) := by
        ext ρ
        simp only [X_succ, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
        constructor
        · intro h
          exact ⟨X π ρ o t, rot π ρ o t (X π ρ o t), h, rfl, rfl⟩
        · rintro ⟨v, a, hva, hv, ha⟩
          subst hv
          rw [ha]
          exact hva
      rw [this]
      exact MeasurableSet.iUnion fun v => MeasurableSet.iUnion fun a =>
        MeasurableSet.iUnion fun _ => (hX v).inter (hrot v a)
    · have : {ρ : Config G | rot π ρ o (t + 1) v = a} =
          ({ρ | X π ρ o t = v} ∩ {ρ | rot π ρ o t v = (π.next v).symm a}) ∪
            ({ρ | X π ρ o t = v}ᶜ ∩ {ρ | rot π ρ o t v = a}) := by
        ext ρ
        simp only [rot_succ, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        by_cases h : X π ρ o t = v
        · subst h
          rw [Function.update_self]
          simp only [true_and, not_true_eq_false, false_and, or_false]
          exact Equiv.apply_eq_iff_eq_symm_apply _
        · rw [Function.update_of_ne (Ne.symm h)]
          simp [h]
      rw [this]
      exact ((hX v).inter (hrot v _)).union ((hX v).compl.inter (hrot v a))

theorem measurableSet_X_eq (t : ℕ) (x : V) : MeasurableSet {ρ : Config G | X π ρ o t = x} :=
  (measurableSet_X_rot π o t).1 x

/-- The recurrence event is measurable. -/
theorem measurableSet_recurrent : MeasurableSet {ρ : Config G | Recurrent π ρ o} := by
  have : {ρ : Config G | Recurrent π ρ o} =
      ⋂ x : V, ⋂ N : ℕ, ⋃ t : ℕ, ⋃ (_ : N ≤ t), {ρ | X π ρ o t = x} := by
    ext ρ
    simp only [Recurrent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    refine forall_congr' fun x => ?_
    rw [← Nat.frequently_atTop_iff_infinite, Filter.frequently_atTop]
  rw [this]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun t =>
    MeasurableSet.iUnion fun _ => measurableSet_X_eq π o t x

end Rotor
