/-
Measurability of the routing-derived events and of the passage time.  Every
such event depends on the rotors at finitely many vertices, hence is a
cylinder event of the product σ-algebra; the countable unions and
intersections over lists and finite sets of vertices then keep
measurability.  `rotor.tex:810-813`: "As `G` is countable, the event that
the boundary routing of every nonempty finite set terminates is measurable."
-/
import Rotor.Support.Equivariance
import Rotor.Support.PathReductionI
import Rotor.Law

open Finset MeasureTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-! ### Functions of finitely many coordinates are measurable -/

/-- The restriction of a configuration to a finite set of vertices. -/
def restr (F : Finset V) (ρ : Config G) : ∀ v : F, G.neighborSet v := fun v => ρ v

omit [DecidableEq V] in
theorem measurable_restr (F : Finset V) : Measurable (restr (G := G) F) :=
  measurable_pi_lambda _ (fun v => measurable_pi_apply v.1)

omit [DecidableEq V] in
/-- A function of the rotors at finitely many vertices is measurable. -/
theorem measurable_of_restr [G.LocallyFinite] {β : Type*} [MeasurableSpace β] (F : Finset V)
    (f : (∀ v : F, G.neighborSet v) → β) : Measurable (fun ρ : Config G => f (restr F ρ)) :=
  (measurable_of_finite f).comp (measurable_restr F)

omit [DecidableEq V] in
/-- A set of configurations determined by the rotors at finitely many
vertices is measurable. -/
theorem measurableSet_of_depends [G.LocallyFinite] (F : Finset V) (P : Set (Config G))
    (h : ∀ ρ ρ' : Config G, (∀ v ∈ F, ρ v = ρ' v) → (ρ ∈ P ↔ ρ' ∈ P)) : MeasurableSet P := by
  classical
  -- `P` is the preimage under `restr F` of its image
  have : P = restr F ⁻¹' (restr F '' P) := by
    ext ρ
    constructor
    · intro hρ; exact ⟨ρ, hρ, rfl⟩
    · rintro ⟨ρ', hρ', heq⟩
      have : ∀ v ∈ F, ρ' v = ρ v := by
        intro v hv
        have := congrFun heq ⟨v, hv⟩
        simpa [restr] using this
      exact (h ρ' ρ this).1 hρ'
  rw [this]
  exact measurable_restr F (MeasurableSet.of_discrete)

/-! ### Routings depend on the rotors at the actuated vertices -/

/-- Running the same actuations from states with the same particles and
rotors agreeing on the actuated vertices gives the same particles. -/
theorem run_σ_congr (S : Finset V) (ξ ξ' : RState G) (vs : List V) (hσ : ξ.σ = ξ'.σ)
    (hρ : ∀ v ∈ vs, ξ.ρ v = ξ'.ρ v) : (run π S ξ vs).σ = (run π S ξ' vs).σ := by
  induction vs generalizing ξ ξ' with
  | nil => exact hσ
  | cons v vs ih =>
    have hv := hρ v (List.mem_cons_self ..)
    have h1 : (actuate π S ξ v).σ = (actuate π S ξ' v).σ := by
      funext x
      simp only [actuate, hσ, hv]
    have h2 : ∀ w ∈ vs, (actuate π S ξ v).ρ w = (actuate π S ξ' v).ρ w := by
      intro w hw
      by_cases hwv : w = v
      · subst hwv; rw [actuate_ρ_self, actuate_ρ_self, hv]
      · rw [actuate_ρ_of_ne π S ξ v w hwv, actuate_ρ_of_ne π S ξ' v w hwv]
        exact hρ w (List.mem_cons_of_mem v hw)
    rw [run_cons, run_cons]
    exact ih _ _ h1 h2

theorem isLegal_congr (S : Finset V) (ξ ξ' : RState G) (vs : List V) (hσ : ξ.σ = ξ'.σ)
    (hρ : ∀ v ∈ vs, ξ.ρ v = ξ'.ρ v) : IsLegal π S ξ vs ↔ IsLegal π S ξ' vs := by
  induction vs generalizing ξ ξ' with
  | nil => simp
  | cons v vs ih =>
    have hv := hρ v (List.mem_cons_self ..)
    have h1 : (actuate π S ξ v).σ = (actuate π S ξ' v).σ := by
      funext x
      simp only [actuate, hσ, hv]
    have h2 : ∀ w ∈ vs, (actuate π S ξ v).ρ w = (actuate π S ξ' v).ρ w := by
      intro w hw
      by_cases hwv : w = v
      · subst hwv; rw [actuate_ρ_self, actuate_ρ_self, hv]
      · rw [actuate_ρ_of_ne π S ξ v w hwv, actuate_ρ_of_ne π S ξ' v w hwv]
        exact hρ w (List.mem_cons_of_mem v hw)
    rw [isLegal_cons, isLegal_cons, hσ, ih _ _ h1 h2]

/-- Completeness of a routing depends only on the rotors at its vertices. -/
theorem isComplete_congr (S : Finset V) (ρ ρ' : Config G) (vs : List V)
    (h : ∀ v ∈ vs, ρ v = ρ' v) :
    IsComplete π S (boundaryInit S ρ) vs ↔ IsComplete π S (boundaryInit S ρ') vs := by
  have hσ : (boundaryInit S ρ).σ = (boundaryInit S ρ').σ := rfl
  unfold IsComplete
  rw [isLegal_congr π S _ _ vs hσ h]
  have := run_σ_congr π S (boundaryInit S ρ) (boundaryInit S ρ') vs hσ h
  unfold Stable
  rw [this]

theorem measurableSet_isComplete [G.LocallyFinite] (S : Finset V) (vs : List V) :
    MeasurableSet {ρ : Config G | IsComplete π S (boundaryInit S ρ) vs} :=
  measurableSet_of_depends vs.toFinset _ (fun ρ ρ' h =>
    isComplete_congr π S ρ ρ' vs (fun v hv => h v (List.mem_toFinset.2 hv)))

theorem measurableSet_terminates [G.LocallyFinite] [Countable V] (S : Finset V) :
    MeasurableSet {ρ : Config G | Terminates π S ρ} := by
  have : {ρ : Config G | Terminates π S ρ} =
      ⋃ vs : List V, {ρ | IsComplete π S (boundaryInit S ρ) vs} := by
    ext ρ; simp [Terminates]
  rw [this]
  exact MeasurableSet.iUnion (fun vs => measurableSet_isComplete π S vs)

theorem measurableSet_allTerminate [G.LocallyFinite] [Countable V] :
    MeasurableSet {ρ : Config G | AllTerminate π ρ} := by
  have : {ρ : Config G | AllTerminate π ρ} =
      ⋂ S : Finset V, ⋂ (_ : S.Nonempty), {ρ | Terminates π S ρ} := by
    ext ρ; simp [AllTerminate]
  rw [this]
  exact MeasurableSet.iInter (fun S => MeasurableSet.iInter (fun _ => measurableSet_terminates π S))

/-! ### The circuit map and the passage time -/

section
variable [G.LocallyFinite] [Countable V]

theorem measurableSet_mem_Φ (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (S : Finset V) (hS : S.Nonempty) (y : V) : MeasurableSet {ρ : Config G | y ∈ Φ π ρ S} := by
  have : {ρ : Config G | y ∈ Φ π ρ S} =
      {ρ | y ∈ S} ∪ ⋃ vs : List V, {ρ | IsComplete π S (boundaryInit S ρ) vs ∧ y ∈ vs} := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion]
    constructor
    · intro h
      rcases mem_Φ_imp π ρ S y h with h | ⟨ws, hws, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨ws, hws, hy⟩
    · rintro (h | ⟨ws, hws, hy⟩)
      · exact subset_Φ π ρ S h
      · exact mem_Φ_of_mem_complete π hAb hG S hS ρ ws hws y hy
  rw [this]
  refine MeasurableSet.union ?_ (MeasurableSet.iUnion (fun vs => ?_))
  · by_cases h : y ∈ S <;> simp [h]
  · by_cases h : y ∈ vs
    · simpa [h] using measurableSet_isComplete π S vs
    · simp [h]

/-- The iterate `Φⁿ({x})`, as a function of the rotors, equals a given finite
set on a measurable event. -/
theorem measurableSet_iterate_eq (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (x : V) (n : ℕ) (S : Finset V) :
    MeasurableSet {ρ : Config G | (Φ π ρ)^[n] {x} = S} := by
  induction n generalizing S with
  | zero =>
    by_cases h : ({x} : Finset V) = S
    · simp [h]
    · simp [h]
  | succ n ih =>
    have : {ρ : Config G | (Φ π ρ)^[n + 1] {x} = S} =
        ⋃ S' : Finset V, {ρ | (Φ π ρ)^[n] {x} = S'} ∩ ⋂ y : V, {ρ | y ∈ Φ π ρ S' ↔ y ∈ S} := by
      ext ρ
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
        Function.iterate_succ_apply']
      constructor
      · intro h
        exact ⟨_, rfl, fun y => by rw [h]⟩
      · rintro ⟨S', hS', hy⟩
        rw [hS']
        ext y
        exact hy y
    rw [this]
    refine MeasurableSet.iUnion (fun S' => (ih S').inter (MeasurableSet.iInter (fun y => ?_)))
    have hS' : S'.Nonempty ∨ S' = ∅ := S'.eq_empty_or_nonempty.symm
    rcases hS' with hS' | rfl
    · have h1 := measurableSet_mem_Φ π hAb hG S' hS' y
      by_cases hyS : y ∈ S
      · have : {ρ : Config G | y ∈ Φ π ρ S' ↔ y ∈ S} = {ρ | y ∈ Φ π ρ S'} := by
          ext ρ; simp [hyS]
        rw [this]; exact h1
      · have : {ρ : Config G | y ∈ Φ π ρ S' ↔ y ∈ S} = {ρ | y ∈ Φ π ρ S'}ᶜ := by
          ext ρ; simp [hyS]
        rw [this]; exact h1.compl
    · -- `Φ ∅ = ∅`: the boundary routing of the empty set is the empty routing
      have : ∀ ρ : Config G, y ∉ Φ π ρ ∅ := by
        intro ρ h
        rcases mem_Φ_imp π ρ ∅ y h with h | ⟨ws, hws, hy⟩
        · simp at h
        · have hleg := hws.1
          cases ws with
          | nil => simp at hy
          | cons v vs =>
            rw [isLegal_cons] at hleg
            have := hleg.2.1
            simp [boundaryInit] at this
      by_cases hyS : y ∈ S <;> simp [this, hyS]

theorem measurableSet_mem_iterate (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (x y : V) (n : ℕ) : MeasurableSet {ρ : Config G | y ∈ (Φ π ρ)^[n] {x}} := by
  have : {ρ : Config G | y ∈ (Φ π ρ)^[n] {x}} =
      ⋃ S : Finset V, ⋃ (_ : y ∈ S), {ρ | (Φ π ρ)^[n] {x} = S} := by
    ext ρ; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨S, hy, hS⟩; rw [hS]; exact hy
  rw [this]
  exact MeasurableSet.iUnion (fun S => MeasurableSet.iUnion (fun _ =>
    measurableSet_iterate_eq π hAb hG x n S))

/-- The passage time is a measurable function of the rotors. -/
theorem measurable_τ (hAb : External.Abelian G) [Infinite V] (hG : G.Connected) (x y : V) :
    Measurable (fun ρ : Config G => τ π ρ x y) := by
  refine measurable_to_countable' (fun n => ?_)
  have : (fun ρ : Config G => τ π ρ x y) ⁻¹' {n} =
      ({ρ | AllTerminate π ρ} ∩ ({ρ | y ∈ (Φ π ρ)^[n] {x}} ∩
        ⋂ m : ℕ, ⋂ (_ : m < n), {ρ | y ∈ (Φ π ρ)^[m] {x}}ᶜ)) ∪
      ({ρ | AllTerminate π ρ}ᶜ ∩ {ρ | G.dist x y = n}) := by
    ext ρ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
    by_cases hall : AllTerminate π ρ
    · simp only [hall, true_and, not_true_eq_false, false_and, or_false]
      rw [τ_of_allTerminate π ρ hall]
      constructor
      · intro h
        have hne : {m : ℕ | y ∈ (Φ π ρ)^[m] {x}}.Nonempty :=
          ⟨G.dist x y, mem_iterate_dist π hG ρ hall x y⟩
        refine ⟨h ▸ Nat.sInf_mem hne, fun m hm hy => ?_⟩
        have := Nat.sInf_le (s := {m : ℕ | y ∈ (Φ π ρ)^[m] {x}}) hy
        omega
      · rintro ⟨hy, hmin⟩
        apply le_antisymm (Nat.sInf_le hy)
        by_contra hlt
        push Not at hlt
        have hne : {m : ℕ | y ∈ (Φ π ρ)^[m] {x}}.Nonempty := ⟨n, hy⟩
        exact hmin _ hlt (Nat.sInf_mem hne)
    · simp only [hall, false_and, not_false_eq_true, true_and, false_or]
      rw [τ_of_not_allTerminate π ρ hall]
  rw [this]
  refine MeasurableSet.union ((measurableSet_allTerminate π).inter
    ((measurableSet_mem_iterate π hAb hG x y n).inter (MeasurableSet.iInter (fun m =>
      MeasurableSet.iInter (fun _ => (measurableSet_mem_iterate π hAb hG x y m).compl)))))
    ((measurableSet_allTerminate π).compl.inter ?_)
  by_cases h : G.dist x y = n <;> simp [h]

end

end Rotor
