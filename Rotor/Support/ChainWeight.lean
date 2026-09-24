import Rotor.Support.StepProb
import Rotor.Support.BlockField

/-!
Weights of paths and the identity `P{γ is live} = P_e{X_i = x_i for all i}`,
`rotor.tex:1440-1446`: for a path listed most recent first, the probability that it is live
under independent uniform rotors is the product of the step probabilities at its internal
vertices, by independence of the rotors at distinct vertices.
-/

open Finset MeasureTheory ProbabilityTheory

namespace Rotor

section Product

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  [∀ i, MeasurableSingletonClass (X i)] [∀ i, Finite (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- A coordinate event is independent of an event determined by other coordinates. -/
theorem infinitePi_eval_inter (b : ι) (S : Set (X b)) (T : Finset ι) (hb : b ∉ T)
    {E : Set (∀ i, X i)} (hE : DeterminedBy (↑T) E) :
    Measure.infinitePi μ ((fun ω => ω b) ⁻¹' S ∩ E) = μ b S * Measure.infinitePi μ E := by
  classical
  have hind := indepFun_of_disjoint μ {b} T (by simpa using hb)
    (fun x : ∀ i : ({b} : Finset ι), X i => x ⟨b, Finset.mem_singleton_self b⟩)
    (measurable_pi_apply _) id measurable_id
  have hS : MeasurableSet S := (Set.toFinite S).measurableSet
  set B := T.restrict '' E with hBdef
  have hB : MeasurableSet B := (Set.toFinite _).measurableSet
  have h1 := hind.measure_inter_preimage_eq_mul S B hS hB
  have hEeq : T.restrict ⁻¹' B = E := hE.preimage_image T
  change Measure.infinitePi μ ((fun ω => ω b) ⁻¹' S ∩ T.restrict ⁻¹' B) =
    Measure.infinitePi μ ((fun ω => ω b) ⁻¹' S) * Measure.infinitePi μ (T.restrict ⁻¹' B) at h1
  rw [hEeq] at h1
  rw [h1, ← Measure.map_apply (measurable_pi_apply b) hS, Measure.infinitePi_map_eval]

end Product

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

/-- The weight of a path listed most recent first: the product of the step probabilities
at its internal vertices (`P_e{X_i = x_i for all i}`). -/
noncomputable def wt : List V → ℝ
  | c :: b :: a :: rest => pStep π a b c * wt (b :: a :: rest)
  | _ => 1

/-- Live at every internal vertex, for a path listed most recent first. -/
def LiveRev (ρ : Config G) : List V → Prop
  | c :: b :: a :: rest => LiveAt π ρ a b c ∧ LiveRev ρ (b :: a :: rest)
  | _ => True

/-- The internal vertices of a path listed most recent first. -/
def internals : List V → List V
  | _ :: b :: a :: rest => b :: internals (b :: a :: rest)
  | _ => []

@[simp] theorem wt_cons₃ (a b c : V) (rest : List V) :
    wt π (c :: b :: a :: rest) = pStep π a b c * wt π (b :: a :: rest) := rfl

@[simp] theorem wt_nil : wt π ([] : List V) = 1 := rfl
@[simp] theorem wt_single (a : V) : wt π [a] = 1 := rfl
@[simp] theorem wt_pair (a b : V) : wt π [b, a] = 1 := rfl

theorem wt_nonneg : ∀ l : List V, 0 ≤ wt π l
  | c :: b :: a :: rest => mul_nonneg (pStep_nonneg π a b c) (wt_nonneg (b :: a :: rest))
  | [] => zero_le_one
  | [_] => zero_le_one
  | [_, _] => zero_le_one

theorem wt_le_one : ∀ l : List V, wt π l ≤ 1
  | c :: b :: a :: rest => by
    rw [wt_cons₃]
    exact mul_le_one₀ (pStep_le_one π a b c) (wt_nonneg π _) (wt_le_one (b :: a :: rest))
  | [] => le_rfl
  | [_] => le_rfl
  | [_, _] => le_rfl

omit [G.LocallyFinite] in
@[simp] theorem liveRev_cons₃ (ρ : Config G) (a b c : V) (rest : List V) :
    LiveRev π ρ (c :: b :: a :: rest) ↔ LiveAt π ρ a b c ∧ LiveRev π ρ (b :: a :: rest) :=
  Iff.rfl

omit [G.LocallyFinite] in
theorem liveRev_of_length_le_two (ρ : Config G) {l : List V} (hl : l.length ≤ 2) :
    LiveRev π ρ l := by
  match l with
  | [] => trivial
  | [_] => trivial
  | [_, _] => trivial
  | _ :: _ :: _ :: _ => simp at hl

omit [DecidableEq V] in
theorem mem_of_mem_internals : ∀ {l : List V} {v : V}, v ∈ internals (l) → ∃ y ys, l = y :: ys ∧ v ∈ ys
  | _ :: b :: a :: rest, v, hv => by
    simp only [internals, List.mem_cons] at hv
    refine ⟨_, _, rfl, ?_⟩
    rcases hv with rfl | hv
    · exact List.mem_cons_self
    · obtain ⟨y, ys, hys, hmem⟩ := mem_of_mem_internals hv
      simp only [List.cons.injEq] at hys
      obtain ⟨rfl, rfl⟩ := hys
      exact List.mem_cons_of_mem _ hmem
  | [], v, hv => by simp [internals] at hv
  | [_], v, hv => by simp [internals] at hv
  | [_, _], v, hv => by simp [internals] at hv

omit [G.LocallyFinite] in
theorem liveRev_determined (ρ ρ' : Config G) :
    ∀ l : List V, (∀ v ∈ internals l, ρ v = ρ' v) → LiveRev π ρ l → LiveRev π ρ' l
  | c :: b :: a :: rest, h, hl => by
    rw [liveRev_cons₃] at hl ⊢
    refine ⟨(liveAt_congr π (h b (by simp [internals]))).1 hl.1, ?_⟩
    exact liveRev_determined ρ ρ' (b :: a :: rest)
      (fun v hv => h v (by simp [internals, hv])) hl.2
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | [_, _], _, _ => trivial

/-- The event that `l` is live, as a set of configurations. -/
def liveRevSet (l : List V) : Set (Config G) := {ρ | LiveRev π ρ l}

omit [G.LocallyFinite] in
theorem liveRevSet_determined (l : List V) :
    DeterminedBy (↑(internals l).toFinset) (liveRevSet π l) :=
  fun ρ ρ' h hl => liveRev_determined π ρ ρ' l (fun v hv => h v (by simpa using hv)) hl

/-- The initial rotors at `b` for which a path entering from `a` and leaving to `c` is
live at `b`. -/
def liveSet (a b c : V) : Set (G.neighborSet b) :=
  {x | ∃ h : G.Adj b a ∧ G.Adj b c, x ∈ stepSet π b ⟨a, h.1⟩ ⟨c, h.2⟩}

theorem liveAt_iff_mem_liveSet (ρ : Config G) (a b c : V) :
    LiveAt π ρ a b c ↔ ρ b ∈ liveSet π a b c := liveAt_iff π ρ a b c

theorem uniformAt_liveSet (a b c : V) :
    uniformAt π b (liveSet π a b c) = ENNReal.ofReal (pStep π a b c) := by
  by_cases h : G.Adj b a ∧ G.Adj b c
  · have : liveSet π a b c = ↑(stepSet π b ⟨a, h.1⟩ ⟨c, h.2⟩) := by
      ext x
      simp only [liveSet, Set.mem_setOf_eq, Finset.mem_coe]
      exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨h, hx⟩⟩
    rw [this, uniformAt_stepSet π h]
  · have : liveSet π a b c = ∅ := by
      ext x
      simp only [liveSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h', _⟩
      exact h h'
    rw [this, measure_empty, pStep_of_not_adj π h, ENNReal.ofReal_zero]

/-- `P{γ is live} = P_e{X_i = x_i}`: for a path with distinct vertices, listed most recent
first, the probability of being live is its weight. -/
theorem uniformLaw_liveRevSet : ∀ l : List V, l.Nodup →
    uniformLaw π (liveRevSet π l) = ENNReal.ofReal (wt π l)
  | c :: b :: a :: rest, hl => by
    have hsplit : liveRevSet π (c :: b :: a :: rest)
        = (fun ρ : Config G => ρ b) ⁻¹' liveSet π a b c ∩ liveRevSet π (b :: a :: rest) := by
      ext ρ
      simp only [liveRevSet, Set.mem_setOf_eq, liveRev_cons₃, Set.mem_inter_iff, Set.mem_preimage,
        liveAt_iff_mem_liveSet]
    have hb : b ∉ (internals (b :: a :: rest)).toFinset := by
      rw [List.mem_toFinset]
      intro hb
      obtain ⟨y, ys, hys, hmem⟩ := mem_of_mem_internals hb
      simp only [List.cons.injEq] at hys
      obtain ⟨rfl, rfl⟩ := hys
      have := List.nodup_cons.1 (List.nodup_cons.1 hl).2
      exact this.1 hmem
    have hprod := infinitePi_eval_inter (uniformAt π) b (liveSet π a b c) _ hb
      (liveRevSet_determined π (b :: a :: rest))
    rw [hsplit, uniformLaw, productLaw, hprod, ← productLaw, ← uniformLaw, uniformAt_liveSet,
      uniformLaw_liveRevSet (b :: a :: rest) (List.nodup_cons.1 hl).2, wt_cons₃,
      ENNReal.ofReal_mul (pStep_nonneg π a b c)]
  | [], _ => by simp [liveRevSet, LiveRev]
  | [_], _ => by simp [liveRevSet, LiveRev]
  | [_, _], _ => by simp [liveRevSet, LiveRev]

end Rotor
