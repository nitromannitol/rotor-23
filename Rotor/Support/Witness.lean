/-
The almost-live paths whose failures are all marked (`rotor.tex:1263-1266`): "On
`L_η(u → v, R)`, choose the first witnessing path in a fixed ordering.  Marking all its
failures has conditional probability at least `s^{ηR}`."  Here the witness is chosen
pointwise inside the lower bound of the section, so no measurable selection is needed: the
event that some witness has all its failures marked is measurable as a countable union over
lists, and its section at almost-live rotors contains the marks covering one witness.
-/
import Rotor.Support.BlockField

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

/-- The witnessing property of `L_η(u → v, R)` for a list. -/
def IsWitness (η : ℝ) (u v : V) (R : ℕ) (ρ : Config G) (l : List V) : Prop :=
  IsPath G l ∧ l.head? = some u ∧ l[1]? = some v ∧ (∃ w ∈ l, G.dist u w = R) ∧
    ((liveFailures π ρ l).card : ℝ) ≤ η * R

omit [G.LocallyFinite] in
theorem mem_almostLiveEvent_iff (η : ℝ) (u v : V) (R : ℕ) (ρ : Config G) :
    ρ ∈ almostLiveEvent π η u v R ↔ ∃ l, IsWitness π η u v R ρ l := Iff.rfl

/-- The marks cover the failures of the path `l` at the rotors `ρ`. -/
def CoversFailures (ρ : Config G) (m : V → Bool) (l : List V) : Prop :=
  ∀ i ∈ liveFailures π ρ l, ∀ hi : i < l.length, m (l[i]) = true

/-- The event that some witness of `L_η(u → v, R)` has all its failures marked. -/
def coverEvent (η : ℝ) (u v : V) (R : ℕ) : Set (MPair G) :=
  {p | ∃ l, IsWitness π η u v R p.1 l ∧ CoversFailures π p.1 p.2 l}

/-! ### Measurability -/

omit [G.LocallyFinite] in
/-- The failure set of a path depends only on the rotors at its vertices. -/
theorem liveFailures_congr {ρ ρ' : Config G} {l : List V}
    (h : ∀ (i : ℕ) (hi : i < l.length), ρ (l.get ⟨i, hi⟩) = ρ' (l.get ⟨i, hi⟩)) :
    liveFailures π ρ l = liveFailures π ρ' l := by
  classical
  unfold liveFailures
  exact Finset.filter_congr (fun i _ => by rw [liveAtIndex_congr π (fun hh => h i hh)])

omit [G.LocallyFinite] in
theorem coverEvent_witness_determined (η : ℝ) (u v : V) (R : ℕ) (l : List V) :
    DeterminedByPair (↑l.toFinset)
      {p : MPair G | IsWitness π η u v R p.1 l ∧ CoversFailures π p.1 p.2 l} := by
  rintro p p' hp ⟨⟨hpath, hh, h1, hw, hfail⟩, hcov⟩
  have hl : ∀ (i : ℕ) (hi : i < l.length), p.1 (l.get ⟨i, hi⟩) = p'.1 (l.get ⟨i, hi⟩) :=
    fun i hi => (hp _ (List.mem_toFinset.2 (List.get_mem l ⟨i, hi⟩))).1
  have hfl : liveFailures π p.1 l = liveFailures π p'.1 l := liveFailures_congr π hl
  refine ⟨⟨hpath, hh, h1, hw, by rw [← hfl]; exact hfail⟩, ?_⟩
  intro i hi hi'
  rw [← hfl] at hi
  rw [← (hp _ (List.mem_toFinset.2 (List.getElem_mem hi'))).2]
  exact hcov i hi hi'

theorem coverEvent_measurableSet [Countable V] (η : ℝ) (u v : V) (R : ℕ) :
    MeasurableSet (coverEvent π η u v R) := by
  have : coverEvent π η u v R = ⋃ l : List V,
      {p : MPair G | IsWitness π η u v R p.1 l ∧ CoversFailures π p.1 p.2 l} := by
    ext p; simp [coverEvent]
  rw [this]
  exact MeasurableSet.iUnion (fun l => (coverEvent_witness_determined π η u v R l).measurableSet _)

theorem almostLiveEvent_measurableSet [Countable V] (η : ℝ) (u v : V) (R : ℕ) :
    MeasurableSet (almostLiveEvent π η u v R) := by
  have : almostLiveEvent π η u v R = ⋃ l : List V, {ρ : Config G | IsWitness π η u v R ρ l} := by
    ext ρ; simp [almostLiveEvent, IsWitness]
  rw [this]
  refine MeasurableSet.iUnion (fun l => ?_)
  have hdet : DeterminedBy (↑l.toFinset) {ρ : Config G | IsWitness π η u v R ρ l} := by
    rintro ρ ρ' hρ ⟨hpath, hh, h1, hw, hfail⟩
    refine ⟨hpath, hh, h1, hw, ?_⟩
    rw [← liveFailures_congr π (fun i hi => hρ _ (List.mem_toFinset.2 (List.get_mem l ⟨i, hi⟩)))]
    exact hfail
  exact hdet.measurableSet _

/-! ### The marks lower bound -/

omit [DecidableEq V] [G.LocallyFinite] in
/-- The probability that a finite set of vertices is entirely marked. -/
theorem marksLaw_all (s : NNReal) (hs : s ≤ 1) (F : Finset V) :
    marksLaw s hs {m : V → Bool | ∀ x ∈ F, m x = true} = (s : ℝ≥0∞) ^ F.card := by
  have e : {m : V → Bool | ∀ x ∈ F, m x = true} =
      F.restrict ⁻¹' (Set.pi Set.univ (fun _ : F => ({true} : Set Bool))) := by
    ext m
    simp [Finset.restrict]
  rw [e, marksLaw, ← Measure.map_apply (Finset.measurable_restrict F)
    (MeasurableSet.univ_pi (fun _ => measurableSet_singleton _)), Measure.infinitePi_map_restrict,
    Measure.pi_pi]
  simp only [External.bernoulli, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.bernoulli_apply, Finset.prod_const, Finset.card_univ, Fintype.card_coe, Bool.cond_true]

omit [G.LocallyFinite] in
/-- The marks covering the failures of a witness have probability at least `s^{⌈ηR⌉}`. -/
theorem marksLaw_cover_ge (s : NNReal) (hs : s ≤ 1) {η : ℝ} {u v : V} {R : ℕ} {ρ : Config G}
    {l : List V} (hl : IsWitness π η u v R ρ l) :
    (s : ℝ≥0∞) ^ ⌈η * R⌉₊ ≤ marksLaw s hs {m : V → Bool | CoversFailures π ρ m l} := by
  classical
  set F : Finset V := (liveFailures π ρ l).attach.image
    (fun i => l.getD i.1 u) with hF
  have hsub : {m : V → Bool | ∀ x ∈ F, m x = true} ⊆ {m : V → Bool | CoversFailures π ρ m l} := by
    intro m hm i hi hi'
    have := hm (l[i]) (Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_attach _ _, by
      simp [List.getD_eq_getElem?_getD, hi']⟩)
    exact this
  have hcard : F.card ≤ ⌈η * R⌉₊ := by
    calc F.card ≤ (liveFailures π ρ l).attach.card := Finset.card_image_le
      _ = (liveFailures π ρ l).card := Finset.card_attach
      _ ≤ ⌈η * R⌉₊ := by exact_mod_cast hl.2.2.2.2.trans (Nat.le_ceil _)
  calc (s : ℝ≥0∞) ^ ⌈η * R⌉₊ ≤ (s : ℝ≥0∞) ^ F.card :=
        pow_le_pow_right_of_le_one' (ENNReal.coe_le_one_iff.2 hs) hcard
    _ = marksLaw s hs {m : V → Bool | ∀ x ∈ F, m x = true} := (marksLaw_all s hs F).symm
    _ ≤ marksLaw s hs {m : V → Bool | CoversFailures π ρ m l} := measure_mono hsub

/-- Fubini: the marked cover event has probability at least `s^{⌈ηR⌉}` times the probability
of the almost-live event (`rotor.tex:1263-1266`). -/
theorem mLaw_coverEvent_ge [Countable V] (ν : ∀ v : V, Measure (G.neighborSet v))
    [∀ v, IsProbabilityMeasure (ν v)] (s : NNReal) (hs : s ≤ 1) (η : ℝ) (u v : V) (R : ℕ) :
    (s : ℝ≥0∞) ^ ⌈η * R⌉₊ * productLaw ν (almostLiveEvent π η u v R) ≤
      mLaw ν s hs (coverEvent π η u v R) := by
  unfold mLaw
  rw [Measure.prod_apply (coverEvent_measurableSet π η u v R)]
  have hsec : ∀ ρ ∈ almostLiveEvent π η u v R,
      (s : ℝ≥0∞) ^ ⌈η * R⌉₊ ≤ marksLaw s hs (Prod.mk ρ ⁻¹' coverEvent π η u v R) := by
    intro ρ hρ
    obtain ⟨l, hl⟩ := hρ
    refine (marksLaw_cover_ge π s hs hl).trans (measure_mono ?_)
    intro m hm
    exact ⟨l, hl, hm⟩
  calc (s : ℝ≥0∞) ^ ⌈η * R⌉₊ * productLaw ν (almostLiveEvent π η u v R)
      = ∫⁻ _ in almostLiveEvent π η u v R, (s : ℝ≥0∞) ^ ⌈η * R⌉₊ ∂(productLaw ν) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ ρ in almostLiveEvent π η u v R,
          marksLaw s hs (Prod.mk ρ ⁻¹' coverEvent π η u v R) ∂(productLaw ν) :=
        setLIntegral_mono (measurable_measure_prodMk_left (coverEvent_measurableSet π η u v R)) hsec
    _ ≤ ∫⁻ ρ, marksLaw s hs (Prod.mk ρ ⁻¹' coverEvent π η u v R) ∂(productLaw ν) :=
        setLIntegral_le_lintegral _ _

end Rotor
