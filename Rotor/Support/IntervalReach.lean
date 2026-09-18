import Rotor.Support.IntervalTree

/-!
Proposition 5.1 (`prop:square-passage`), part 5: the reach of one interval.  The interval
starting at `h₀` reaches distance `s` from its root only through a minimal witness, so its
probability is at most `Pm h₀` times the constrained-crossing probability, which Lemma 5.3
bounds by `C e^{-cs}`.  Between consecutive forced tests every test is nonforced.
-/

open Finset MeasureTheory ENNReal Classical

namespace Rotor

/-- The root of the interval starting at `h`: the head of the last tested edge, or `f`. -/
noncomputable def rootOf (f d : Site) (h : List Bool) : Site :=
  match (replay f d h).tested.getLast? with
  | some t => t.2.1
  | none => f

theorem rootOf_nil (f d : Site) : rootOf f d [] = f := by
  simp [rootOf, replay, explInit]

theorem rootOf_append (f d : Site) (h₁ : List Bool) {e : Site × Site} {rest : List (Site × Site)}
    (he : (replay f d h₁).active = e :: rest) (o : Bool) : rootOf f d (h₁ ++ [o]) = e.2 := by
  unfold rootOf
  rw [tested_replay_append_cons f d h₁ he o, List.getLast?_append_of_ne_nil _ (by simp)]
  rfl

/-- The interval after `h₀` reaches distance `s` from its root. -/
def IntReach (f d : Site) (h₀ : List Bool) (s : ℕ) : Set (Config squareGraph) :=
  {ρ | ∃ n, IntervalHist f d h₀ (history ρ f d n) ∧ ∃ g ∈ (explore ρ f d n).visited,
    g ∉ (replay f d h₀).visited ∧ (s : ℤ) ≤ linfDist g (rootOf f d h₀)}

theorem intReach_subset (f : Site) {d : Site} (hd : IsUnit d) {h₀ : List Bool}
    (hs0 : IntervalStart f d h₀ (rootOf f d h₀)) {s : ℕ} (hs : 1 ≤ s) :
    {ρ | history ρ f d h₀.length = h₀} ∩ IntReach f d h₀ s ⊆
      ⋃ h' : {h' // MinWit f d h₀ (rootOf f d h₀) s h'}, {ρ | history ρ f d h'.1.length = h'.1} := by
  rintro ρ ⟨hρ0, n, hI, g, hg, hg0, hdist⟩
  simp only [Set.mem_setOf_eq] at hρ0
  set h' := history ρ f d n with hh'
  have hρ' : history ρ f d h'.length = h' := ((history_eq_iff ρ f d n h').1 hh'.symm).1
  have hex : explore ρ f d h'.length = replay f d h' := by rw [explore_eq_replay, hρ']
  have hg' : g ∈ (replay f d h').visited := by rw [← explore_eq_replay]; exact hg
  obtain ⟨h'', -, hp, hmin⟩ := exists_minWit f hd hs0 hI hex hg' hg0 hs hdist
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨⟨h'', hmin⟩, history_of_prefix f d hp hρ'⟩

/-- The interval reach bound, from the constrained-crossing constants `c, C`. -/
theorem intReach_measure_le (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) {c C : ℝ}
    (hCB : ∀ (x : Site) (r : ℕ), 1 ≤ r →
      bondLaw (1 / 2) half_le_one (constrainedCrossing x r) ≤ ENNReal.ofReal (C * Real.exp (-c * r)))
    {h₀ : List Bool} (hs0 : IntervalStart f d h₀ (rootOf f d h₀)) {s : ℕ} (hs : 1 ≤ s) :
    uniformLaw clockwise ({ρ | history ρ f d h₀.length = h₀} ∩ IntReach f d h₀ s) ≤
      Pm f d h₀ * ENNReal.ofReal (C * Real.exp (-c * s)) := by
  have hdu : IsUnit d := by have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this
  calc uniformLaw clockwise ({ρ | history ρ f d h₀.length = h₀} ∩ IntReach f d h₀ s)
      ≤ uniformLaw clockwise (⋃ h' : {h' // MinWit f d h₀ (rootOf f d h₀) s h'},
          {ρ | history ρ f d h'.1.length = h'.1}) := measure_mono (intReach_subset f hdu hs0 hs)
    _ ≤ ∑' h' : {h' // MinWit f d h₀ (rootOf f d h₀) s h'}, Pm f d h'.1 := measure_iUnion_le _
    _ ≤ Pm f d h₀ * bondLaw (1 / 2) half_le_one (constrainedCrossing (rootOf f d h₀) s) :=
        interval_domination f hd h₀ _ s
    _ ≤ Pm f d h₀ * ENNReal.ofReal (C * Real.exp (-c * s)) := by gcongr; exact hCB _ s hs

/-! ### Between consecutive forced tests -/

theorem forced_take_ge (f d : Site) {h₀ h' : List Bool} (hp : h₀ <+: h') {i : ℕ}
    (hi : h₀.length ≤ i) : (replay f d h₀).forced ≤ (replay f d (h'.take i)).forced :=
  forced_mono_prefix f d (List.prefix_of_prefix_length_le hp (List.take_prefix _ _)
    (by rw [List.length_take]; have := hp.length_le; omega))

/-- Between the `j`-th and the `(j+1)`-st forced tests every test is nonforced. -/
theorem intervalHist_of_minF (f d : Site) {j : ℕ} {h₀ h' : List Bool}
    (hm0 : (replay f d h₀).forced = j) (hm1 : MinF f d (j + 1) h') (hp : h₀ <+: h') :
    IntervalHist f d h₀ h'.dropLast := by
  have hne : h' ≠ [] := by
    intro h; rw [h] at hm1; have := hm1.1; simp [replay, explInit] at this
  have hlen : h'.dropLast.length = h'.length - 1 := List.length_dropLast
  have hp' : h₀ <+: h'.dropLast := by
    refine List.prefix_of_prefix_length_le hp (List.dropLast_prefix _) ?_
    rw [hlen]
    by_contra hlt
    push Not at hlt
    have : h₀ = h' := hp.eq_of_length (by have := hp.length_le; omega)
    subst this
    have := hm1.1; omega
  refine ⟨hp', fun i hi hi' e rest he hW => ?_⟩
  rw [hlen] at hi'
  have htake : h'.dropLast.take i = h'.take i := by
    rw [List.dropLast_eq_take, List.take_take, min_eq_left (by omega)]
  rw [htake] at he hW
  have h1 : (replay f d (h'.take (i + 1))).forced = (replay f d (h'.take i)).forced + 1 := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some]
    rw [forced_append_cons f d _ he, if_pos hW]
  have h2 := forced_take_ge f d hp hi
  have h3 := hm1.2 (i + 1) (by omega)
  omega

/-- The sum over a finite family of next roots reaching distance `s` is at most the
probability of the interval reach. -/
theorem sum_minF_succ_le (f : Site) {d : Site} (hd : IsUnit d) {j : ℕ} {h₀ : List Bool}
    (hm0 : (replay f d h₀).forced = j) {s : ℕ} (F : Finset (List Bool))
    (hF : ∀ h' ∈ F, MinF f d (j + 1) h' ∧ h₀ <+: h' ∧
      ∃ g ∈ (replay f d h'.dropLast).visited, g ∉ (replay f d h₀).visited ∧
        (s : ℤ) ≤ linfDist g (rootOf f d h₀)) :
    ∑ h' ∈ F, Pm f d h' ≤
      uniformLaw clockwise ({ρ | history ρ f d h₀.length = h₀} ∩ IntReach f d h₀ s) := by
  unfold Pm
  rw [← measure_biUnion_finset ?_ (fun h' _ => measurableSet_history_len f hd h')]
  · apply measure_mono
    intro ρ hρ
    simp only [Set.mem_iUnion, exists_prop] at hρ
    obtain ⟨h', hh', hρ'⟩ := hρ
    obtain ⟨hm1, hp, g, hg, hg0, hdist⟩ := hF h' hh'
    simp only [Set.mem_setOf_eq] at hρ'
    refine ⟨history_of_prefix f d hp hρ', h'.length - 1, ?_, g, ?_, hg0, hdist⟩
    · have hd' : history ρ f d (h'.length - 1) = h'.dropLast := by
        have := history_of_prefix f d (List.dropLast_prefix h') hρ'
        rwa [List.length_dropLast] at this
      rw [hd']
      exact intervalHist_of_minF f d hm0 hm1 hp
    · have hd' : history ρ f d (h'.length - 1) = h'.dropLast := by
        have := history_of_prefix f d (List.dropLast_prefix h') hρ'
        rwa [List.length_dropLast] at this
      rw [explore_eq_replay, hd']
      exact hg
  · intro h₁ hh₁ h₂ hh₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ρ h1 h2
    exact hne (minF_unique f d (hF h₁ hh₁).1 (hF h₂ hh₂).1 h1 h2)

end Rotor
