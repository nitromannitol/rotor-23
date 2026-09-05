/-
`prop:path-reduction` (i) and (ii) (`rotor.tex:1040-1063`):

  "An infinite live path beginning with a directed edge `e` belongs to
   `L_η(e, R)` for every `R`.  Thus the criterion, followed by a countable
   union over the directed edges, rules out all infinite live paths almost
   surely.  Proposition live-recurrence then implies (i).  For part (ii), set
   `a := min{η, 1/2}` and fix distinct vertices `x, y`.  By Lemma
   decreasing-positions (ii), on the probability-one event supplied by part
   (i), `{τ(x,y) ≤ a d_G(x,y)} ⊆ ⋃_{z ∼ x} L_η(x → z, d_G(x,y))`.  Indeed, the
   lemma supplies a path from `x` to `y` with at most `τ(x,y) - 1 ≤ η d_G(x,y)`
   failures of the live condition.  The bounded degree of `G`, the criterion,
   and a union bound give (ii)."
-/
import Rotor.Support.LiveRecurrence
import Rotor.Events

open Finset MeasureTheory Filter Topology
open scoped ENNReal

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-! ### A connected locally finite graph has countably many vertices -/

omit [DecidableEq V] in
theorem countable_of_connected [G.LocallyFinite] (hG : G.Connected) : Countable V := by
  obtain ⟨o⟩ := hG.nonempty
  have : (Set.univ : Set V) ⊆ ⋃ R : ℕ, ball G {o} R := by
    intro v _
    rw [Set.mem_iUnion]
    exact ⟨G.dist o v, o, by simp, le_rfl⟩
  have hc : (Set.univ : Set V).Countable :=
    (Set.countable_iUnion (fun R => (ball_finite hG {o} R).countable)).mono this
  exact Set.countable_univ_iff.1 hc

/-! ### An infinite live path from `e` lies in every `L_η(e, R)` -/

omit [DecidableEq V] in
/-- Along an infinite path from `u` in a connected locally finite graph, the
graph distance from `u` takes every value. -/
theorem exists_dist_eq_of_infPath [G.LocallyFinite] (hG : G.Connected) (x : ℕ → V)
    (hx : IsInfPath G x) (R : ℕ) : ∃ k, G.dist (x 0) (x k) = R := by
  classical
  -- unbounded distances: otherwise the injective `x` lands in a finite ball
  have hunb : ∃ k, R ≤ G.dist (x 0) (x k) := by
    by_contra hcon
    push_neg at hcon
    have hsub : Set.range x ⊆ ball G {x 0} R := by
      rintro _ ⟨k, rfl⟩
      exact ⟨x 0, by simp, (hcon k).le⟩
    have hfin : (Set.range x).Finite := (ball_finite hG {x 0} R).subset hsub
    exact Set.infinite_range_of_injective hx.1 hfin
  -- the first index at distance `≥ R`
  refine ⟨Nat.find hunb, le_antisymm ?_ (Nat.find_spec hunb)⟩
  rcases Nat.eq_zero_or_pos (Nat.find hunb) with h0 | hpos
  · rw [h0]; simp
  · have hprev : G.dist (x 0) (x (Nat.find hunb - 1)) < R := by
      have := Nat.find_min hunb (m := Nat.find hunb - 1) (by omega)
      omega
    have hadj : G.Adj (x (Nat.find hunb - 1)) (x (Nat.find hunb)) := by
      have := hx.2 (Nat.find hunb - 1)
      rwa [Nat.sub_add_cancel hpos] at this
    have htri := hG.dist_triangle (u := x 0) (v := x (Nat.find hunb - 1)) (w := x (Nat.find hunb))
    rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj] at htri
    omega

/-- The infinite live paths starting with the directed edge `u → v`. -/
def InfLiveFrom (ρ : Config G) (u v : V) : Prop :=
  ∃ x : ℕ → V, IsInfPath G x ∧ IsInfLive π ρ x ∧ x 0 = u ∧ x 1 = v

theorem infLiveFrom_subset [G.LocallyFinite] (hG : G.Connected) (η : ℝ) (hη : 0 ≤ η) (u v : V)
    (R : ℕ) (hR : 1 ≤ R) : {ρ | InfLiveFrom π ρ u v} ⊆ almostLiveEvent π η u v R := by
  intro ρ ⟨x, hx, hlive, hu, hv⟩
  obtain ⟨k, hk⟩ := exists_dist_eq_of_infPath hG x hx R
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    subst this
    simp at hk; omega
  refine ⟨(List.range (k + 1)).map x, ⟨?_, ?_⟩, ?_, ?_,
    ⟨x k, List.mem_map_of_mem (List.mem_range.2 (by omega)), hu ▸ hk⟩, ?_⟩
  · exact List.Nodup.map hx.1 List.nodup_range
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    simpa using hx.2 i
  · rw [List.range_succ_eq_map]; simp [hu]
  · rw [List.getElem?_map, List.getElem?_range (by omega)]; simp [hv]
  · -- no failures: the path is live everywhere
    have : liveFailures π ρ ((List.range (k + 1)).map x) = ∅ := by
      classical
      unfold liveFailures
      rw [Finset.filter_eq_empty_iff]
      intro i _ ⟨hi0, hi1, hnl⟩
      apply hnl
      refine ⟨⟨hi0, hi1⟩, ?_⟩
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
      have := hlive (i - 1)
      rwa [Nat.sub_add_cancel hi0, show i - 1 + 2 = i + 1 by omega] at this
    rw [this]
    simp
    positivity

/-! ### Almost surely there is no infinite live path -/

theorem measure_infLiveFrom_eq_zero [G.LocallyFinite] (hG : G.Connected)
    (μ : Measure (Config G)) (η : ℝ) (hη : 0 < η) (hcrit : Criterion π μ η) (e : G.Dart) :
    μ {ρ | InfLiveFrom π ρ e.fst e.snd} = 0 := by
  have hle : ∀ᶠ R : ℕ in atTop, μ {ρ | InfLiveFrom π ρ e.fst e.snd} ≤
      ⨆ e' : G.Dart, μ (almostLiveEvent π η e'.fst e'.snd R) := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun R hR => ?_⟩
    exact (measure_mono (infLiveFrom_subset π hG η hη.le _ _ R hR)).trans
      (le_iSup (fun e' : G.Dart => μ (almostLiveEvent π η e'.fst e'.snd R)) e)
  exact le_antisymm (ge_of_tendsto hcrit hle) (zero_le _)

theorem ae_no_infLivePath [G.LocallyFinite] (hG : G.Connected) (μ : Measure (Config G))
    (η : ℝ) (hη : 0 < η) (hcrit : Criterion π μ η) : ∀ᵐ ρ ∂μ, ¬ HasInfLivePath π ρ := by
  haveI := countable_of_connected hG
  haveI : Countable G.Dart := SimpleGraph.Dart.toProd_injective.countable
  rw [ae_iff]
  simp only [not_not]
  have hsub : {ρ | HasInfLivePath π ρ} ⊆ ⋃ e : G.Dart, {ρ | InfLiveFrom π ρ e.fst e.snd} := by
    rintro ρ ⟨x, hx, hlive⟩
    rw [Set.mem_iUnion]
    exact ⟨⟨(x 0, x 1), hx.2 0⟩, x, hx, hlive, rfl, rfl⟩
  exact measure_mono_null hsub
    (measure_iUnion_null (fun e => measure_infLiveFrom_eq_zero π hG μ η hη hcrit e))

/-- `prop:path-reduction` (i). -/
theorem path_reduction_i [G.LocallyFinite] (hFLP : External.OneCircuit G)
    (hAb : External.Abelian G) (hHP : External.VisitsAllOfVisitsOne G) [Infinite V]
    (hG : G.Connected) (μ : Measure (Config G)) (η : ℝ) (hη : 0 < η) (hcrit : Criterion π μ η) :
    ∀ᵐ ρ ∂μ, AllTerminate π ρ ∧ ∀ o : V, Recurrent π ρ o := by
  filter_upwards [ae_no_infLivePath π hG μ η hη hcrit] with ρ hρ
  obtain ⟨o⟩ := hG.nonempty
  exact ⟨(live_recurrence_proof π hFLP hAb hHP hG ρ o hρ).1,
    fun o => (live_recurrence_proof π hFLP hAb hHP hG ρ o hρ).2.2⟩

/-! ### Fast passage forces an almost-live path -/

theorem fast_passage_subset [G.LocallyFinite] (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (ρ : Config G) (hall : AllTerminate π ρ) (η a : ℝ) (ha : a ≤ η)
    (x y : V) (hxy : x ≠ y) (hτ : (τ π ρ x y : ℝ) ≤ a * G.dist x y) :
    ρ ∈ ⋃ z ∈ G.neighborFinset x, almostLiveEvent π η x z (G.dist x y) := by
  have hy := mem_iterate_τ π hG ρ hall x y
  have hn1 : 1 ≤ τ π ρ x y := by
    by_contra h0
    have h0' : τ π ρ x y = 0 := by omega
    rw [h0'] at hy
    simp at hy
    exact hxy hy.symm
  have hdef : IteratesDefined π ρ {x} (τ π ρ x y) :=
    fun i _ => hall _ (nonempty_Φ_iterate π ρ {x} (by simp) i)
  obtain ⟨l, hpath, hhead, hlast, -, hfail⟩ :=
    decreasing_positions_ii π hAb hG ρ x (τ π ρ x y) y hdef hy
  -- `l = x :: z :: rest`
  obtain ⟨z, rest, hl⟩ : ∃ z rest, l = x :: z :: rest := by
    cases l with
    | nil => simp at hhead
    | cons a l' =>
      simp only [List.head?_cons, Option.some_inj] at hhead
      subst hhead
      cases l' with
      | nil => simp at hlast; exact absurd hlast hxy
      | cons z rest => exact ⟨z, rest, rfl⟩
  have hadj : G.Adj x z := by
    have := hpath.2
    rw [hl, List.isChain_cons] at this
    exact this.1 z rfl
  rw [Set.mem_iUnion₂]
  refine ⟨z, (G.mem_neighborFinset x z).2 hadj, l, hpath, hhead, by rw [hl]; rfl,
    ⟨y, List.mem_of_mem_getLast? hlast, rfl⟩, ?_⟩
  have hd : (0 : ℝ) ≤ G.dist x y := by positivity
  have h1 : ((liveFailures π ρ l).card : ℝ) ≤ (τ π ρ x y : ℝ) := by
    exact_mod_cast (hfail.trans (Nat.sub_le _ _))
  calc ((liveFailures π ρ l).card : ℝ) ≤ τ π ρ x y := h1
    _ ≤ a * G.dist x y := hτ
    _ ≤ η * G.dist x y := mul_le_mul_of_nonneg_right ha hd

/-- `prop:path-reduction` (ii). -/
theorem path_reduction_ii [G.LocallyFinite] (hFLP : External.OneCircuit G)
    (hAb : External.Abelian G) (hHP : External.VisitsAllOfVisitsOne G) [Infinite V]
    (hG : G.Connected) (hdeg : ∃ D : ℕ, ∀ v, G.degree v ≤ D) (μ : Measure (Config G))
    (η : ℝ) (hη : 0 < η) (hcrit : Criterion π μ η) :
    ∃ a : ℝ, 0 < a ∧ Tendsto (fun R : ℕ => ⨆ (x : V) (y : V) (_ : R ≤ G.dist x y),
      μ {ρ | (τ π ρ x y : ℝ) ≤ a * G.dist x y}) atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := hdeg
  refine ⟨min η (1 / 2), lt_min hη (by norm_num), ?_⟩
  have hnull : μ {ρ | ¬ AllTerminate π ρ} = 0 := by
    have := path_reduction_i π hFLP hAb hHP hG μ η hη hcrit
    rw [ae_iff] at this
    refine measure_mono_null (s := {ρ | ¬ AllTerminate π ρ}) ?_ this
    intro ρ (hρ : ¬ AllTerminate π ρ) (h : AllTerminate π ρ ∧ ∀ o, Recurrent π ρ o)
    exact hρ h.1
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have hDpos : (0 : ℝ≥0∞) < (D : ℝ≥0∞) + 1 := by positivity
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 hcrit (ε / ((D : ℝ≥0∞) + 1))
    (ENNReal.div_pos hε.ne' (by simp))
  refine ⟨max N 1, fun R hR => ?_⟩
  refine iSup₂_le (fun x y => iSup_le (fun hxy => ?_))
  have hne : x ≠ y := by
    intro h
    subst h
    simp at hxy
    omega
  have hdR : N ≤ G.dist x y := le_trans (le_max_left N 1) (hR.trans hxy)
  calc μ {ρ | (τ π ρ x y : ℝ) ≤ min η (1 / 2) * G.dist x y}
      ≤ μ ({ρ | ¬ AllTerminate π ρ} ∪
          ⋃ z ∈ G.neighborFinset x, almostLiveEvent π (η) x z (G.dist x y)) := by
        refine measure_mono (fun ρ hρ => ?_)
        by_cases hall : AllTerminate π ρ
        · exact Or.inr (fast_passage_subset π hAb hG ρ hall η _ (min_le_left _ _) x y hne hρ)
        · exact Or.inl hall
    _ ≤ μ {ρ | ¬ AllTerminate π ρ} +
          μ (⋃ z ∈ G.neighborFinset x, almostLiveEvent π η x z (G.dist x y)) :=
        measure_union_le _ _
    _ ≤ 0 + ∑ z ∈ G.neighborFinset x, μ (almostLiveEvent π η x z (G.dist x y)) :=
        add_le_add (le_of_eq hnull) (measure_biUnion_finset_le _ _)
    _ ≤ ∑ z ∈ G.neighborFinset x, ε / ((D : ℝ≥0∞) + 1) := by
        rw [zero_add]
        refine Finset.sum_le_sum (fun z hz => ?_)
        have hadj : G.Adj x z := (G.mem_neighborFinset x z).1 hz
        refine le_trans (le_iSup (fun e : G.Dart => μ (almostLiveEvent π η e.fst e.snd (G.dist x y)))
          ⟨(x, z), hadj⟩) (hN _ hdR)
    _ = (G.degree x : ℝ≥0∞) * (ε / ((D : ℝ≥0∞) + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ ((D : ℝ≥0∞) + 1) * (ε / ((D : ℝ≥0∞) + 1)) := by
        gcongr
        exact_mod_cast (hD x).trans (Nat.le_succ D)
    _ ≤ ε := ENNReal.mul_div_le

end Rotor
