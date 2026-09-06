/-
The marked configurations of the proof of `lem:block-live-paths` (`rotor.tex:1252-1262`):
"Under `P̂`, let the initial rotors be independent with laws `ν̃_x`, and mark each vertex
independently with probability `s`."  Part one: events determined by finitely many
coordinates, independence under a pushforward, the pair space of rotors and marks, and the
independence of functions of disjoint coordinate sets on it.
-/
import Rotor.Support.BlockGeom
import Rotor.Support.ProductTools
import Rotor.Support.TVTools
import Rotor.Events
import Rotor.External.LSS

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Rotor

/-! ### Events determined by finitely many coordinates -/

section Determined

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- `E` depends only on the coordinates in `S`. -/
def DeterminedBy (S : Set ι) (E : Set (∀ i, X i)) : Prop :=
  ∀ ω ω' : ∀ i, X i, (∀ i ∈ S, ω i = ω' i) → ω ∈ E → ω' ∈ E

omit [∀ i, MeasurableSpace (X i)] in
theorem DeterminedBy.mono {S T : Set ι} (hST : S ⊆ T) {E : Set (∀ i, X i)}
    (h : DeterminedBy S E) : DeterminedBy T E :=
  fun ω ω' hω => h ω ω' (fun i hi => hω i (hST hi))

omit [∀ i, MeasurableSpace (X i)] in
theorem DeterminedBy.preimage_image (S : Finset ι) {E : Set (∀ i, X i)}
    (h : DeterminedBy (↑S) E) : S.restrict ⁻¹' (S.restrict '' E) = E := by
  ext ω
  constructor
  · rintro ⟨ω', hω', hr⟩
    exact h ω' ω (fun i hi => congrFun hr ⟨i, hi⟩) hω'
  · intro hω
    exact ⟨ω, hω, rfl⟩

theorem DeterminedBy.measurableSet [∀ i, MeasurableSingletonClass (X i)] [∀ i, Finite (X i)]
    (S : Finset ι) {E : Set (∀ i, X i)} (h : DeterminedBy (↑S) E) : MeasurableSet E := by
  rw [← h.preimage_image S]
  exact (Finset.measurable_restrict S) (Set.toFinite _).measurableSet

omit [∀ i, MeasurableSpace (X i)] in
theorem DeterminedBy.mem_iff (S : Finset ι) {E : Set (∀ i, X i)} (h : DeterminedBy (↑S) E)
    (ω : ∀ i, X i) : ω ∈ E ↔ S.restrict ω ∈ S.restrict '' E := by
  conv_lhs => rw [← h.preimage_image S]
  rfl

end Determined

/-! ### Independence under a pushforward -/

theorem indepFun_map_of {Ω Ω' β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure Ω) {ψ : Ω → Ω'} (hψ : Measurable ψ)
    {f : Ω' → β} {g : Ω' → γ} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun (f ∘ ψ) (g ∘ ψ) μ) : IndepFun f g (μ.map ψ) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  rw [Measure.map_apply hψ (hf hs), Measure.map_apply hψ (hg ht),
    Measure.map_apply hψ ((hf hs).inter (hg ht))]
  exact h s t hs ht

/-! ### The pair space of rotors and marks -/

section Pair

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {Y : ι → Type*}
  [∀ i, MeasurableSpace (Y i)]

/-- Restriction of a pair of configurations to the coordinates in `S`. -/
def restrPair (S : Finset ι) (p : (∀ i, X i) × (∀ i, Y i)) :
    (∀ i : S, X i) × (∀ i : S, Y i) :=
  (S.restrict p.1, S.restrict p.2)

theorem measurable_restrPair (S : Finset ι) : Measurable (restrPair (X := X) (Y := Y) S) :=
  ((Finset.measurable_restrict S).comp measurable_fst).prodMk
    ((Finset.measurable_restrict S).comp measurable_snd)

variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
  (κ : ∀ i, Measure (Y i)) [∀ i, IsProbabilityMeasure (κ i)]

/-- Under the product of two product laws, functions of the pair restricted to disjoint finite
coordinate sets are independent. -/
theorem indepFun_restrPair (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun (restrPair S) (restrPair T) ((Measure.infinitePi μ).prod (Measure.infinitePi κ)) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  -- the sections in the rotor variable, for a fixed mark configuration
  let secA : (∀ i : S, Y i) → Set (∀ i : S, X i) := fun r' => (fun r => (r, r')) ⁻¹' A
  let secB : (∀ i : T, Y i) → Set (∀ i : T, X i) := fun r' => (fun r => (r, r')) ⁻¹' B
  have hsecA : ∀ r', MeasurableSet (secA r') := fun r' => (measurable_id.prodMk measurable_const) hA
  have hsecB : ∀ r', MeasurableSet (secB r') := fun r' => (measurable_id.prodMk measurable_const) hB
  let f : (∀ i : S, Y i) → ℝ≥0∞ := fun r' => Measure.infinitePi μ (S.restrict ⁻¹' secA r')
  let g : (∀ i : T, Y i) → ℝ≥0∞ := fun r' => Measure.infinitePi μ (T.restrict ⁻¹' secB r')
  have hf : Measurable f := by
    have : f = fun r' => (Measure.infinitePi μ).map S.restrict ((fun r => (r, r')) ⁻¹' A) := by
      funext r'
      rw [Measure.map_apply (Finset.measurable_restrict S) (hsecA r')]
    rw [this]
    exact measurable_measure_prodMk_right hA
  have hg : Measurable g := by
    have : g = fun r' => (Measure.infinitePi μ).map T.restrict ((fun r => (r, r')) ⁻¹' B) := by
      funext r'
      rw [Measure.map_apply (Finset.measurable_restrict T) (hsecB r')]
    rw [this]
    exact measurable_measure_prodMk_right hB
  -- independence of the two restrictions under each product law
  have hindX := (iIndepFun_eval_infinitePi μ).indepFun_finset S T hST (fun i => measurable_pi_apply i)
  have hindY := (iIndepFun_eval_infinitePi κ).indepFun_finset S T hST (fun i => measurable_pi_apply i)
  have hXA : ∀ m : ∀ i, Y i, Measure.infinitePi μ
      ((fun ρ => (S.restrict ρ, S.restrict m)) ⁻¹' A ∩ (fun ρ => (T.restrict ρ, T.restrict m)) ⁻¹' B) =
      f (S.restrict m) * g (T.restrict m) := by
    intro m
    have := (indepFun_iff_measure_inter_preimage_eq_mul.1 hindX) (secA (S.restrict m))
      (secB (T.restrict m)) (hsecA _) (hsecB _)
    exact this
  -- the three product measures as integrals over the marks
  have hmeasS : MeasurableSet (restrPair S ⁻¹' A) := measurable_restrPair S hA
  have hmeasT : MeasurableSet (restrPair T ⁻¹' B) := measurable_restrPair T hB
  rw [Measure.prod_apply_symm (hmeasS.inter hmeasT), Measure.prod_apply_symm hmeasS,
    Measure.prod_apply_symm hmeasT]
  have e1 : (fun m => Measure.infinitePi μ ((fun ρ => (ρ, m)) ⁻¹' (restrPair S ⁻¹' A ∩ restrPair T ⁻¹' B))) =
      fun m => f (S.restrict m) * g (T.restrict m) := by
    funext m
    rw [← hXA m]
    rfl
  have e2 : (fun m => Measure.infinitePi μ ((fun ρ => (ρ, m)) ⁻¹' (restrPair S ⁻¹' A))) =
      fun m => f (S.restrict m) := by
    funext m
    rfl
  have e3 : (fun m => Measure.infinitePi μ ((fun ρ => (ρ, m)) ⁻¹' (restrPair T ⁻¹' B))) =
      fun m => g (T.restrict m) := by
    funext m
    rfl
  rw [e1, e2, e3]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hf.comp (Finset.measurable_restrict S))
    (hg.comp (Finset.measurable_restrict T)) (hindY.comp hf hg)

end Pair

/-! ### Events on the pair space determined by finitely many coordinates -/

section DeterminedPair

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {Y : ι → Type*}
  [∀ i, MeasurableSpace (Y i)]

/-- `E` depends only on the coordinates in `S` of both components. -/
def DeterminedByPair (S : Set ι) (E : Set ((∀ i, X i) × (∀ i, Y i))) : Prop :=
  ∀ p p' : (∀ i, X i) × (∀ i, Y i), (∀ i ∈ S, p.1 i = p'.1 i ∧ p.2 i = p'.2 i) → p ∈ E → p' ∈ E

omit [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] in
theorem DeterminedByPair.mono {S T : Set ι} (hST : S ⊆ T) {E : Set ((∀ i, X i) × (∀ i, Y i))}
    (h : DeterminedByPair S E) : DeterminedByPair T E :=
  fun p p' hp => h p p' (fun i hi => hp i (hST hi))

omit [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] in
theorem DeterminedByPair.preimage_image (S : Finset ι) {E : Set ((∀ i, X i) × (∀ i, Y i))}
    (h : DeterminedByPair (↑S) E) : restrPair S ⁻¹' (restrPair S '' E) = E := by
  ext p
  constructor
  · rintro ⟨p', hp', hr⟩
    have h1 : S.restrict p'.1 = S.restrict p.1 := congrArg Prod.fst hr
    have h2 : S.restrict p'.2 = S.restrict p.2 := congrArg Prod.snd hr
    exact h p' p (fun i hi => ⟨congrFun h1 ⟨i, hi⟩, congrFun h2 ⟨i, hi⟩⟩) hp'
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem DeterminedByPair.measurableSet [∀ i, MeasurableSingletonClass (X i)] [∀ i, Finite (X i)]
    [∀ i, MeasurableSingletonClass (Y i)] [∀ i, Finite (Y i)] (S : Finset ι)
    {E : Set ((∀ i, X i) × (∀ i, Y i))} (h : DeterminedByPair (↑S) E) : MeasurableSet E := by
  rw [← h.preimage_image S]
  exact measurable_restrPair S (Set.toFinite _).measurableSet

omit [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] in
theorem DeterminedByPair.mem_iff (S : Finset ι) {E : Set ((∀ i, X i) × (∀ i, Y i))}
    (h : DeterminedByPair (↑S) E) (p : (∀ i, X i) × (∀ i, Y i)) :
    p ∈ E ↔ restrPair S p ∈ restrPair S '' E := by
  conv_lhs => rw [← h.preimage_image S]
  rfl

end DeterminedPair

/-! ### Live paths depend only on the rotors at their internal vertices -/

section Congr

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

omit [G.LocallyFinite] in
theorem rank_congr {ρ ρ' : Config G} (v : V) (h : ρ v = ρ' v) (w : G.neighborSet v) :
    rank π ρ v w = rank π ρ' v w := by
  unfold rank
  apply le_antisymm
  · exact Nat.find_le ⟨(Nat.find_spec (rank_exists π ρ' v w)).1, by
      rw [h]; exact (Nat.find_spec (rank_exists π ρ' v w)).2⟩
  · exact Nat.find_le ⟨(Nat.find_spec (rank_exists π ρ v w)).1, by
      rw [← h]; exact (Nat.find_spec (rank_exists π ρ v w)).2⟩

omit [G.LocallyFinite] in
theorem liveAt_congr {ρ ρ' : Config G} {u v w : V} (h : ρ v = ρ' v) :
    LiveAt π ρ u v w ↔ LiveAt π ρ' u v w := by
  unfold LiveAt rank'
  constructor
  · rintro ⟨hw, hu, hlt⟩
    exact ⟨hw, hu, by rw [← rank_congr π v h, ← rank_congr π v h]; exact hlt⟩
  · rintro ⟨hw, hu, hlt⟩
    exact ⟨hw, hu, by rw [rank_congr π v h, rank_congr π v h]; exact hlt⟩

omit [G.LocallyFinite] in
theorem liveAtIndex_congr {ρ ρ' : Config G} {l : List V} {i : ℕ}
    (h : ∀ hi : i < l.length, ρ (l.get ⟨i, hi⟩) = ρ' (l.get ⟨i, hi⟩)) :
    LiveAtIndex π ρ l i ↔ LiveAtIndex π ρ' l i := by
  unfold LiveAtIndex
  constructor
  · rintro ⟨hh, hl⟩
    exact ⟨hh, (liveAt_congr π (h (by omega))).1 hl⟩
  · rintro ⟨hh, hl⟩
    exact ⟨hh, (liveAt_congr π (h (by omega))).2 hl⟩

omit [G.LocallyFinite] in
theorem isLive_congr {ρ ρ' : Config G} {l : List V}
    (h : ∀ (i : ℕ) (hi : i < l.length), 0 < i → i + 1 < l.length →
      ρ (l.get ⟨i, hi⟩) = ρ' (l.get ⟨i, hi⟩)) :
    IsLive π ρ l ↔ IsLive π ρ' l := by
  unfold IsLive
  constructor
  · intro hl i hi hi'
    exact (liveAtIndex_congr π (fun hh => h i hh hi hi')).1 (hl i hi hi')
  · intro hl i hi hi'
    exact (liveAtIndex_congr π (fun hh => h i hh hi hi')).2 (hl i hi hi')

omit [G.LocallyFinite] in
/-- The block event depends only on the rotors in `Q_z⁺`. -/
theorem blockEvent_determined (P : DoublyPeriodic G) (L : ℕ) (z : ℤ × ℤ) :
    DeterminedBy (P.blockPlus L z) (blockEvent π P L z) := by
  rintro ρ ρ' hρ ⟨l, hpath, hlive, hstart, hstay, hlast⟩
  refine ⟨l, hpath, ?_, hstart, hstay, hlast⟩
  exact (isLive_congr π (fun i hi hi0 hi1 => hρ _ (hstay i hi1))).1 hlive

end Congr

/-! ### Live paths with marks -/

section Marked

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

/-- A configuration of rotors together with marks. -/
abbrev MPair (G : SimpleGraph V) := Config G × (V → Bool)

/-- The path is live at every unmarked internal vertex. -/
def IsLiveUnmarked (p : MPair G) (l : List V) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < l.length), 0 < i →
    p.2 (l.get ⟨i, by omega⟩) = true ∨ LiveAtIndex π p.1 l i

/-- The event `E_z`: a path crosses `Q_z⁺` as in `C_z` and is live at every unmarked internal
vertex (`rotor.tex:1256-1257`). -/
def markedBlockEvent (P : DoublyPeriodic G) (L : ℕ) (z : ℤ × ℤ) : Set (MPair G) :=
  {p | ∃ l : List V, IsPath G l ∧ IsLiveUnmarked π p l ∧
    (∃ h : 0 < l.length, l.get ⟨0, h⟩ ∈ P.block L z) ∧
    (∀ (i : ℕ) (h : i + 1 < l.length), l.get ⟨i, by omega⟩ ∈ P.blockPlus L z) ∧
    (∀ y ∈ l.getLast?, y ∉ P.blockPlus L z)}

omit [G.LocallyFinite] in
theorem markedBlockEvent_determined (P : DoublyPeriodic G) (L : ℕ) (z : ℤ × ℤ) :
    DeterminedByPair (P.blockPlus L z) (markedBlockEvent π P L z) := by
  rintro p p' hp ⟨l, hpath, hlive, hstart, hstay, hlast⟩
  refine ⟨l, hpath, ?_, hstart, hstay, hlast⟩
  intro i hi hi0
  rcases hlive i hi hi0 with hm | hl
  · left
    rw [← (hp _ (hstay i hi)).2]
    exact hm
  · right
    exact (liveAtIndex_congr π (fun hh => (hp _ (hstay i hi)).1)).1 hl

omit [G.LocallyFinite] in
/-- Without marks in `Q_z⁺`, the marked event is the block event of the rotors. -/
theorem blockEvent_of_marked (P : DoublyPeriodic G) (L : ℕ) (z : ℤ × ℤ) {p : MPair G}
    (hp : p ∈ markedBlockEvent π P L z) (hm : ∀ v ∈ P.blockPlus L z, p.2 v = false) :
    p.1 ∈ blockEvent π P L z := by
  obtain ⟨l, hpath, hlive, hstart, hstay, hlast⟩ := hp
  refine ⟨l, hpath, ?_, hstart, hstay, hlast⟩
  intro i hi0 hi
  rcases hlive i hi hi0 with hmark | hl
  · rw [hm _ (hstay i hi)] at hmark
    exact absurd hmark Bool.false_ne_true
  · exact hl

end Marked

/-! ### The law of the marked configurations and the one-site bound -/

section MarkedLaw

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

/-- Independent marks with probability `s` at every vertex. -/
noncomputable def marksLaw (s : NNReal) (hs : s ≤ 1) : Measure (V → Bool) :=
  Measure.infinitePi (fun _ : V => External.bernoulli s hs)

instance (s : NNReal) (hs : s ≤ 1) : IsProbabilityMeasure (marksLaw (V := V) s hs) := by
  unfold marksLaw; infer_instance

/-- The law `P̂`: independent rotors with laws `ν`, independent marks with probability `s`. -/
noncomputable def mLaw (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)]
    (s : NNReal) (hs : s ≤ 1) : Measure (MPair G) :=
  (productLaw ν).prod (marksLaw s hs)

instance (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)] (s : NNReal)
    (hs : s ≤ 1) : IsProbabilityMeasure (mLaw ν s hs) := by
  unfold mLaw; infer_instance

omit [DecidableEq V] [G.LocallyFinite] in
theorem mLaw_fst (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)]
    (s : NNReal) (hs : s ≤ 1) {C : Set (Config G)} (hC : MeasurableSet C) :
    mLaw ν s hs (Prod.fst ⁻¹' C) = productLaw ν C := by
  unfold mLaw
  rw [← Measure.map_apply measurable_fst hC, Measure.map_fst_prod, measure_univ, one_smul]

omit [DecidableEq V] [G.LocallyFinite] in
set_option linter.deprecated false in
theorem marksLaw_mark (s : NNReal) (hs : s ≤ 1) (v : V) :
    marksLaw s hs {m : V → Bool | m v = true} = s := by
  unfold marksLaw
  have : {m : V → Bool | m v = true} = (fun m : V → Bool => m v) ⁻¹' {true} := rfl
  rw [this, ← Measure.map_apply (measurable_pi_apply v) (measurableSet_singleton _),
    Measure.infinitePi_map_eval, External.bernoulli,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.bernoulli_apply]
  rfl

omit [DecidableEq V] [G.LocallyFinite] in
theorem mLaw_mark (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)]
    (s : NNReal) (hs : s ≤ 1) (v : V) :
    mLaw ν s hs {p : MPair G | p.2 v = true} = s := by
  unfold mLaw
  have : {p : MPair G | p.2 v = true} = Prod.snd ⁻¹' {m : V → Bool | m v = true} := rfl
  have hmeas : MeasurableSet {m : V → Bool | m v = true} := by
    have e : {m : V → Bool | m v = true} = (fun m : V → Bool => m v) ⁻¹' {true} := rfl
    rw [e]
    exact measurable_pi_apply v (measurableSet_singleton true)
  rw [this, ← Measure.map_apply measurable_snd hmeas, Measure.map_snd_prod, measure_univ, one_smul,
    marksLaw_mark]

omit [DecidableEq V] [G.LocallyFinite] in
/-- The union bound for the marks in a finite set. -/
theorem mLaw_marks_le (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)]
    (s : NNReal) (hs : s ≤ 1) (S : Finset V) :
    mLaw ν s hs (⋃ v ∈ S, {p : MPair G | p.2 v = true}) ≤ S.card * s := by
  refine (measure_biUnion_finset_le S _).trans (le_of_eq ?_)
  simp only [mLaw_mark, Finset.sum_const, nsmul_eq_mul]

end MarkedLaw

/-! ### The block field, its `2`-dependence, and domination -/

section Field

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G) (L : ℕ)

/-- `Q_z⁺` as a finset. -/
noncomputable def blockPlusFin (z : ℤ × ℤ) : Finset V := (P.blockPlus_finite L z).toFinset

omit [DecidableEq V] [G.LocallyFinite] in
theorem coe_blockPlusFin (z : ℤ × ℤ) : (↑(blockPlusFin P L z) : Set V) = P.blockPlus L z :=
  Set.Finite.coe_toFinset _

theorem blockEvent_measurableSet (z : ℤ × ℤ) : MeasurableSet (blockEvent π P L z) := by
  have h := blockEvent_determined π P L z
  rw [← coe_blockPlusFin P L z] at h
  exact h.measurableSet _

theorem markedBlockEvent_measurableSet (z : ℤ × ℤ) :
    MeasurableSet (markedBlockEvent π P L z) := by
  have h := markedBlockEvent_determined π P L z
  rw [← coe_blockPlusFin P L z] at h
  exact h.measurableSet _

open Classical in
/-- The `{0,1}`-field `(1_{E_z})_{z ∈ ℤ²}` (`rotor.tex:1258-1260`). -/
noncomputable def blockField (p : MPair G) : ℤ × ℤ → Bool :=
  fun z => decide (p ∈ markedBlockEvent π P L z)

open Classical in
theorem measurable_blockField : Measurable (blockField π P L) := by
  refine measurable_pi_lambda _ (fun z => ?_)
  refine measurable_to_countable' (fun b => ?_)
  cases b
  · have : (fun c : MPair G => blockField π P L c z) ⁻¹' {false} =
        (markedBlockEvent π P L z)ᶜ := by
      ext p; simp [blockField]
    rw [this]
    exact (markedBlockEvent_measurableSet π P L z).compl
  · have : (fun c : MPair G => blockField π P L c z) ⁻¹' {true} =
        markedBlockEvent π P L z := by
      ext p; simp [blockField]
    rw [this]
    exact markedBlockEvent_measurableSet π P L z

omit [G.LocallyFinite] in
open Classical in
/-- The field restricted to `I` is a function of the pair restricted to `⋃_{i ∈ I} Q_i⁺`. -/
theorem blockField_restrict_eq (I : Finset (ℤ × ℤ)) :
    (fun ω : ℤ × ℤ → Bool => fun i : I => ω i) ∘ blockField π P L =
      (fun r => fun i : I => decide (r ∈ restrPair (I.biUnion (blockPlusFin P L)) ''
        markedBlockEvent π P L i)) ∘ restrPair (I.biUnion (blockPlusFin P L)) := by
  classical
  funext p
  simp only [Function.comp, blockField]
  funext i
  apply decide_eq_decide.2
  have hdet : DeterminedByPair (↑(I.biUnion (blockPlusFin P L))) (markedBlockEvent π P L i) := by
    refine (markedBlockEvent_determined π P L i).mono ?_
    intro v hv
    rw [Finset.coe_biUnion]
    exact Set.mem_biUnion (Finset.mem_coe.2 i.2) (by rw [coe_blockPlusFin]; exact hv)
  exact hdet.mem_iff _ p

variable (ν : ∀ v : V, Measure (G.neighborSet v)) [∀ v, IsProbabilityMeasure (ν v)] (s : NNReal)
  (hs : s ≤ 1)

/-- The block field is `2`-dependent (`rotor.tex:1260-1262`). -/
theorem kDependent_blockField (hL : 0 < L) :
    External.KDependent 2 ((mLaw ν s hs).map (blockField π P L)) := by
  classical
  intro I J hIJ
  refine indepFun_map_of _ (measurable_blockField π P L)
    (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
    (measurable_pi_lambda _ (fun j => measurable_pi_apply _)) ?_
  rw [blockField_restrict_eq π P L I, blockField_restrict_eq π P L J]
  have hdisj : Disjoint (I.biUnion (blockPlusFin P L)) (J.biUnion (blockPlusFin P L)) := by
    rw [Finset.disjoint_biUnion_left]
    intro i hi
    rw [Finset.disjoint_biUnion_right]
    intro j hj
    rw [← Finset.disjoint_coe, coe_blockPlusFin, coe_blockPlusFin]
    refine P.blockPlus_disjoint hL ?_
    have := hIJ i hi j hj
    simp only [linf, Prod.fst_sub, Prod.snd_sub]
    omega
  have := indepFun_restrPair (X := fun v => G.neighborSet v) (Y := fun _ : V => Bool) ν
    (fun _ => External.bernoulli s hs) _ _ hdisj
  exact this.comp (measurable_of_countable _) (measurable_of_countable _)

theorem map_blockField_site (z : ℤ × ℤ) :
    (mLaw ν s hs).map (blockField π P L) {ω | ω z = true} =
      mLaw ν s hs (markedBlockEvent π P L z) := by
  have hmeas : MeasurableSet {ω : ℤ × ℤ → Bool | ω z = true} := by
    have e : {ω : ℤ × ℤ → Bool | ω z = true} = (fun ω : ℤ × ℤ → Bool => ω z) ⁻¹' {true} := rfl
    rw [e]
    exact measurable_pi_apply z (measurableSet_singleton true)
  rw [Measure.map_apply (measurable_blockField π P L) hmeas]
  congr 1
  ext p
  simp [blockField]

/-- The one-site bound: `P̂(E_z) ≤ P̃(C_z) + |Q_z⁺| s`. -/
theorem mLaw_markedBlockEvent_le (z : ℤ × ℤ) :
    mLaw ν s hs (markedBlockEvent π P L z) ≤
      productLaw ν (blockEvent π P L z) + (blockPlusFin P L z).card * s := by
  have hsub : markedBlockEvent π P L z ⊆
      Prod.fst ⁻¹' blockEvent π P L z ∪ ⋃ v ∈ blockPlusFin P L z, {p : MPair G | p.2 v = true} := by
    intro p hp
    by_cases h : ∀ v ∈ P.blockPlus L z, p.2 v = false
    · exact Or.inl (blockEvent_of_marked π P L z hp h)
    · push Not at h
      obtain ⟨v, hv, hne⟩ := h
      refine Or.inr (Set.mem_iUnion₂.2 ⟨v, (Set.Finite.mem_toFinset _).2 hv, ?_⟩)
      simpa using hne
  calc mLaw ν s hs (markedBlockEvent π P L z)
      ≤ mLaw ν s hs (Prod.fst ⁻¹' blockEvent π P L z ∪
          ⋃ v ∈ blockPlusFin P L z, {p : MPair G | p.2 v = true}) := measure_mono hsub
    _ ≤ mLaw ν s hs (Prod.fst ⁻¹' blockEvent π P L z) +
          mLaw ν s hs (⋃ v ∈ blockPlusFin P L z, {p : MPair G | p.2 v = true}) :=
        measure_union_le _ _
    _ ≤ productLaw ν (blockEvent π P L z) + (blockPlusFin P L z).card * s :=
        add_le_add (le_of_eq (mLaw_fst ν s hs (blockEvent_measurableSet π P L z)))
          (mLaw_marks_le ν s hs _)

set_option linter.deprecated false in
/-- The product Bernoulli(`1/8`) field on a finite set of sites. -/
theorem bernoulliField_all (Z : Finset (ℤ × ℤ)) :
    External.bernoulliField (1 / 8) External.eighth_le_one {ω | ∀ z ∈ Z, ω z = true} =
      (1 / 8 : ℝ≥0∞) ^ Z.card := by
  have e : {ω : ℤ × ℤ → Bool | ∀ z ∈ Z, ω z = true} =
      Z.restrict ⁻¹' (Set.pi Set.univ (fun _ : Z => ({true} : Set Bool))) := by
    ext ω
    simp [Finset.restrict]
  rw [e, External.bernoulliField, ← Measure.map_apply (Finset.measurable_restrict Z)
    (MeasurableSet.univ_pi (fun _ => measurableSet_singleton _)), Measure.infinitePi_map_restrict,
    Measure.pi_pi]
  simp only [External.bernoulli, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.bernoulli_apply, Finset.prod_const, Finset.card_univ, Fintype.card_coe, Bool.cond_true]
  norm_num [ENNReal.coe_div]

/-- Domination: on a finite set of blocks, all the marked block events hold with probability at
most `(1/8)^{|Z|}` (LSS, `rotor.tex:1260-1262`). -/
theorem mLaw_iInter_markedBlockEvent_le (hL : 0 < L) {ε : ℝ}
    (hLSS : ∀ μ : Measure (ℤ × ℤ → Bool), IsProbabilityMeasure μ →
      External.KDependent 2 μ → (∀ z, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
      ∀ A : Set (ℤ × ℤ → Bool), MeasurableSet A → External.IsIncreasing A →
        μ A ≤ External.bernoulliField (1 / 8) External.eighth_le_one A)
    (hsite : ∀ z, mLaw ν s hs (markedBlockEvent π P L z) ≤ ENNReal.ofReal (2 * ε))
    (Z : Finset (ℤ × ℤ)) :
    mLaw ν s hs (⋂ z ∈ Z, markedBlockEvent π P L z) ≤ (1 / 8 : ℝ≥0∞) ^ Z.card := by
  have hA : MeasurableSet {ω : ℤ × ℤ → Bool | ∀ z ∈ Z, ω z = true} := by
    have e : {ω : ℤ × ℤ → Bool | ∀ z ∈ Z, ω z = true} =
        ⋂ z ∈ Z, (fun ω : ℤ × ℤ → Bool => ω z) ⁻¹' {true} := by
      ext ω; simp
    rw [e]
    exact MeasurableSet.biInter Z.countable_toSet (fun z _ => measurable_pi_apply z (measurableSet_singleton _))
  have hinc : External.IsIncreasing {ω : ℤ × ℤ → Bool | ∀ z ∈ Z, ω z = true} :=
    fun ω ω' hω hle z hz => hle z (hω z hz)
  have h := hLSS ((mLaw ν s hs).map (blockField π P L))
    (Measure.isProbabilityMeasure_map (measurable_blockField π P L).aemeasurable)
    (kDependent_blockField π P L ν s hs hL) (fun z => by rw [map_blockField_site]; exact hsite z)
    _ hA hinc
  rw [bernoulliField_all, Measure.map_apply (measurable_blockField π P L) hA] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext p
  simp [blockField]

end Field

end Rotor

