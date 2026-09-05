/-
Proposition 3.1 (iii) (`prop:path-reduction`, `rotor.tex:1023-1035`; proof at
`rotor.tex:1178-1195`).  Part one: the passage function is bounded below by a multiple of the
Euclidean norm.  The paper: "Fix a nonzero `z ∈ Λ` and `b < aC⁻¹|z|`, where `a` is as in
`eq:criterion-passage`.  By `eq:distance-comparison`, `bn ≤ a d_G(o, o+nz)` for all sufficiently
large `n`.  Hence `eq:criterion-passage` gives `P{τ(o,o+nz)/n ≤ b} → 0`.  Since
`τ(o,o+nz)/n → μ(z)` in probability, `μ(z) ≥ b`.  Letting `b ↑ aC⁻¹|z|` gives
`μ(z) ≥ aC⁻¹|z|`, and homogeneity and continuity extend this to `ℝ²`."
-/
import Rotor.Support.PathReductionI
import Rotor.Support.CircuitShape
import Rotor.Support.CircuitClock

open Rotor MeasureTheory Filter Topology
open scoped Pointwise ENNReal

universe u

namespace Rotor

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G)

/-! ### Graph distance dominates Euclidean distance (the lower half of `eq:distance-comparison`) -/

omit [DecidableEq V] in
omit [G.LocallyFinite] in
theorem latVec_nsmul (n : ℕ) (z : ℤ × ℤ) : P.latVec (n • z) = (n : ℝ) • P.latVec z := by
  unfold DoublyPeriodic.latVec
  rw [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul, nsmul_eq_mul, smul_add, smul_smul, smul_smul]
  push_cast
  rfl

omit [DecidableEq V] in
/-- Edge lengths are bounded, by periodicity and local finiteness. -/
theorem exists_edge_bound : ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ u v : V, G.Adj u v → ‖P.emb u - P.emb v‖ ≤ ℓ := by
  classical
  obtain ⟨R, hR⟩ := P.finite_orbits.exists_finset_coe
  let S : Finset ℝ := R.biUnion (fun r => (G.neighborFinset r).image (fun w => ‖P.emb r - P.emb w‖))
  have hS : ∀ x ∈ S, 0 ≤ x := by
    intro x hx
    simp only [S, Finset.mem_biUnion, Finset.mem_image] at hx
    obtain ⟨r, -, w, -, rfl⟩ := hx
    exact norm_nonneg _
  refine ⟨1 + ∑ x ∈ S, x, add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg hS), fun u v huv => ?_⟩
  have hu : u = P.shift (P.coord u) (P.rep u) := (P.shift_coord_rep u).symm
  have hadj : G.Adj (P.rep u) (P.shift (-(P.coord u)) v) := by
    have := (P.adj_shift (-(P.coord u)) u v).2 huv
    have e : P.shift (-(P.coord u)) u = P.rep u := by
      rw [← P.shift_shift_neg (P.coord u) (P.rep u), P.shift_coord_rep]
    rw [e] at this
    exact this
  have hlen : ‖P.emb u - P.emb v‖ = ‖P.emb (P.rep u) - P.emb (P.shift (-(P.coord u)) v)‖ := by
    have e1 : P.emb u - P.emb (P.rep u) = P.latVec (P.coord u) := by
      have := P.emb_shift_sub (P.coord u) (P.rep u)
      rwa [P.shift_coord_rep] at this
    have e2 : P.emb v - P.emb (P.shift (-(P.coord u)) v) = P.latVec (P.coord u) := by
      have := P.emb_shift_sub (P.coord u) (P.shift (-(P.coord u)) v)
      rwa [P.shift_neg_shift] at this
    have : P.emb u - P.emb v = P.emb (P.rep u) - P.emb (P.shift (-(P.coord u)) v) := by
      rw [eq_add_of_sub_eq e1, eq_add_of_sub_eq e2]
      abel
    rw [this]
  rw [hlen]
  have hmem : ‖P.emb (P.rep u) - P.emb (P.shift (-(P.coord u)) v)‖ ∈ S := by
    simp only [S, Finset.mem_biUnion, Finset.mem_image, SimpleGraph.mem_neighborFinset]
    refine ⟨P.rep u, ?_, P.shift (-(P.coord u)) v, hadj, rfl⟩
    rw [← Finset.mem_coe, hR]
    exact ⟨u, rfl⟩
  calc ‖P.emb (P.rep u) - P.emb (P.shift (-(P.coord u)) v)‖ ≤ ∑ x ∈ S, x :=
        Finset.single_le_sum hS hmem
    _ ≤ 1 + ∑ x ∈ S, x := by linarith

omit [DecidableEq V] [G.LocallyFinite] in
/-- Euclidean distance is at most `ℓ` times graph distance when edges have length at most `ℓ`. -/
theorem norm_sub_le_dist (hG : G.Connected) {ℓ : ℝ}
    (hℓ : ∀ u v : V, G.Adj u v → ‖P.emb u - P.emb v‖ ≤ ℓ) (x y : V) :
    ‖P.emb x - P.emb y‖ ≤ ℓ * G.dist x y := by
  obtain ⟨p, hp⟩ := (hG.preconnected x y).exists_walk_length_eq_dist
  rw [← hp]
  have key : ∀ {a b : V} (q : G.Walk a b), ‖P.emb a - P.emb b‖ ≤ ℓ * q.length := by
    intro a b q
    induction q with
    | nil => simp
    | @cons a b c h q ih =>
      rw [SimpleGraph.Walk.length_cons]
      push_cast
      calc ‖P.emb a - P.emb c‖ = ‖(P.emb a - P.emb b) + (P.emb b - P.emb c)‖ := by congr 1; abel
        _ ≤ ‖P.emb a - P.emb b‖ + ‖P.emb b - P.emb c‖ := norm_add_le _ _
        _ ≤ ℓ + ℓ * q.length := add_le_add (hℓ _ _ h) ih
        _ = ℓ * (q.length + 1) := by ring
  exact key p

/-! ### The directional constants are bounded below (`eq:criterion-passage`) -/

/-- The event `{τ(x, y) ≤ a d_G(x, y)}` is measurable. -/
theorem measurableSet_fast (hAb : External.Abelian G) [Infinite V] (hG : G.Connected) (a : ℝ)
    (x y : V) : MeasurableSet {ρ : Config G | (τ π ρ x y : ℝ) ≤ a * G.dist x y} := by
  haveI : Countable V := countable_of_connected hG
  exact measurableSet_le
    ((measurable_from_nat (f := (Nat.cast : ℕ → ℝ))).comp (measurable_τ π hAb hG x y))
    measurable_const

/-- From `eq:criterion-passage`: every directional constant is at least `a/ℓ` times the length of
the lattice vector. -/
theorem dir_lower (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (μ : Measure (Config G)) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 < a)
    (hii : Tendsto (fun R : ℕ => ⨆ (x : V) (y : V) (_ : R ≤ G.dist x y),
      μ {ρ | (τ π ρ x y : ℝ) ≤ a * G.dist x y}) atTop (𝓝 0))
    {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ : ∀ x y : V, ‖P.emb x - P.emb y‖ ≤ ℓ * G.dist x y)
    (o : V) {z : ℤ × ℤ} {c : ℝ} (hc : IsDirLimit π P μ z c) :
    a / ℓ * ‖P.latVec z‖ ≤ c := by
  by_contra hlt
  push_neg at hlt
  have hc0 := hc.nonneg π P μ
  have hpos : 0 < ‖P.latVec z‖ := by
    by_contra h
    push_neg at h
    have := norm_nonneg (P.latVec z)
    have h0 : ‖P.latVec z‖ = 0 := le_antisymm h this
    rw [h0, mul_zero] at hlt
    linarith
  obtain ⟨ε, hε, hεdef⟩ : ∃ ε : ℝ, 0 < ε ∧ c + ε = a / ℓ * ‖P.latVec z‖ - ε :=
    ⟨(a / ℓ * ‖P.latVec z‖ - c) / 2, by linarith, by ring⟩
  -- the events
  let E : ℕ → Set (Config G) := fun n =>
    {ρ | (τ π ρ o (P.shift (n • z) o) : ℝ) ≤ a * G.dist o (P.shift (n • z) o)}
  have hE : ∀ n, MeasurableSet (E n) := fun n => measurableSet_fast π hAb hG a o _
  -- the distance to the `n`-th translate grows linearly
  have hdist : ∀ n : ℕ, (n : ℝ) * ‖P.latVec z‖ ≤ ℓ * G.dist o (P.shift (n • z) o) := by
    intro n
    have := hℓ o (P.shift (n • z) o)
    rw [norm_sub_rev, P.emb_shift_sub, latVec_nsmul, norm_smul, Real.norm_natCast] at this
    exact this
  -- almost surely, eventually the event holds
  have hae : ∀ᵐ ρ ∂μ, ∀ᶠ n : ℕ in atTop, ρ ∈ E n := by
    filter_upwards [hc] with ρ hρ
    filter_upwards [(hρ o).eventually (eventually_lt_nhds (show c < c + ε by linarith)),
      eventually_gt_atTop 0] with n hn hn0
    have harr : arr π P ρ o z 0 n = τ π ρ o (P.shift (n • z) o) := by simp [arr, P.shift_zero]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [harr, div_lt_iff₀ hn'] at hn
    show (τ π ρ o (P.shift (n • z) o) : ℝ) ≤ a * G.dist o (P.shift (n • z) o)
    have h1 := hdist n
    have h2 : a / ℓ * ((n : ℝ) * ‖P.latVec z‖) ≤ a / ℓ * (ℓ * G.dist o (P.shift (n • z) o)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : a / ℓ * (ℓ * G.dist o (P.shift (n • z) o)) = a * G.dist o (P.shift (n • z) o) := by
      field_simp
    have h4 : 0 ≤ ε * n := by positivity
    nlinarith
  -- the eventual event has full measure, so some tail intersection has measure above `1/2`
  have hfull : μ (⋃ N : ℕ, ⋂ n ∈ Set.Ici N, E n) = 1 := by
    have hmeas : MeasurableSet (⋃ N : ℕ, ⋂ n ∈ Set.Ici N, E n) :=
      MeasurableSet.iUnion (fun N => MeasurableSet.biInter (Set.to_countable _) (fun n _ => hE n))
    have h : ∀ᵐ ρ ∂μ, ρ ∈ ⋃ N : ℕ, ⋂ n ∈ Set.Ici N, E n := by
      filter_upwards [hae] with ρ hρ
      obtain ⟨N, hN⟩ := eventually_atTop.1 hρ
      exact Set.mem_iUnion.2 ⟨N, Set.mem_iInter₂.2 (fun n hn => hN n hn)⟩
    refine (prob_compl_eq_zero_iff hmeas).1 ?_
    rw [Set.compl_def]
    exact ae_iff.1 h
  have hmono : Monotone (fun N : ℕ => ⋂ n ∈ Set.Ici N, E n) := fun N M hNM =>
    Set.biInter_subset_biInter_left (Set.Ici_subset_Ici.2 hNM)
  have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hfull] at htend
  -- the threshold from `eq:criterion-passage`
  obtain ⟨R, hR⟩ := eventually_atTop.1
    (hii.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ≥0∞) < 1 / 2)))
  -- an index that is both large for the tail and far for the distance
  have hfar : ∀ᶠ N : ℕ in atTop, (R : ℝ) ≤ G.dist o (P.shift (N • z) o) := by
    filter_upwards [eventually_ge_atTop ⌈(R : ℝ) * ℓ / ‖P.latVec z‖⌉₊] with N hN
    have h1 : (R : ℝ) * ℓ / ‖P.latVec z‖ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [div_le_iff₀ hpos] at h1
    have h2 := hdist N
    have : (R : ℝ) * ℓ ≤ ℓ * G.dist o (P.shift (N • z) o) := by linarith
    nlinarith
  obtain ⟨N, hN1, hN2⟩ := ((htend.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ≥0∞) < 1))).and
    hfar).exists
  -- the measure of `E N` is at least the tail measure, above `1/2`
  have hEN : 1 / 2 < μ (E N) :=
    lt_of_lt_of_le hN1 (measure_mono (Set.biInter_subset_of_mem (Set.mem_Ici.2 le_rfl)))
  -- and at most the supremum, below `1/2`
  have hRN : R ≤ G.dist o (P.shift (N • z) o) := by exact_mod_cast hN2
  have hsup : μ (E N) ≤ ⨆ (x : V) (y : V) (_ : R ≤ G.dist x y),
      μ {ρ | (τ π ρ x y : ℝ) ≤ a * G.dist x y} :=
    le_iSup_of_le o (le_iSup_of_le (P.shift (N • z) o) (le_iSup_of_le hRN le_rfl))
  have := hR R le_rfl
  exact absurd (lt_of_lt_of_le hEN (hsup.trans this.le)) (lt_irrefl _)

/-! ### The lower bound on the plane -/

omit [DecidableEq V] [G.LocallyFinite] in
/-- Every point of the plane is within `‖b₀‖ + ‖b₁‖` of a lattice vector. -/
theorem exists_latVec_near (p : Plane) :
    ∃ z : ℤ × ℤ, ‖P.latVec z - p‖ ≤ ‖P.b 0‖ + ‖P.b 1‖ := by
  refine ⟨(⌊P.coords p 0⌋, ⌊P.coords p 1⌋), ?_⟩
  have hp : p = P.coords p 0 • P.b 0 + P.coords p 1 • P.b 1 := by
    have := P.basis.sum_equivFun p
    rw [Fin.sum_univ_two] at this
    simp only [P.basis_apply] at this
    rw [P.coords_apply]
    exact this.symm
  have hsub : P.latVec (⌊P.coords p 0⌋, ⌊P.coords p 1⌋) -
      (P.coords p 0 • P.b 0 + P.coords p 1 • P.b 1) =
      -(Int.fract (P.coords p 0) • P.b 0 + Int.fract (P.coords p 1) • P.b 1) := by
    simp only [DoublyPeriodic.latVec, Int.fract, sub_smul]
    abel
  rw [← hp] at hsub
  rw [hsub, norm_neg]
  calc ‖Int.fract (P.coords p 0) • P.b 0 + Int.fract (P.coords p 1) • P.b 1‖
      ≤ ‖Int.fract (P.coords p 0) • P.b 0‖ + ‖Int.fract (P.coords p 1) • P.b 1‖ := norm_add_le _ _
    _ = Int.fract (P.coords p 0) * ‖P.b 0‖ + Int.fract (P.coords p 1) * ‖P.b 1‖ := by
        rw [norm_smul_of_nonneg (Int.fract_nonneg _), norm_smul_of_nonneg (Int.fract_nonneg _)]
    _ ≤ 1 * ‖P.b 0‖ + 1 * ‖P.b 1‖ := by
        gcongr
        · exact (Int.fract_lt_one _).le
        · exact (Int.fract_lt_one _).le
    _ = ‖P.b 0‖ + ‖P.b 1‖ := by ring

omit [DecidableEq V] [G.LocallyFinite] in
/-- A lower bound on the lattice vectors extends to the plane by homogeneity and continuity. -/
theorem f_lower_of_lattice {f : Plane → ℝ} (hfc : Continuous f)
    (hfadd : ∀ x y, f (x + y) ≤ f x + f y) (hfsmul : ∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x)
    {l : ℝ} (hl : 0 ≤ l) (hm : ∀ z, l * ‖P.latVec z‖ ≤ f (P.latVec z)) (x : Plane) :
    l * ‖x‖ ≤ f x := by
  obtain ⟨C, hC0, hC⟩ := pf_exists_upper hfc hfsmul
  set D₀ : ℝ := ‖P.b 0‖ + ‖P.b 1‖ with hD₀
  have hD₀0 : 0 ≤ D₀ := by positivity
  have key : ∀ k : ℕ, 0 < k → l * ‖x‖ - (l * D₀ + C * D₀) / k ≤ f x := by
    intro k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    obtain ⟨z, hz⟩ := exists_latVec_near P ((k : ℝ) • x)
    have h1 : f ((k : ℝ) • x) = k * f x := hfsmul _ (Nat.cast_nonneg _) x
    have h2 := pf_lip hfadd hC (P.latVec z) ((k : ℝ) • x)
    have h3 := hm z
    have h4 : (k : ℝ) * ‖x‖ - D₀ ≤ ‖P.latVec z‖ := by
      have := norm_sub_norm_le ((k : ℝ) • x) (P.latVec z)
      rw [norm_smul, Real.norm_natCast, norm_sub_rev] at this
      linarith
    have h5 : l * ((k : ℝ) * ‖x‖ - D₀) ≤ l * ‖P.latVec z‖ := mul_le_mul_of_nonneg_left h4 hl
    have h6 : C * ‖P.latVec z - (k : ℝ) • x‖ ≤ C * D₀ := mul_le_mul_of_nonneg_left hz hC0.le
    have h7 : (k : ℝ) * (l * ‖x‖) - (l * D₀ + C * D₀) ≤ k * f x := by linarith
    calc l * ‖x‖ - (l * D₀ + C * D₀) / k = ((k : ℝ) * (l * ‖x‖) - (l * D₀ + C * D₀)) / k := by
          field_simp
      _ ≤ (k * f x) / k := div_le_div_of_nonneg_right h7 hk'.le
      _ = f x := by field_simp
  have hlim : Tendsto (fun k : ℕ => l * ‖x‖ - (l * D₀ + C * D₀) / k) atTop (𝓝 (l * ‖x‖ - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [sub_zero] at hlim
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun k hk => key k hk⟩)

/-! ### Lattice points in scaled sets (Mathlib's `ZLattice.covolume`) -/

namespace DoublyPeriodic

/-- The translation lattice `Λ` as a `ℤ`-submodule of the plane. -/
noncomputable def lattice : Submodule ℤ Plane := Submodule.span ℤ (Set.range P.basis)

instance : DiscreteTopology P.lattice := by
  unfold lattice; infer_instance

instance : IsZLattice ℝ P.lattice := by
  unfold lattice; infer_instance

omit [DecidableEq V] [G.LocallyFinite] in
theorem mem_lattice_iff (x : Plane) : x ∈ P.lattice ↔ ∃ z : ℤ × ℤ, P.latVec z = x := by
  unfold lattice
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(c 0, c 1), ?_⟩
    rw [← hc, Fin.sum_univ_two]
    simp only [DoublyPeriodic.latVec, P.basis_apply]
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  · rintro ⟨z, rfl⟩
    refine ⟨![z.1, z.2], ?_⟩
    rw [Fin.sum_univ_two]
    simp only [DoublyPeriodic.latVec, P.basis_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

omit [DecidableEq V] [G.LocallyFinite] in
theorem latVec_injective : Function.Injective P.latVec := by
  intro z w h
  have := congrArg P.coords h
  rw [P.coords_latVec, P.coords_latVec] at this
  have h0 := congrFun this 0
  have h1 := congrFun this 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_inj] at h0 h1
  exact Prod.ext h0 h1

omit [DecidableEq V] [G.LocallyFinite] in
/-- The lattice points of `n • S`, counted through `latVec`. -/
theorem card_scaled (S : Set Plane) {n : ℕ} (hn : 0 < n) :
    Nat.card (S ∩ (n : ℝ)⁻¹ • (P.lattice : Set Plane) : Set Plane) =
      {z : ℤ × ℤ | P.latVec z ∈ (n : ℝ) • S}.ncard := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.card_coe_set_eq]
  have hinj : Function.Injective (fun z : ℤ × ℤ => (n : ℝ)⁻¹ • P.latVec z) := by
    intro z w h
    exact P.latVec_injective (smul_right_injective _ (inv_ne_zero hn') h)
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext x
  constructor
  · rintro ⟨hxS, hxL⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hxL
    obtain ⟨z, rfl⟩ := (P.mem_lattice_iff _).1 hy
    exact ⟨z, (Set.mem_smul_set_iff_inv_smul_mem₀ hn' S _).2 hxS, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(Set.mem_smul_set_iff_inv_smul_mem₀ hn' S _).1 hz, ?_⟩
    exact Set.smul_mem_smul_set ((P.mem_lattice_iff _).2 ⟨z, rfl⟩)

omit [DecidableEq V] [G.LocallyFinite] in
/-- Counting lattice points in a scaled set: Mathlib's `ZLattice.covolume.tendsto_card_div_pow'`. -/
theorem tendsto_count (S : Set Plane) (hb : Bornology.IsBounded S) (hm : MeasurableSet S)
    (hf : volume (frontier S) = 0) :
    Tendsto (fun n : ℕ => ({z : ℤ × ℤ | P.latVec z ∈ (n : ℝ) • S}.ncard : ℝ) / (n : ℝ) ^ 2) atTop
      (𝓝 (volume.real S / ZLattice.covolume P.lattice)) := by
  have := ZLattice.covolume.tendsto_card_div_pow' P.lattice hb hm hf
  rw [finrank_euclideanSpace_fin] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [P.card_scaled S hn]

end DoublyPeriodic

/-! ### The scaled unit balls -/

section Balls

variable {f : Plane → ℝ} (hfc : Continuous f) (hfadd : ∀ x y, f (x + y) ≤ f x + f y)
  (hfsmul : ∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x)
  {l : ℝ} (hl : 0 < l) (hmin : ∀ u : Plane, ‖u‖ = 1 → l ≤ f u)

include hfc hfsmul hl hmin in
theorem ball_isBounded (θ : ℝ) : Bornology.IsBounded (θ • {x : Plane | f x ≤ 1}) :=
  (pf_isCompact hfc hfsmul hl hmin).isBounded.smul₀ θ

include hfc hfsmul in
theorem ball_measurableSet (θ : ℝ) : MeasurableSet (θ • {x : Plane | f x ≤ 1}) := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · rw [Set.zero_smul_set ⟨0, by simp [pf_zero hfsmul]⟩]
    exact measurableSet_singleton 0
  · exact ((isClosed_Iic.preimage hfc).smul₀ θ).measurableSet

include hfadd hfsmul in
theorem ball_frontier_null (θ : ℝ) : volume (frontier (θ • {x : Plane | f x ≤ 1})) = 0 :=
  ((pf_convex hfadd hfsmul).smul θ).addHaar_frontier volume

theorem volume_real_ball_smul {θ : ℝ} (hθ : 0 ≤ θ) :
    volume.real (θ • {x : Plane | f x ≤ 1}) = θ ^ 2 * volume.real {x : Plane | f x ≤ 1} := by
  rw [measureReal_def, measureReal_def, MeasureTheory.Measure.addHaar_smul_of_nonneg _ hθ,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

include hfc hfsmul hl hmin in
theorem volume_real_ball_pos {C : ℝ} (hC0 : 0 < C) (hC : ∀ x, f x ≤ C * ‖x‖) :
    0 < volume.real {x : Plane | f x ≤ 1} := by
  rw [measureReal_def, ENNReal.toReal_pos_iff]
  constructor
  · exact Measure.measure_pos_of_nonempty_interior _ ⟨0, pf_zero_mem_interior hC0 hC⟩
  · exact (pf_isCompact hfc hfsmul hl hmin).measure_lt_top

end Balls

/-! ### Counting the range in each orbit -/

section Orbit

variable {f : Plane → ℝ} (hfc : Continuous f) (hfadd : ∀ x y, f (x + y) ≤ f x + f y)
  (hfsmul : ∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x)
  {l : ℝ} (hl : 0 < l) (hmin : ∀ u : Plane, ‖u‖ = 1 → l ≤ f u)

omit [DecidableEq V] [G.LocallyFinite] in
/-- Lattice points in a scaled bounded set are finitely many. -/
theorem finite_latt_of_bounded {S : Set Plane} (hb : Bornology.IsBounded S) (n : ℕ) :
    {z : ℤ × ℤ | P.latVec z ∈ (n : ℝ) • S}.Finite := by
  obtain ⟨R₀, hR₀⟩ := hb.exists_norm_le
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ S, ‖y‖ ≤ R :=
    ⟨max R₀ 0, le_max_right _ _, fun y hy => (hR₀ y hy).trans (le_max_left _ _)⟩
  refine (Set.finite_Icc (-(⌈‖P.coords‖ * (n * R)⌉₊ : ℤ), -(⌈‖P.coords‖ * (n * R)⌉₊ : ℤ))
    ((⌈‖P.coords‖ * (n * R)⌉₊ : ℤ), (⌈‖P.coords‖ * (n * R)⌉₊ : ℤ))).subset (fun z hz => ?_)
  obtain ⟨y, hy, hyz⟩ := Set.mem_smul_set.1 hz
  have h1 : ‖P.latVec z‖ ≤ n * R := by
    rw [← hyz, norm_smul, Real.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hR y hy) (Nat.cast_nonneg _)
  have h2 : supNorm z ≤ ‖P.coords‖ * (n * R) :=
    (P.supNorm_le_norm_latVec z).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
  have h3 : ‖P.coords‖ * (n * R) ≤ ⌈‖P.coords‖ * (n * R)⌉₊ := Nat.le_ceil _
  have b1 := (abs_fst_le_supNorm z).trans (h2.trans h3)
  have b2 := (abs_snd_le_supNorm z).trans (h2.trans h3)
  rw [abs_le] at b1 b2
  rw [Set.mem_Icc, Prod.mk_le_mk, Prod.mk_le_mk]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact_mod_cast b1.1
  · exact_mod_cast b2.1
  · exact_mod_cast b1.2
  · exact_mod_cast b2.2

/-- The fiber of `A_n` over a representative `r`, as a set of lattice points. -/
theorem card_fiber_eq (ρ : Config G) (o r : V) (hr : P.rep r = r) (n : ℕ) :
    ((A π ρ o n).filter (fun x => P.rep x = r)).card =
      {z : ℤ × ℤ | P.shift z r ∈ A π ρ o n}.ncard := by
  have hinj : Function.Injective (fun z : ℤ × ℤ => P.shift z r) := by
    intro z w h
    have h' : P.shift z r = P.shift w r := h
    have : P.latVec z = P.latVec w := by
      rw [← P.emb_shift_sub z r, ← P.emb_shift_sub w r, h']
    exact P.latVec_injective this
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext x
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, hrx⟩
    refine ⟨P.coord x, ?_, ?_⟩
    · rw [← hrx, P.shift_coord_rep]; exact hx
    · rw [← hrx, P.shift_coord_rep]
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, by rw [P.rep_shift, hr]⟩

omit [DecidableEq V] [G.LocallyFinite] in
include hfsmul in
/-- Membership of a lattice vector in the scaled ball, through `f`. -/
theorem mem_scaled_ball_iff {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (hn : 0 < n) (x : Plane) :
    x ∈ (n : ℝ) • (θ • {y : Plane | f y ≤ 1}) ↔ f x ≤ n * θ := by
  have hnθ : (0 : ℝ) < (n : ℝ) * θ := by positivity
  rw [smul_smul, Set.mem_smul_set_iff_inv_smul_mem₀ hnθ.ne', Set.mem_setOf_eq,
    hfsmul _ (inv_nonneg.2 hnθ.le), inv_mul_le_iff₀ hnθ, mul_one]

include hfadd hfsmul in
/-- The lattice points of the fiber are sandwiched between those of two scaled balls. -/
theorem fiber_sandwich (ρ : Config G) (o r : V) {C : ℝ} (hC : ∀ x, f x ≤ C * ‖x‖)
    (hsand : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
      (∀ x : V, f (P.emb x - P.emb o) ≤ (1 - ε) * n → x ∈ A π ρ o n) ∧
      (∀ x ∈ A π ρ o n, f (P.emb x - P.emb o) ≤ (1 + ε) * n))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      {z : ℤ × ℤ | P.latVec z ∈ (n : ℝ) • ((1 - 2 * ε) • {x : Plane | f x ≤ 1})} ⊆
        {z | P.shift z r ∈ A π ρ o n} ∧
      {z : ℤ × ℤ | P.shift z r ∈ A π ρ o n} ⊆
        {z | P.latVec z ∈ (n : ℝ) • ((1 + 2 * ε) • {x : Plane | f x ≤ 1})} := by
  have hemb : ∀ z, P.emb (P.shift z r) - P.emb o = P.latVec z + (P.emb r - P.emb o) := fun z => by
    rw [← P.emb_shift_sub]; abel
  filter_upwards [hsand ε hε (by linarith), eventually_ge_atTop ⌈C * ‖P.emb r - P.emb o‖ / ε⌉₊,
    eventually_gt_atTop 0] with n hn hN hn0
  have hCv : C * ‖P.emb r - P.emb o‖ ≤ ε * n := by
    have : C * ‖P.emb r - P.emb o‖ / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [div_le_iff₀ hε] at this
    linarith
  constructor
  · intro z hz
    rw [Set.mem_setOf_eq, mem_scaled_ball_iff hfsmul (by linarith) hn0] at hz
    show P.shift z r ∈ A π ρ o n
    apply hn.1
    rw [hemb]
    have := pf_lip hfadd hC (P.latVec z + (P.emb r - P.emb o)) (P.latVec z)
    rw [add_sub_cancel_left] at this
    linarith
  · intro z hz
    rw [Set.mem_setOf_eq, mem_scaled_ball_iff hfsmul (by linarith) hn0]
    have h1 := hn.2 _ hz
    rw [hemb] at h1
    have := pf_lip hfadd hC (P.latVec z) (P.latVec z + (P.emb r - P.emb o))
    rw [sub_add_cancel_left, norm_neg] at this
    linarith

include hfc hfadd hfsmul hl hmin in
/-- The number of range vertices in the orbit of `r`, normalized by `n²`, converges to the area
of the unit ball divided by the covolume of the lattice. -/
theorem tendsto_fiber (ρ : Config G) (o r : V) (hr : P.rep r = r) {C : ℝ}
    (hC : ∀ x, f x ≤ C * ‖x‖)
    (hsand : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
      (∀ x : V, f (P.emb x - P.emb o) ≤ (1 - ε) * n → x ∈ A π ρ o n) ∧
      (∀ x ∈ A π ρ o n, f (P.emb x - P.emb o) ≤ (1 + ε) * n)) :
    Tendsto (fun n : ℕ => (((A π ρ o n).filter (fun x => P.rep x = r)).card : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (volume.real {x : Plane | f x ≤ 1} / ZLattice.covolume P.lattice)) := by
  obtain ⟨v, hv0, hv⟩ : ∃ v : ℝ, 0 ≤ v ∧ v = volume.real {x : Plane | f x ≤ 1} / ZLattice.covolume P.lattice :=
    ⟨_, div_nonneg measureReal_nonneg (ZLattice.covolume_pos P.lattice volume).le, rfl⟩
  rw [← hv]
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨ε, hε, hε1, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ 8 * ε * v ≤ δ / 2 := by
    refine ⟨min (1 / 4) (δ / (16 * (v + 1))), by positivity, ?_, ?_⟩
    · exact (min_le_left _ _).trans_lt (by norm_num)
    · calc 8 * min (1 / 4) (δ / (16 * (v + 1))) * v ≤ 8 * (δ / (16 * (v + 1))) * v := by
            gcongr; exact min_le_right _ _
        _ = δ / 2 * (v / (v + 1)) := by field_simp; ring
        _ ≤ δ / 2 * 1 := by
            gcongr
            rw [div_le_one (by positivity)]; linarith
        _ = δ / 2 := mul_one _
  have h1ε : (0 : ℝ) < 1 - 2 * ε := by linarith
  have h2ε : (0 : ℝ) < 1 + 2 * ε := by linarith
  have hlow := P.tendsto_count ((1 - 2 * ε) • {x : Plane | f x ≤ 1})
    (ball_isBounded hfc hfsmul hl hmin _) (ball_measurableSet hfc hfsmul _)
    (ball_frontier_null hfadd hfsmul _)
  have hup := P.tendsto_count ((1 + 2 * ε) • {x : Plane | f x ≤ 1})
    (ball_isBounded hfc hfsmul hl hmin _) (ball_measurableSet hfc hfsmul _)
    (ball_frontier_null hfadd hfsmul _)
  rw [volume_real_ball_smul h1ε.le, mul_div_assoc, ← hv] at hlow
  rw [volume_real_ball_smul h2ε.le, mul_div_assoc, ← hv] at hup
  have e1 := hlow.eventually (eventually_gt_nhds
    (show (1 - 2 * ε) ^ 2 * v - δ / 4 < (1 - 2 * ε) ^ 2 * v by linarith))
  have e2 := hup.eventually (eventually_lt_nhds
    (show (1 + 2 * ε) ^ 2 * v < (1 + 2 * ε) ^ 2 * v + δ / 4 by linarith))
  have e3 := fiber_sandwich π P hfadd hfsmul ρ o r hC hsand hε hε1
  obtain ⟨N, hN⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (eventually_gt_atTop 0))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2, ⟨hsub1, hsub2⟩, hn0⟩ := hN n hn
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hfin := finite_latt_of_bounded P (ball_isBounded hfc hfsmul hl hmin (1 + 2 * ε)) n
  have c1 : ({z : ℤ × ℤ | P.latVec z ∈ (n : ℝ) • ((1 - 2 * ε) • {x : Plane | f x ≤ 1})}.ncard : ℝ) ≤
      ((A π ρ o n).filter (fun x => P.rep x = r)).card := by
    rw [card_fiber_eq π P ρ o r hr]
    exact_mod_cast Set.ncard_le_ncard hsub1 (hfin.subset hsub2)
  have c2 : (((A π ρ o n).filter (fun x => P.rep x = r)).card : ℝ) ≤
      ({z : ℤ × ℤ | P.latVec z ∈ (n : ℝ) • ((1 + 2 * ε) • {x : Plane | f x ≤ 1})}.ncard : ℝ) := by
    rw [card_fiber_eq π P ρ o r hr]
    exact_mod_cast Set.ncard_le_ncard hsub2 hfin
  have d1 := div_le_div_of_nonneg_right c1 hn'.le
  have d2 := div_le_div_of_nonneg_right c2 hn'.le
  have p1 : 0 ≤ ε * v := mul_nonneg hε.le hv0
  have p2 : 0 ≤ ε * ε * v := mul_nonneg (mul_nonneg hε.le hε.le) hv0
  have p3 : ε * ε * v ≤ ε * v := by nlinarith
  have q1 : v - 8 * ε * v ≤ (1 - 2 * ε) ^ 2 * v := by nlinarith
  have q2 : (1 + 2 * ε) ^ 2 * v ≤ v + 8 * ε * v := by nlinarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Orbit

/-! ### The constants `α` and `β` -/

section Constants

omit [DecidableEq V] [G.LocallyFinite] in
/-- In a connected graph on an infinite vertex type, every vertex has a neighbor. -/
theorem exists_adj_of_connected [Infinite V] (hG : G.Connected) (v : V) : ∃ w, G.Adj v w := by
  obtain ⟨u, hu⟩ := exists_ne v
  obtain ⟨p⟩ := hG.preconnected v u
  cases p with
  | nil => exact (hu rfl).elim
  | cons h _ => exact ⟨_, h⟩

omit [DecidableEq V] in
theorem degree_pos_of_connected [Infinite V] (hG : G.Connected) (v : V) : 0 < G.degree v := by
  obtain ⟨w, hw⟩ := exists_adj_of_connected hG v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_pos.2 ⟨w, (SimpleGraph.mem_neighborFinset G v w).2 hw⟩

omit [DecidableEq V] in
/-- Degrees are constant on orbits. -/
theorem degree_shift (hπ : P.Periodic π) (z : ℤ × ℤ) (v : V) :
    G.degree (P.shift z v) = G.degree v := by
  have := (P.mechAut π hπ z).degree_act v
  simpa [P.mechAut_σ] using this

omit [DecidableEq V] in
theorem degree_eq_rep (hπ : P.Periodic π) (v : V) : G.degree v = G.degree (P.rep v) := by
  have := degree_shift π P hπ (P.coord v) (P.rep v)
  rw [P.shift_coord_rep] at this
  exact this

omit [DecidableEq V] [G.LocallyFinite] in
theorem rep_rep (v : V) : P.rep (P.rep v) = P.rep v := by
  have := P.rep_shift (P.coord v) (P.rep v)
  rw [P.shift_coord_rep] at this
  exact this.symm

omit [DecidableEq V] [G.LocallyFinite] in
theorem rep_eq_of_mem {R : Finset V} (hR : (R : Set V) = Set.range P.rep) {r : V} (hr : r ∈ R) :
    P.rep r = r := by
  have : r ∈ Set.range P.rep := by rw [← hR]; exact Finset.mem_coe.2 hr
  obtain ⟨v, rfl⟩ := this
  exact rep_rep P v

omit [DecidableEq V] [G.LocallyFinite] in
theorem rep_mem {R : Finset V} (hR : (R : Set V) = Set.range P.rep) (v : V) : P.rep v ∈ R := by
  rw [← Finset.mem_coe, hR]
  exact ⟨v, rfl⟩

theorem card_A_eq_sum {R : Finset V} (hR : (R : Set V) = Set.range P.rep) (ρ : Config G) (o : V)
    (n : ℕ) : (A π ρ o n).card = ∑ r ∈ R, ((A π ρ o n).filter (fun x => P.rep x = r)).card :=
  Finset.card_eq_sum_card_fiberwise (fun x _ => rep_mem P hR x)

theorem degsum_A_eq_sum (hπ : P.Periodic π) {R : Finset V} (hR : (R : Set V) = Set.range P.rep)
    (ρ : Config G) (o : V) (n : ℕ) :
    ∑ x ∈ A π ρ o n, G.degree x =
      ∑ r ∈ R, G.degree r * ((A π ρ o n).filter (fun x => P.rep x = r)).card := by
  calc ∑ x ∈ A π ρ o n, G.degree x
      = ∑ r ∈ R, ∑ x ∈ (A π ρ o n).filter (fun x => P.rep x = r), G.degree x :=
        (Finset.sum_fiberwise_of_maps_to (s := A π ρ o n) (t := R) (g := P.rep)
          (fun x _ => rep_mem P hR x) (fun x => G.degree x)).symm
    _ = ∑ r ∈ R, G.degree r * ((A π ρ o n).filter (fun x => P.rep x = r)).card := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Finset.sum_congr rfl (fun x hx => by
          rw [degree_eq_rep π P hπ x, (Finset.mem_filter.1 hx).2]), Finset.sum_const, smul_eq_mul,
          mul_comm]

variable {f : Plane → ℝ} (hfc : Continuous f) (hfadd : ∀ x y, f (x + y) ≤ f x + f y)
  (hfsmul : ∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x)
  {l : ℝ} (hl : 0 < l) (hmin : ∀ u : Plane, ‖u‖ = 1 → l ≤ f u)

include hfc hfadd hfsmul hl hmin in
theorem tendsto_card_A {R : Finset V} (hR : (R : Set V) = Set.range P.rep) (ρ : Config G) (o : V)
    {C : ℝ} (hC : ∀ x, f x ≤ C * ‖x‖)
    (hsand : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
      (∀ x : V, f (P.emb x - P.emb o) ≤ (1 - ε) * n → x ∈ A π ρ o n) ∧
      (∀ x ∈ A π ρ o n, f (P.emb x - P.emb o) ≤ (1 + ε) * n)) :
    Tendsto (fun n : ℕ => ((A π ρ o n).card : ℝ) / (n : ℝ) ^ 2) atTop
      (𝓝 (R.card * (volume.real {x : Plane | f x ≤ 1} / ZLattice.covolume P.lattice))) := by
  have h : ∀ n : ℕ, ((A π ρ o n).card : ℝ) / (n : ℝ) ^ 2 =
      ∑ r ∈ R, (((A π ρ o n).filter (fun x => P.rep x = r)).card : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    rw [card_A_eq_sum π P hR ρ o n, Nat.cast_sum, Finset.sum_div]
  simp_rw [h]
  have := tendsto_finset_sum R (fun r hr =>
    tendsto_fiber π P hfc hfadd hfsmul hl hmin ρ o r (rep_eq_of_mem P hR hr) hC hsand)
  simpa [Finset.sum_const, nsmul_eq_mul] using this

include hfc hfadd hfsmul hl hmin in
theorem tendsto_deg_A (hπ : P.Periodic π) {R : Finset V} (hR : (R : Set V) = Set.range P.rep)
    (ρ : Config G) (o : V) {C : ℝ} (hC : ∀ x, f x ≤ C * ‖x‖)
    (hsand : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
      (∀ x : V, f (P.emb x - P.emb o) ≤ (1 - ε) * n → x ∈ A π ρ o n) ∧
      (∀ x ∈ A π ρ o n, f (P.emb x - P.emb o) ≤ (1 + ε) * n)) :
    Tendsto (fun n : ℕ => ((∑ x ∈ A π ρ o n, G.degree x : ℕ) : ℝ) / (n : ℝ) ^ 2) atTop
      (𝓝 (((∑ r ∈ R, G.degree r : ℕ) : ℝ) *
        (volume.real {x : Plane | f x ≤ 1} / ZLattice.covolume P.lattice))) := by
  have h : ∀ n : ℕ, ((∑ x ∈ A π ρ o n, G.degree x : ℕ) : ℝ) / (n : ℝ) ^ 2 =
      ∑ r ∈ R, (G.degree r : ℝ) *
        ((((A π ρ o n).filter (fun x => P.rep x = r)).card : ℝ) / (n : ℝ) ^ 2) := by
    intro n
    rw [degsum_A_eq_sum π P hπ hR ρ o n, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    push_cast
    ring
  simp_rw [h]
  have := tendsto_finset_sum R (fun r hr =>
    (tendsto_fiber π P hfc hfadd hfsmul hl hmin ρ o r (rep_eq_of_mem P hR hr) hC hsand).const_mul
      (G.degree r : ℝ))
  rw [← Finset.sum_mul] at this
  push_cast
  exact this

end Constants

/-! ### The directional limits of the passage function -/

/-- The uniform limit gives the directional limits at the lattice vectors. -/
theorem isDirLimit_of_uniform [Infinite V] (hG : G.Connected)
    (μ : Measure (Config G)) {f : Plane → ℝ}
    (hfsmul : ∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x)
    (hunif : ∀ o : V, ∀ᵐ ρ ∂μ, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ x : V, R₀ ≤ ‖P.emb x - P.emb o‖ →
      |(τ π ρ o x : ℝ) - f (P.emb x - P.emb o)| ≤ ε * ‖P.emb x - P.emb o‖)
    (z : ℤ × ℤ) : IsDirLimit π P μ z (f (P.latVec z)) := by
  haveI : Countable V := countable_of_connected hG
  rw [IsDirLimit, ae_all_iff]
  intro o
  filter_upwards [hunif o] with ρ hρ
  have harr : ∀ n : ℕ, (arr π P ρ o z 0 n : ℝ) = τ π ρ o (P.shift (n • z) o) := fun n => by
    simp [arr, P.shift_zero]
  have hemb : ∀ n : ℕ, P.emb (P.shift (n • z) o) - P.emb o = (n : ℝ) • P.latVec z := fun n => by
    rw [P.emb_shift_sub, latVec_nsmul]
  rcases eq_or_ne (P.latVec z) 0 with hz | hz
  · -- the trivial direction
    have hz0 : z = 0 := P.latVec_injective (by rw [hz]; simp [DoublyPeriodic.latVec])
    subst hz0
    have hl0 : P.latVec 0 = 0 := by simp [DoublyPeriodic.latVec]
    have hf0 : f (P.latVec 0) = 0 := by
      have := hfsmul 0 le_rfl (P.latVec 0)
      rw [hl0]
      simpa using this
    rw [hf0]
    have : (fun n : ℕ => (arr π P ρ o 0 0 n : ℝ) / n) = fun _ => 0 := by
      funext n
      rw [harr]
      simp [P.shift_zero, τ_self π hG]
    rw [this]
    exact tendsto_const_nhds
  · have hpos : 0 < ‖P.latVec z‖ := norm_pos_iff.2 hz
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨R₀, hR₀⟩ := hρ (δ / (‖P.latVec z‖ + 1)) (by positivity)
    refine ⟨⌈R₀ / ‖P.latVec z‖⌉₊ + 1, fun n hn => ?_⟩
    have hn0 : 0 < n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnR : R₀ ≤ n * ‖P.latVec z‖ := by
      have : R₀ / ‖P.latVec z‖ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈R₀ / ‖P.latVec z‖⌉₊ ≤ n))
      rwa [div_le_iff₀ hpos] at this
    have hx := hR₀ (P.shift (n • z) o) (by rw [hemb, norm_smul, Real.norm_natCast]; exact hnR)
    rw [hemb, norm_smul, Real.norm_natCast, hfsmul _ hn'.le] at hx
    rw [Real.dist_eq, harr]
    have : (τ π ρ o (P.shift (n • z) o) : ℝ) / n - f (P.latVec z) =
        ((τ π ρ o (P.shift (n • z) o) : ℝ) - n * f (P.latVec z)) / n := by
      field_simp
    rw [this, abs_div, abs_of_pos hn', div_lt_iff₀ hn']
    calc |(τ π ρ o (P.shift (n • z) o) : ℝ) - n * f (P.latVec z)|
        ≤ δ / (‖P.latVec z‖ + 1) * (n * ‖P.latVec z‖) := hx
      _ = δ * (‖P.latVec z‖ / (‖P.latVec z‖ + 1)) * n := by ring
      _ < δ * 1 * n := by
          gcongr
          rw [div_lt_one (by positivity)]
          linarith
      _ = δ * n := by ring

/-! ### Assembly of `prop:path-reduction` -/

/-- Proof of `prop:path-reduction` (iii). -/
theorem path_reduction_iii_proof (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (hHP : External.VisitsAllOfVisitsOne G) (hK : External.Kingman.{u}) [Infinite V]
    (hG : G.Connected) (hdeg : ∃ D : ℕ, ∀ v, G.degree v ≤ D) (μ : Measure (Config G))
    [IsProbabilityMeasure μ] (η : ℝ) (hη : 0 < η) (hcrit : Criterion π μ η) (hπ : P.Periodic π)
    (hinv : P.Invariant μ) (herg : P.Ergodic μ) (o : V) :
    ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
      ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
        ∀ᵐ ρ ∂μ, (∀ n : ℕ, T π ρ o n < ⊤) ∧
          Tendsto (fun n : ℕ =>
            Metric.hausdorffDist ((n : ℝ)⁻¹ • ((fun x => P.emb x - P.emb o) '' (A π ρ o n : Set V))) B)
            atTop (𝓝 0) ∧
          Tendsto (fun t : ℕ =>
            Metric.hausdorffDist (((t : ℝ) ^ (-(1 / 3 : ℝ))) •
              ((fun x => P.emb x - P.emb o) '' (R π ρ o t : Set V))) (κ • B)) atTop (𝓝 0) ∧
          Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c) := by
  haveI : Countable V := countable_of_connected hG
  have hi := path_reduction_i π hFLP hAb hHP hG μ η hη hcrit
  obtain ⟨a, ha, hii⟩ := path_reduction_ii π hFLP hAb hHP hG hdeg μ η hη hcrit
  obtain ⟨f, hfc, hf0, hfadd, hfsmul, hunif⟩ := passage_limit_proof π P hK hπ hAb hG μ hinv herg
  have hball : ∀ᵐ ρ ∂μ, ∀ n : ℕ, T π ρ o n < ⊤ ∧ ∀ x : V, x ∈ A π ρ o n ↔ τ π ρ o x ≤ n := by
    filter_upwards [hi] with ρ hρ
    exact (passage_proof π hFLP hAb hG ρ o).2.2 hρ.1
  -- the lower bound on the passage function
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_edge_bound P
  have hℓ' : ∀ x y, ‖P.emb x - P.emb y‖ ≤ ℓ * G.dist x y := norm_sub_le_dist P hG hℓ
  have hdir : ∀ z, IsDirLimit π P μ z (f (P.latVec z)) :=
    isDirLimit_of_uniform π P hG μ hfsmul hunif
  have hlat : ∀ z, a / ℓ * ‖P.latVec z‖ ≤ f (P.latVec z) := fun z =>
    dir_lower π P hAb hG μ ha hii hℓ0 hℓ' o (hdir z)
  have hlow : ∀ x, a / ℓ * ‖x‖ ≤ f x :=
    f_lower_of_lattice P hfc hfadd hfsmul (by positivity) hlat
  have hl : 0 < a / ℓ := by positivity
  have hmin : ∀ u : Plane, ‖u‖ = 1 → a / ℓ ≤ f u := fun u hu => by
    have := hlow u
    rwa [hu, mul_one] at this
  obtain ⟨C, hC0, hC⟩ := pf_exists_upper hfc hfsmul
  -- the shape
  obtain ⟨hBc, hBconv, hB0, hhaus, hsand⟩ := circuit_shape_proof π P hπ hG μ o f
    ⟨hfc, hf0, hfadd, hfsmul, hunif o⟩ hball ⟨a / ℓ, hl, hmin⟩
  -- the constants
  obtain ⟨Rf, hRf⟩ := P.finite_orbits.exists_finset_coe
  obtain ⟨v, hv, hvdef⟩ : ∃ v : ℝ, 0 < v ∧
      v = volume.real {x : Plane | f x ≤ 1} / ZLattice.covolume P.lattice :=
    ⟨_, div_pos (volume_real_ball_pos hfc hfsmul hl hmin hC0 hC) (ZLattice.covolume_pos _ _), rfl⟩
  have hRne : Rf.Nonempty := ⟨P.rep o, rep_mem P hRf o⟩
  have hα : 0 < (Rf.card : ℝ) * v := mul_pos (by exact_mod_cast Finset.card_pos.2 hRne) hv
  have hβ : 0 < ((∑ r ∈ Rf, G.degree r : ℕ) : ℝ) * v :=
    mul_pos (by exact_mod_cast Finset.sum_pos (fun r _ => degree_pos_of_connected hG r) hRne) hv
  refine ⟨{x | f x ≤ 1}, hBc, hBconv, hB0,
    (3 / (((∑ r ∈ Rf, G.degree r : ℕ) : ℝ) * v)) ^ (1 / 3 : ℝ),
    (Rf.card : ℝ) * v * (3 / (((∑ r ∈ Rf, G.degree r : ℕ) : ℝ) * v)) ^ (2 / 3 : ℝ),
    Real.rpow_pos_of_pos (by positivity) _, mul_pos hα (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  filter_upwards [hball, hhaus, hsand] with ρ hρb hρh hρs
  have hT : ∀ n, T π ρ o n < ⊤ := fun n => (hρb n).1
  have hαn := tendsto_card_A π P hfc hfadd hfsmul hl hmin hRf ρ o hC hρs
  have hβn := tendsto_deg_A π P hfc hfadd hfsmul hl hmin hπ hRf ρ o hC hρs
  rw [← hvdef] at hαn hβn
  obtain ⟨-, hclock2, hclock3⟩ := circuit_clock_proof π ρ o hFLP hG hT
  obtain ⟨-, hcard⟩ := hclock2 _ _ hα hβ hαn hβn
  exact ⟨hT, hρh, hclock3 _ _ hα hβ hαn hβn (fun x => P.emb x - P.emb o) _ hBc hρh, hcard⟩

/-- Proof of `prop:path-reduction`. -/
theorem path_reduction_proof (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    (hHP : External.VisitsAllOfVisitsOne G) (hK : External.Kingman.{u}) [Infinite V]
    (hG : G.Connected) (hdeg : ∃ D : ℕ, ∀ v, G.degree v ≤ D) (μ : Measure (Config G))
    [IsProbabilityMeasure μ] (η : ℝ) (hη : 0 < η) (hcrit : Criterion π μ η) :
    (∀ᵐ ρ ∂μ, AllTerminate π ρ ∧ ∀ o : V, Recurrent π ρ o) ∧
    (∃ a : ℝ, 0 < a ∧
      Tendsto (fun R : ℕ => ⨆ (x : V) (y : V) (_ : R ≤ G.dist x y),
        μ {ρ | (τ π ρ x y : ℝ) ≤ a * G.dist x y}) atTop (𝓝 0)) ∧
    (∀ P : DoublyPeriodic G, P.Periodic π → P.Invariant μ → P.Ergodic μ → ∀ o : V,
      ∃ B : Set Plane, IsCompact B ∧ Convex ℝ B ∧ (0 : Plane) ∈ interior B ∧
      ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
        ∀ᵐ ρ ∂μ, (∀ n : ℕ, T π ρ o n < ⊤) ∧
          Tendsto (fun n : ℕ =>
            Metric.hausdorffDist ((n : ℝ)⁻¹ • ((fun x => P.emb x - P.emb o) '' (A π ρ o n : Set V))) B) atTop (𝓝 0) ∧
          Tendsto (fun t : ℕ =>
            Metric.hausdorffDist (((t : ℝ) ^ (-(1 / 3 : ℝ))) • ((fun x => P.emb x - P.emb o) '' (R π ρ o t : Set V)))
              (κ • B)) atTop (𝓝 0) ∧
          Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 c)) :=
  ⟨path_reduction_i π hFLP hAb hHP hG μ η hη hcrit,
    path_reduction_ii π hFLP hAb hHP hG hdeg μ η hη hcrit,
    fun P hπ hinv herg o =>
      path_reduction_iii_proof π P hFLP hAb hHP hK hG hdeg μ η hη hcrit hπ hinv herg o⟩

end Rotor

