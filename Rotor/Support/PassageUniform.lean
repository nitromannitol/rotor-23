/-
Uniform convergence of the passage time to the passage function, and the proof of
`prop:passage-limit` (`rotor.tex:1084-1111`).  The paper: "The usual argument, using the
triangle inequality and the four-endpoint inequality, extends `μ` to the stated
deterministic function and gives `eq:uniform-passage`."  The argument: the lattice
directional constants form a subadditive function on `ℤ²` (`Support/PassageArray`), it
extends to the plane (`Support/PlaneExtension`), and for a lattice point `w` at scale `n`
the passage time to `w` is within `O(n)` of the passage time along a direction from a
finite set, where the directional limit is uniform.
-/
import Rotor.Support.PassageArray
import Rotor.Support.PlaneExtension

open Finset MeasureTheory Filter Topology

universe u

namespace Rotor

theorem abs_add_three' (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

/-- The sup norm of a lattice vector as a natural number. -/
def supNat (w : ℤ × ℤ) : ℕ := max w.1.natAbs w.2.natAbs

theorem supNorm_eq_supNat (w : ℤ × ℤ) : supNorm w = supNat w := by
  rw [supNorm, supNat, Nat.cast_max, ← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs,
    Int.abs_eq_natAbs, Int.cast_natCast, Int.cast_natCast]

theorem abs_fst_le_supNat (w : ℤ × ℤ) : |w.1| ≤ (supNat w : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast le_max_left _ _

theorem abs_snd_le_supNat (w : ℤ × ℤ) : |w.2| ≤ (supNat w : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast le_max_right _ _

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G)

/-- The passage times from a base point are 1-Lipschitz in the graph distance. -/
theorem abs_τ_sub_le (hAb : External.Abelian G) [Infinite V] (hG : G.Connected) (ρ : Config G)
    (o x y : V) : |(τ π ρ o x : ℝ) - τ π ρ o y| ≤ G.dist x y := by
  simpa only [SimpleGraph.dist_self, Nat.cast_zero, zero_add] using
    τ_four π hAb hG ρ o o x y
/-- Uniform convergence over the lattice: almost surely, for every `ε` the passage time to
`shift w o` is within `ε |w|_∞` of `m w` once `|w|_∞` is large. -/
theorem uniform_lattice (hπ : P.Periodic π) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (μ : Measure (Config G)) [IsProbabilityMeasure μ] (m : ℤ × ℤ → ℝ) (K₀ : ℝ)
    (hm : ∀ z, IsDirLimit π P μ z (m z)) (hL : LatticeSubadditive m K₀) (o : V)
    (hK : ∀ z, (G.dist o (P.shift z o) : ℝ) ≤ K₀ * supNorm z) :
    ∀ᵐ ρ ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ w : ℤ × ℤ, (N : ℝ) ≤ supNorm w →
      |(τ π ρ o (P.shift w o) : ℝ) - m w| ≤ ε * supNorm w := by
  have hall : ∀ᵐ ρ ∂μ, ∀ z : ℤ × ℤ,
      Tendsto (fun n : ℕ => (arr π P ρ o z 0 n : ℝ) / n) atTop (𝓝 (m z)) := by
    rw [ae_all_iff]
    intro z
    filter_upwards [hm z] with ρ hρ using hρ o
  filter_upwards [hall] with ρ hρ
  intro ε hε
  have hK₀ := hL.K_nonneg
  -- the scale `M`
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℕ, 1 ≤ M ∧ (2 * K₀ + 1) / M ≤ ε := by
    refine ⟨⌈(2 * K₀ + 1) / ε⌉₊ + 1, by omega, ?_⟩
    have hpos : (0 : ℝ) < (⌈(2 * K₀ + 1) / ε⌉₊ + 1 : ℕ) := by positivity
    rw [div_le_iff₀ hpos]
    have hc := Nat.le_ceil ((2 * K₀ + 1) / ε)
    have h1 : 2 * K₀ + 1 = (2 * K₀ + 1) / ε * ε := by field_simp
    have h2 : (2 * K₀ + 1) / ε * ε ≤ (⌈(2 * K₀ + 1) / ε⌉₊ : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hc hε.le
    push_cast
    nlinarith
  -- the finite set of directions
  have hSfin : (Set.Icc (-(2 * M : ℤ), -(2 * M : ℤ)) ((2 * M : ℤ), (2 * M : ℤ))).Finite :=
    Set.finite_Icc _ _
  have hev : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Set.Icc (-(2 * M : ℤ), -(2 * M : ℤ)) ((2 * M : ℤ), (2 * M : ℤ)),
      |(arr π P ρ o z 0 n : ℝ) / n - m z| < 1 := by
    rw [Filter.eventually_all_finite hSfin]
    intro z _
    filter_upwards [(hρ z).eventually (Metric.ball_mem_nhds (m z) one_pos)] with n hn
    rwa [Real.dist_eq] at hn
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  refine ⟨M * (N₁ + 1), fun w hw => ?_⟩
  -- integer bookkeeping
  have hw' : M * (N₁ + 1) ≤ supNat w := by
    rw [supNorm_eq_supNat] at hw
    exact_mod_cast hw
  obtain ⟨n, hn_def⟩ : ∃ n : ℕ, n = supNat w / M := ⟨_, rfl⟩
  have hMpos : 0 < M := by omega
  have hn1 : N₁ + 1 ≤ n := by
    rw [hn_def, Nat.le_div_iff_mul_le hMpos, mul_comm]
    exact hw'
  have hnpos : 0 < n := by omega
  have hnM : n * M ≤ supNat w := by
    rw [hn_def]
    exact Nat.div_mul_le_self _ _
  have hsup_lt : supNat w < 2 * n * M := by
    have h1 := Nat.lt_div_mul_add (a := supNat w) hMpos
    rw [← hn_def] at h1
    have h2 : M ≤ n * M := Nat.le_mul_of_pos_left M hnpos
    nlinarith
  have hnz : (0 : ℤ) < n := by exact_mod_cast hnpos
  have hsup_lt' : (supNat w : ℤ) < 2 * M * n := by
    have : (supNat w : ℤ) < 2 * n * M := by exact_mod_cast hsup_lt
    linarith
  obtain ⟨z, hz_def⟩ : ∃ z : ℤ × ℤ, z = (w.1 / (n : ℤ), w.2 / (n : ℤ)) := ⟨_, rfl⟩
  obtain ⟨r, hr_def⟩ : ∃ r : ℤ × ℤ, r = w - n • z := ⟨_, rfl⟩
  have hr1 : r.1 = w.1 % (n : ℤ) := by
    rw [hr_def, hz_def, Int.emod_def]
    simp
  have hr2 : r.2 = w.2 % (n : ℤ) := by
    rw [hr_def, hz_def, Int.emod_def]
    simp
  have hr_le : supNorm r ≤ n := by
    rw [supNorm_le_iff]
    constructor
    · rw [hr1, abs_of_nonneg (by exact_mod_cast Int.emod_nonneg _ hnz.ne')]
      exact_mod_cast (Int.emod_lt_of_pos _ hnz).le
    · rw [hr2, abs_of_nonneg (by exact_mod_cast Int.emod_nonneg _ hnz.ne')]
      exact_mod_cast (Int.emod_lt_of_pos _ hnz).le
  have hzS : z ∈ Set.Icc (-(2 * M : ℤ), -(2 * M : ℤ)) ((2 * M : ℤ), (2 * M : ℤ)) := by
    have a1 := abs_fst_le_supNat w
    have a2 := abs_snd_le_supNat w
    have b2 := abs_lt.1 (a2.trans_lt hsup_lt')
    have b1' := abs_lt.1 (a1.trans_lt hsup_lt')
    rw [hz_def, Set.mem_Icc, Prod.mk_le_mk, Prod.mk_le_mk]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [Int.le_ediv_iff_mul_le hnz]; linarith [b1'.1]
    · rw [Int.le_ediv_iff_mul_le hnz]; linarith [b2.1]
    · exact ((Int.ediv_lt_iff_lt_mul hnz).2 (by linarith [b1'.2])).le
    · exact ((Int.ediv_lt_iff_lt_mul hnz).2 (by linarith [b2.2])).le
  -- the three terms
  have hw_eq : w = n • z + r := by rw [hr_def]; abel
  have t1 : |(τ π ρ o (P.shift w o) : ℝ) - τ π ρ o (P.shift (n • z) o)| ≤ K₀ * n := by
    refine (abs_τ_sub_le π hAb hG ρ o _ _).trans ?_
    have : G.dist (P.shift w o) (P.shift (n • z) o) = G.dist o (P.shift r o) := by
      conv_lhs => rw [hw_eq, P.shift_add]
      rw [dist_shift_shift π P hπ hG, G.dist_comm]
    rw [this]
    exact (hK r).trans (mul_le_mul_of_nonneg_left hr_le hK₀)
  have t2 : |(τ π ρ o (P.shift (n • z) o) : ℝ) - n * m z| ≤ n := by
    have h := hN₁ n (by omega) z hzS
    have harr : arr π P ρ o z 0 n = τ π ρ o (P.shift (n • z) o) := by simp [arr, P.shift_zero]
    rw [harr] at h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [div_sub' hn'.ne', abs_div, abs_of_pos hn', div_lt_one hn'] at h
    exact h.le
  have t3 : |(n : ℝ) * m z - m w| ≤ K₀ * n := by
    rw [← hL.nsmul n z]
    refine (hL.lip _ _).trans (mul_le_mul_of_nonneg_left ?_ hK₀)
    have : n • z - w = -r := by rw [hr_def]; abel
    rw [this, supNorm_neg]
    exact hr_le
  have hsum : |(τ π ρ o (P.shift w o) : ℝ) - m w| ≤ (2 * K₀ + 1) * n := by
    calc |(τ π ρ o (P.shift w o) : ℝ) - m w|
        = |((τ π ρ o (P.shift w o) : ℝ) - τ π ρ o (P.shift (n • z) o)) +
            ((τ π ρ o (P.shift (n • z) o) : ℝ) - n * m z) + ((n : ℝ) * m z - m w)| := by
          congr 1; ring
      _ ≤ _ := abs_add_three' _ _ _
      _ ≤ K₀ * n + n + K₀ * n := add_le_add (add_le_add t1 t2) t3
      _ = (2 * K₀ + 1) * n := by ring
  have hnw : (n : ℝ) * M ≤ supNorm w := by
    rw [supNorm_eq_supNat]
    exact_mod_cast hnM
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  calc |(τ π ρ o (P.shift w o) : ℝ) - m w| ≤ (2 * K₀ + 1) * n := hsum
    _ = (2 * K₀ + 1) / M * (n * M) := by field_simp
    _ ≤ (2 * K₀ + 1) / M * supNorm w :=
        mul_le_mul_of_nonneg_left hnw (div_nonneg (by linarith) hMpos'.le)
    _ ≤ ε * supNorm w := mul_le_mul_of_nonneg_right hM (supNorm_nonneg w)

/-- The passage function and the uniform limit: proof of `prop:passage-limit`. -/
theorem passage_limit_proof (hK : External.Kingman.{u}) (hπ : P.Periodic π)
    (hAb : External.Abelian G) [Infinite V] (hG : G.Connected) (μ : Measure (Config G))
    [IsProbabilityMeasure μ] (hinv : P.Invariant μ) (herg : P.Ergodic μ) :
    ∃ f : Plane → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x y, f (x + y) ≤ f x + f y) ∧
      (∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x) ∧
      ∀ o : V, ∀ᵐ ρ ∂μ, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ x : V, R₀ ≤ ‖P.emb x - P.emb o‖ →
        |(τ π ρ o x : ℝ) - f (P.emb x - P.emb o)| ≤ ε * ‖P.emb x - P.emb o‖ := by
  obtain ⟨o₀⟩ : Nonempty V := inferInstance
  choose m hm using fun z => exists_isDirLimit π P hK hπ hAb hG μ hinv herg z
  -- the lattice function is subadditive
  have hLat : ∀ o : V, LatticeSubadditive m
      (G.dist o (P.shift (1, 0) o) + G.dist o (P.shift (0, 1) o)) := fun o =>
    { nonneg := fun z => (hm z).nonneg π P μ
      add_le := fun z w => (hm z).add_le π P hπ hAb hG μ hinv (hm w) (hm (z + w))
      nsmul := fun k z => (hm (k • z)).unique π P μ ((hm z).nsmul π P hG μ k)
      le := fun z => ((hm z).le_dist π P hπ hG μ o).trans (dist_shift_le_supNorm π P hπ hG o z) }
  obtain ⟨f, hfc, hf0, hfadd, hfsmul, hflip', hfm⟩ := (hLat o₀).exists_ext P.coords
  obtain ⟨Lf, hLf0, hflip⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |f x - f y| ≤ L * ‖x - y‖ :=
    ⟨_, mul_nonneg (hLat o₀).K_nonneg (norm_nonneg _), hflip'⟩
  obtain ⟨CB, hCB0, hCB⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, supNorm w ≤ C * ‖P.latVec w‖ :=
    ⟨‖P.coords‖, norm_nonneg _, P.supNorm_le_norm_latVec⟩
  obtain ⟨Cb, hCb, hCb'⟩ : ∃ C : ℝ, 0 < C ∧ ∀ w, ‖P.latVec w‖ ≤ C * supNorm w :=
    ⟨‖P.b 0‖ + ‖P.b 1‖, add_pos_of_pos_of_nonneg (norm_pos_iff.2 (P.b_indep.ne_zero 0))
      (norm_nonneg _), P.norm_latVec_le⟩
  refine ⟨f, hfc, hf0, hfadd, hfsmul, fun o => ?_⟩
  obtain ⟨D, hD0, hD⟩ := P.exists_rep_bound π hπ hG o
  filter_upwards [uniform_lattice π P hπ hAb hG μ m _ hm (hLat o) o
    (dist_shift_le_supNorm π P hπ hG o)] with ρ hρ
  intro ε hε
  obtain ⟨ε', hε', hε'CB⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' * CB ≤ ε / 2 := by
    refine ⟨ε / (2 * (CB + 1)), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨N, hN⟩ := hρ ε' hε'
  refine ⟨max (D + Cb * N) (2 * (D + Lf * D + ε' * CB * D) / ε + 1), fun x hx => ?_⟩
  obtain ⟨hd, he⟩ := hD x
  have hlat : P.emb (P.shift (P.coord x) o) - P.emb o = P.latVec (P.coord x) :=
    P.emb_shift_sub (P.coord x) o
  have hfy : f (P.emb (P.shift (P.coord x) o) - P.emb o) = m (P.coord x) := by
    rw [hlat]
    exact hfm _ _ (P.coords_latVec _)
  have hn1 := hCb' (P.coord x)
  have hn2 := hCB (P.coord x)
  have hxy : ‖P.emb x - P.emb o‖ ≤ ‖P.latVec (P.coord x)‖ + D := by
    calc ‖P.emb x - P.emb o‖
        = ‖(P.emb x - P.emb (P.shift (P.coord x) o)) + (P.emb (P.shift (P.coord x) o) - P.emb o)‖ := by
          congr 1; abel
      _ ≤ ‖P.emb x - P.emb (P.shift (P.coord x) o)‖ + ‖P.emb (P.shift (P.coord x) o) - P.emb o‖ :=
          norm_add_le _ _
      _ ≤ ‖P.latVec (P.coord x)‖ + D := by rw [hlat]; linarith
  have hyx : ‖P.latVec (P.coord x)‖ ≤ ‖P.emb x - P.emb o‖ + D := by
    rw [← hlat]
    calc ‖P.emb (P.shift (P.coord x) o) - P.emb o‖
        = ‖(P.emb x - P.emb o) - (P.emb x - P.emb (P.shift (P.coord x) o))‖ := by
          congr 1; abel
      _ ≤ ‖P.emb x - P.emb o‖ + ‖P.emb x - P.emb (P.shift (P.coord x) o)‖ := norm_sub_le _ _
      _ ≤ ‖P.emb x - P.emb o‖ + D := by linarith
  have hR1 : D + Cb * N ≤ ‖P.emb x - P.emb o‖ := le_trans (le_max_left _ _) hx
  have hR2 : 2 * (D + Lf * D + ε' * CB * D) / ε + 1 ≤ ‖P.emb x - P.emb o‖ :=
    le_trans (le_max_right _ _) hx
  have hwN : (N : ℝ) ≤ supNorm (P.coord x) := by
    have : Cb * N ≤ Cb * supNorm (P.coord x) := by linarith
    exact le_of_mul_le_mul_left this hCb
  have hτ := hN _ hwN
  have t1 : |(τ π ρ o x : ℝ) - τ π ρ o (P.shift (P.coord x) o)| ≤ D :=
    (abs_τ_sub_le π hAb hG ρ o x _).trans hd
  have t3 : |f (P.emb (P.shift (P.coord x) o) - P.emb o) - f (P.emb x - P.emb o)| ≤ Lf * D := by
    refine (hflip _ _).trans ?_
    have : ‖(P.emb (P.shift (P.coord x) o) - P.emb o) - (P.emb x - P.emb o)‖ =
        ‖P.emb x - P.emb (P.shift (P.coord x) o)‖ := by
      rw [← norm_neg]; congr 1; abel
    rw [this]
    exact mul_le_mul_of_nonneg_left he hLf0
  have hsum : |(τ π ρ o x : ℝ) - f (P.emb x - P.emb o)| ≤
      D + ε' * supNorm (P.coord x) + Lf * D := by
    calc |(τ π ρ o x : ℝ) - f (P.emb x - P.emb o)|
        = |((τ π ρ o x : ℝ) - τ π ρ o (P.shift (P.coord x) o)) +
            ((τ π ρ o (P.shift (P.coord x) o) : ℝ) - m (P.coord x)) +
            (f (P.emb (P.shift (P.coord x) o) - P.emb o) - f (P.emb x - P.emb o))| := by
          rw [hfy]; congr 1; ring
      _ ≤ _ := abs_add_three' _ _ _
      _ ≤ D + ε' * supNorm (P.coord x) + Lf * D := add_le_add (add_le_add t1 hτ) t3
  have hsw : supNorm (P.coord x) ≤ CB * (‖P.emb x - P.emb o‖ + D) :=
    hn2.trans (mul_le_mul_of_nonneg_left hyx hCB0)
  have hconst : D + Lf * D + ε' * CB * D ≤ ε / 2 * ‖P.emb x - P.emb o‖ := by
    have h1 : 2 * (D + Lf * D + ε' * CB * D) / ε ≤ ‖P.emb x - P.emb o‖ := by linarith
    rw [div_le_iff₀ hε] at h1
    linarith
  calc |(τ π ρ o x : ℝ) - f (P.emb x - P.emb o)| ≤ D + ε' * supNorm (P.coord x) + Lf * D := hsum
    _ ≤ D + ε' * (CB * (‖P.emb x - P.emb o‖ + D)) + Lf * D := by
        have := mul_le_mul_of_nonneg_left hsw hε'.le
        linarith
    _ = (D + Lf * D + ε' * CB * D) + (ε' * CB) * ‖P.emb x - P.emb o‖ := by ring
    _ ≤ ε / 2 * ‖P.emb x - P.emb o‖ + ε / 2 * ‖P.emb x - P.emb o‖ :=
        add_le_add hconst (mul_le_mul_of_nonneg_right hε'CB (norm_nonneg _))
    _ = ε * ‖P.emb x - P.emb o‖ := by ring

end Rotor
