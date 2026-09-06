import Rotor.Support.PathReductionIII

/-!
The shape conclusions of Theorem 1.1 with the sandwich clause (`rotor.tex:120-124`, the
second display of the theorem): the proof of `prop:path-reduction`(iii) with the sandwich
`(1-ε) n B ⊆ A_n ⊆ (1+ε) n B` retained from `prop:circuit-shape`.
-/

open Filter Topology MeasureTheory
open scoped Pointwise

universe u

namespace Rotor

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G)

theorem shape_sandwich_proof (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
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
          (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop,
            (∀ x : V, P.emb x - P.emb o ∈ ((1 - ε) * n) • B → x ∈ A π ρ o n) ∧
            (∀ x ∈ A π ρ o n, P.emb x - P.emb o ∈ ((1 + ε) * n) • B)) ∧
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
  refine ⟨hT, hρh, ?_, hclock3 _ _ hα hβ hαn hβn (fun x => P.emb x - P.emb o) _ hBc hρh, hcard⟩
  intro ε hε hε1
  filter_upwards [hρs ε hε hε1, Filter.eventually_ge_atTop 1] with n hn hn1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmem : ∀ (t : ℝ), 0 < t → ∀ y : Plane, y ∈ t • {x : Plane | f x ≤ 1} ↔ f y ≤ t := by
    intro t ht y
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hfsmul t ht.le]
      exact mul_le_of_le_one_right ht.le hw
    · intro hy
      refine ⟨t⁻¹ • y, ?_, by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]⟩
      show f (t⁻¹ • y) ≤ 1
      rw [hfsmul t⁻¹ (inv_nonneg.2 ht.le)]
      exact inv_mul_le_one_of_le₀ hy ht.le
  refine ⟨fun x hx => hn.1 x ((hmem _ (by nlinarith) _).1 hx),
    fun x hx => (hmem _ (by nlinarith) _).2 (hn.2 x hx)⟩



end Rotor
