/-
Extension of a subadditive function on the lattice `ℤ²` to a continuous, subadditive,
positively homogeneous function on the plane.  This is the "usual argument" of the proof
of `prop:passage-limit` (`rotor.tex:1108-1110`): the limit along the integer multiples
of the coordinate vector of a point exists by Fekete's lemma, the floor errors are bounded,
and the resulting function is Lipschitz.
-/
import Rotor.Support.LatticeGeom

open Filter Topology

namespace Rotor

/-- Scaling the argument of a floor by `θ` versus by `⌊n θ⌋₊` (drafted by the GLM fleet). -/
theorem floor_scale_diff (θ x : ℝ) (hθ : 0 < θ) (n : ℕ) :
    |(⌊(n : ℝ) * θ * x⌋ : ℝ) - ⌊(⌊(n : ℝ) * θ⌋₊ : ℝ) * x⌋| ≤ |x| + 1 := by
  have h2 :
      |(n : ℝ) * θ * x - (⌊(n : ℝ) * θ⌋₊ : ℝ) * x| ≤ |x| := by
    rw [← sub_mul, abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (Nat.abs_sub_floor_le (mul_nonneg (Nat.cast_nonneg n) hθ.le))
      (abs_nonneg x)
  obtain ⟨hx1, hx2⟩ := abs_le.1 h2
  have f1 := Int.floor_le ((n : ℝ) * θ * x)
  have f2 := Int.lt_floor_add_one ((n : ℝ) * θ * x)
  have f3 := Int.floor_le ((⌊(n : ℝ) * θ⌋₊ : ℝ) * x)
  have f4 := Int.lt_floor_add_one ((⌊(n : ℝ) * θ⌋₊ : ℝ) * x)
  rw [abs_le]
  constructor <;> linarith only [hx1, hx2, f1, f2, f3, f4]
/-- The lattice point below a coordinate vector. -/
noncomputable def latt (c : Fin 2 → ℝ) : ℤ × ℤ := (⌊c 0⌋, ⌊c 1⌋)

theorem latt_zero : latt 0 = 0 := by simp [latt]

theorem latt_add (c d : Fin 2 → ℝ) :
    ∃ e : ℤ × ℤ, latt (c + d) = latt c + latt d + e ∧ supNorm e ≤ 1 := by
  refine ⟨latt (c + d) - latt c - latt d, by abel, ?_⟩
  have key : ∀ a b : ℝ, |((⌊a + b⌋ - ⌊a⌋ - ⌊b⌋ : ℤ) : ℝ)| ≤ 1 := fun a b => by
    have h1 := Int.le_floor_add a b
    have h2 := Int.le_floor_add_floor a b
    have h3 : (-1 : ℤ) ≤ ⌊a + b⌋ - ⌊a⌋ - ⌊b⌋ := by omega
    have h4 : ⌊a + b⌋ - ⌊a⌋ - ⌊b⌋ ≤ 1 := by omega
    rw [abs_le]
    constructor <;> exact_mod_cast ‹_›
  rw [supNorm_le_iff]
  exact ⟨key (c 0) (d 0), key (c 1) (d 1)⟩

theorem abs_floor_le (t : ℝ) : |(⌊t⌋ : ℝ)| ≤ |t| + 1 := by
  have f1 := Int.floor_le t
  have f2 := Int.lt_floor_add_one t
  rw [abs_le]
  constructor
  · linarith [neg_abs_le t]
  · linarith [le_abs_self t]

theorem supNorm_latt_le (c : Fin 2 → ℝ) : supNorm (latt c) ≤ ‖c‖ + 1 := by
  rw [supNorm_le_iff]
  have h0 := norm_le_pi_norm c 0
  have h1 := norm_le_pi_norm c 1
  rw [Real.norm_eq_abs] at h0 h1
  exact ⟨(abs_floor_le _).trans (by linarith), (abs_floor_le _).trans (by linarith)⟩

theorem latt_natCast_smul (n : ℕ) (z : ℤ × ℤ) :
    latt ((n : ℝ) • ![(z.1 : ℝ), (z.2 : ℝ)]) = n • z := by
  have key (a : ℤ) : ⌊(n : ℝ) * (a : ℝ)⌋ = n • a := by
    rw [nsmul_eq_mul, ← Int.cast_natCast (R := ℝ) n,
      ← Int.cast_mul, Int.floor_intCast]
  exact Prod.ext (key z.1) (key z.2)
/-- A nonnegative subadditive function on the lattice, scaling linearly along rays and
bounded by `K` times the sup norm. -/
structure LatticeSubadditive (m : ℤ × ℤ → ℝ) (K : ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ m z
  add_le : ∀ z w, m (z + w) ≤ m z + m w
  nsmul : ∀ (k : ℕ) z, m (k • z) = k * m z
  le : ∀ z, m z ≤ K * supNorm z

namespace LatticeSubadditive

variable {m : ℤ × ℤ → ℝ} {K : ℝ} (h : LatticeSubadditive m K)
include h

theorem zero : m 0 = 0 := by
  have := h.nsmul 0 0
  simpa using this

theorem K_nonneg : 0 ≤ K := by
  have h1 := h.le (1, 0)
  have h2 := h.nonneg (1, 0)
  simp [supNorm] at h1
  linarith

/-- Lipschitz in the sup norm (drafted by the GLM fleet). -/
theorem lip (z w : ℤ × ℤ) : |m z - m w| ≤ K * supNorm (z - w) := by
  have hm1 : m (z - w) ≤ K * supNorm (z - w) := h.le (z - w)
  have hm2 : m (w - z) ≤ K * supNorm (z - w) := by
    rw [supNorm_sub_comm]; exact h.le (w - z)
  rw [abs_sub_le_iff]
  constructor
  · have h1 : m z ≤ m (z - w) + m w := by
      have := h.add_le (z - w) w
      rwa [sub_add_cancel] at this
    linarith
  · have h2 : m w ≤ m (w - z) + m z := by
      have := h.add_le (w - z) z
      rwa [sub_add_cancel] at this
    linarith

theorem latt_add_le (c d : Fin 2 → ℝ) : m (latt (c + d)) ≤ m (latt c) + m (latt d) + K := by
  obtain ⟨e, he, hse⟩ := latt_add c d
  rw [he]
  have h1 := h.add_le (latt c + latt d) e
  have h2 := h.add_le (latt c) (latt d)
  have h3 := h.le e
  have h4 := mul_le_mul_of_nonneg_left hse h.K_nonneg
  linarith

end LatticeSubadditive

section Extension

variable (m : ℤ × ℤ → ℝ) (ξ : Plane →L[ℝ] (Fin 2 → ℝ))

/-- The lattice function along the integer multiples of the coordinates of `x`. -/
noncomputable def latSeq (x : Plane) (n : ℕ) : ℝ := m (latt ((n : ℝ) • ξ x))

/-- The extension of `m` to the plane: the limit of `latSeq / n`. -/
noncomputable def planeExt (x : Plane) : ℝ := limUnder atTop (fun n : ℕ => latSeq m ξ x n / n)

variable {m} {K : ℝ} (h : LatticeSubadditive m K)
include h

theorem LatticeSubadditive.latSeq_add_le (x : Plane) (p q : ℕ) :
    latSeq m ξ x (p + q) ≤ latSeq m ξ x p + latSeq m ξ x q + K := by
  unfold latSeq
  rw [Nat.cast_add, add_smul]
  exact h.latt_add_le _ _

theorem LatticeSubadditive.latSeq_nonneg (x : Plane) (n : ℕ) : 0 ≤ latSeq m ξ x n := h.nonneg _

theorem LatticeSubadditive.latSeq_le (x : Plane) (n : ℕ) :
    latSeq m ξ x n ≤ K * (n * ‖ξ x‖ + 1) := by
  unfold latSeq
  calc m _ ≤ K * supNorm (latt ((n : ℝ) • ξ x)) := h.le _
    _ ≤ K * (‖(n : ℝ) • ξ x‖ + 1) := mul_le_mul_of_nonneg_left (supNorm_latt_le _) h.K_nonneg
    _ = K * (n * ‖ξ x‖ + 1) := by rw [norm_smul, Real.norm_natCast]

/-- Fekete's lemma: the sequence converges to the extension. -/
theorem LatticeSubadditive.tendsto_latSeq (x : Plane) :
    Tendsto (fun n : ℕ => latSeq m ξ x n / n) atTop (𝓝 (planeExt m ξ x)) := by
  apply tendsto_nhds_limUnder
  have hu : Subadditive (fun n => latSeq m ξ x n + K) := fun p q => by
    simpa only [add_assoc, add_left_comm, add_comm] using
      add_le_add_right (h.latSeq_add_le ξ x p q) K
  have hbdd :
      BddBelow (Set.range fun n : ℕ => (latSeq m ξ x n + K) / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg
      (add_nonneg (h.latSeq_nonneg ξ x n) h.K_nonneg)
      (Nat.cast_nonneg _)
  exact ⟨hu.lim, by
    simpa only [sub_zero, ← sub_div, add_sub_cancel_right] using
      (hu.tendsto_lim hbdd).sub
        (tendsto_const_div_atTop_nhds_zero_nat K)⟩
theorem LatticeSubadditive.planeExt_nonneg (x : Plane) : 0 ≤ planeExt m ξ x :=
  ge_of_tendsto' (h.tendsto_latSeq ξ x)
    (fun n => div_nonneg (h.latSeq_nonneg ξ x n) (Nat.cast_nonneg _))

theorem LatticeSubadditive.planeExt_le (x : Plane) : planeExt m ξ x ≤ K * ‖ξ x‖ := by
  have hK := h.K_nonneg
  have hlim : Tendsto (fun n : ℕ => K * ‖ξ x‖ + K / n) atTop (𝓝 (K * ‖ξ x‖ + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat K)
  rw [add_zero] at hlim
  refine le_of_tendsto_of_tendsto' (h.tendsto_latSeq ξ x) hlim (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, div_zero, div_zero, add_zero]
    positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    have := h.latSeq_le ξ x n
    calc latSeq m ξ x n ≤ K * (n * ‖ξ x‖ + 1) := this
      _ = (K * ‖ξ x‖ + K / n) * n := by field_simp

theorem LatticeSubadditive.planeExt_add_le (x y : Plane) :
    planeExt m ξ (x + y) ≤ planeExt m ξ x + planeExt m ξ y := by
  have hlim : Tendsto (fun n : ℕ => latSeq m ξ x n / n + latSeq m ξ y n / n + K / n) atTop
      (𝓝 (planeExt m ξ x + planeExt m ξ y + 0)) :=
    ((h.tendsto_latSeq ξ x).add (h.tendsto_latSeq ξ y)).add
      (tendsto_const_div_atTop_nhds_zero_nat K)
  rw [add_zero] at hlim
  refine le_of_tendsto_of_tendsto' (h.tendsto_latSeq ξ (x + y)) hlim (fun n => ?_)
  rw [← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  unfold latSeq
  rw [map_add, smul_add]
  exact h.latt_add_le _ _

/-- On a point with integer coordinates `z`, the extension is `m z`. -/
theorem LatticeSubadditive.planeExt_eq_of_coords (x : Plane) (z : ℤ × ℤ)
    (hx : ξ x = ![(z.1 : ℝ), (z.2 : ℝ)]) : planeExt m ξ x = m z := by
  refine tendsto_nhds_unique (h.tendsto_latSeq ξ x)
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [latSeq, hx, latt_natCast_smul, h.nsmul,
    mul_div_cancel_left₀ _ hn']
theorem LatticeSubadditive.planeExt_zero : planeExt m ξ 0 = 0 := by
  simpa only [h.zero] using
    h.planeExt_eq_of_coords ξ 0 0 (by ext i; fin_cases i <;> simp)
theorem LatticeSubadditive.planeExt_smul (θ : ℝ) (hθ : 0 ≤ θ) (x : Plane) :
    planeExt m ξ (θ • x) = θ * planeExt m ξ x := by
  rcases hθ.eq_or_lt with rfl | hθ
  · rw [zero_smul, zero_mul, h.planeExt_zero]
  have hlim := h.tendsto_latSeq ξ x
  set k : ℕ → ℕ := fun n => ⌊(n : ℝ) * θ⌋₊ with hk_def
  have hk : Tendsto k atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hθ)
  have hkn : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 θ) := by
    have := (tendsto_nat_floor_mul_div_atTop hθ.le).comp tendsto_natCast_atTop_atTop
    refine this.congr (fun n => ?_)
    simp only [Function.comp, hk_def, mul_comm]
  have h1 : Tendsto (fun n => latSeq m ξ x (k n) / (k n) * ((k n : ℝ) / n)) atTop
      (𝓝 (planeExt m ξ x * θ)) := (hlim.comp hk).mul hkn
  have hc0 := norm_le_pi_norm (ξ x) 0
  have hc1 := norm_le_pi_norm (ξ x) 1
  rw [Real.norm_eq_abs] at hc0 hc1
  have h2 : Tendsto (fun n : ℕ => (latSeq m ξ (θ • x) n - latSeq m ξ x (k n)) / n) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (K * (‖ξ x‖ + 1)))
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    unfold latSeq
    rw [map_smul]
    refine (h.lip _ _).trans (mul_le_mul_of_nonneg_left ?_ h.K_nonneg)
    rw [supNorm_le_iff]
    constructor
    · have := floor_scale_diff θ (ξ x 0) hθ n
      simp only [latt, Prod.fst_sub, Pi.smul_apply, smul_eq_mul, Int.cast_sub]
      rw [← mul_assoc]
      linarith
    · have := floor_scale_diff θ (ξ x 1) hθ n
      simp only [latt, Prod.snd_sub, Pi.smul_apply, smul_eq_mul, Int.cast_sub]
      rw [← mul_assoc]
      linarith
  have h3 := h1.add h2
  rw [add_zero] at h3
  have h4 : Tendsto (fun n : ℕ => latSeq m ξ (θ • x) n / n) atTop (𝓝 (planeExt m ξ x * θ)) := by
    refine h3.congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos (k n) with hk0 | hk0
    · rw [hk0]
      simp [latSeq, latt_zero, h.zero]
    · have hk' : (k n : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
      rw [div_mul_div_comm, mul_comm (k n : ℝ) (n : ℝ), mul_div_mul_right _ _ hk', ← add_div,
        add_sub_cancel]
  rw [tendsto_nhds_unique (h.tendsto_latSeq ξ (θ • x)) h4, mul_comm]

theorem LatticeSubadditive.planeExt_lip (x y : Plane) :
    |planeExt m ξ x - planeExt m ξ y| ≤ K * ‖ξ‖ * ‖x - y‖ := by
  have hK := h.K_nonneg
  have key : ∀ x y : Plane, planeExt m ξ x ≤ planeExt m ξ y + K * ‖ξ‖ * ‖x - y‖ := by
    intro x y
    have h1 := h.planeExt_add_le ξ y (x - y)
    rw [add_sub_cancel] at h1
    have h2 := h.planeExt_le ξ (x - y)
    have h3 := ξ.le_opNorm (x - y)
    have h4 := mul_le_mul_of_nonneg_left h3 hK
    linarith
  rw [abs_sub_le_iff]
  constructor
  · linarith [key x y]
  · have := key y x
    rw [norm_sub_rev] at this
    linarith

theorem LatticeSubadditive.planeExt_continuous : Continuous (planeExt m ξ) := by
  have hK := h.K_nonneg
  refine LipschitzWith.continuous (K := ⟨K * ‖ξ‖, by positivity⟩)
    (LipschitzWith.of_dist_le_mul (fun x y => ?_))
  rw [Real.dist_eq, dist_eq_norm]
  show |planeExt m ξ x - planeExt m ξ y| ≤ K * ‖ξ‖ * ‖x - y‖
  exact h.planeExt_lip ξ x y

/-- The extension theorem. -/
theorem LatticeSubadditive.exists_ext :
    ∃ f : Plane → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x y, f (x + y) ≤ f x + f y) ∧
      (∀ θ : ℝ, 0 ≤ θ → ∀ x, f (θ • x) = θ * f x) ∧
      (∀ x y, |f x - f y| ≤ K * ‖ξ‖ * ‖x - y‖) ∧
      (∀ x (z : ℤ × ℤ), ξ x = ![(z.1 : ℝ), (z.2 : ℝ)] → f x = m z) :=
  ⟨planeExt m ξ, h.planeExt_continuous ξ, h.planeExt_nonneg ξ, h.planeExt_add_le ξ,
    h.planeExt_smul ξ, h.planeExt_lip ξ, h.planeExt_eq_of_coords ξ⟩

end Extension

end Rotor
