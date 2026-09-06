import Rotor.Support.StuckWalk
import Rotor.Support.BallGrowth

/-!
Proposition 4.2, `prop:degree-three-passage` (`rotor.tex:1385-1460`): exponential decay of
live paths on a doubly periodic graph of maximum degree three with independent uniform rotors.
The union bound over `Γ_R` is realised as the union over the self-avoiding extensions of
`[v, u]` by `R - 1` vertices; `P{γ is live} = wt γ` is `uniformLaw_liveRevSet`; the
sub-stochastic chain and the block argument give `eq:chain-survival`.
-/

open Finset MeasureTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

omit [G.LocallyFinite] in
theorem liveRev_of_forall (ρ : Config G) : ∀ (m : List V),
    (∀ i (h : i + 2 < m.length), LiveAt π ρ (m[i + 2]) (m[i + 1]) (m[i])) → LiveRev π ρ m
  | c :: b :: a :: rest, h => by
    rw [liveRev_cons₃]
    refine ⟨h 0 (by simp), ?_⟩
    exact liveRev_of_forall ρ (b :: a :: rest)
      (fun i hi => h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega))
  | [], _ => trivial
  | [_], _ => trivial
  | [_, _], _ => trivial

omit [G.LocallyFinite] in
theorem liveAt_of_isLive {ρ : Config G} {l : List V} (hl : IsLive π ρ l) {j : ℕ} (hj0 : 0 < j)
    (hj : j + 1 < l.length) :
    LiveAt π ρ (l[j - 1]'(by omega)) (l[j]'(by omega)) (l[j + 1]'hj) := by
  obtain ⟨_, h⟩ := hl j hj0 hj
  exact h

omit [G.LocallyFinite] in
/-- The reversal of a prefix of a live path is live in the head-first sense. -/
theorem liveRev_reverse_take {ρ : Config G} {l : List V} (hl : IsLive π ρ l) {R : ℕ}
    (hR : R + 1 ≤ l.length) : LiveRev π ρ (l.take (R + 1)).reverse := by
  refine liveRev_of_forall π ρ _ (fun i hi => ?_)
  have hlen : (l.take (R + 1)).length = R + 1 := by rw [List.length_take]; omega
  have hlen' : (l.take (R + 1)).reverse.length = R + 1 := by rw [List.length_reverse, hlen]
  rw [hlen'] at hi
  have key := liveAt_of_isLive π hl (j := R - i - 1) (by omega) (by omega)
  simp only [List.getElem_reverse, List.getElem_take]
  convert key using 2 <;> omega

omit [DecidableEq V] [G.LocallyFinite] in
theorem dist_getElem_le (hG : G.Connected) : ∀ (l : List V), l.IsChain G.Adj →
    ∀ (i : ℕ) (hi : i < l.length) (h0 : 0 < l.length), G.dist (l[0]'h0) (l[i]'hi) ≤ i
  | [], _, i, hi, _ => by simp at hi
  | [a], _, i, hi, _ => by
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simp
  | a :: b :: rest, hch, i, hi, h0 => by
    match i with
    | 0 => simp
    | k + 1 =>
      have hk : k < (b :: rest).length := by simp only [List.length_cons] at hi ⊢; omega
      have hrec := dist_getElem_le hG (b :: rest) hch.of_cons k hk (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hrec ⊢
      calc G.dist a ((b :: rest)[k]'hk) ≤ G.dist a b + G.dist b ((b :: rest)[k]'hk) :=
          hG.dist_triangle
        _ ≤ 1 + k := by
            rw [SimpleGraph.dist_eq_one_iff_adj.2 hch.rel]
            omega
        _ = k + 1 := by ring

omit [DecidableEq V] [G.LocallyFinite] in
theorem adm_pair {u v : V} (huv : G.Adj u v) : Adm G [v, u] := by
  refine ⟨?_, ?_, by simp⟩
  · simp [huv.ne.symm]
  · exact List.isChain_cons.2 ⟨fun y hy => by simp at hy; subst hy; exact huv.symm,
      List.isChain_singleton u⟩

/-- Stopping a live path when it first reaches distance `R` gives an element of `Γ_R`; its
first `R + 1` vertices, reversed, form a self-avoiding extension of `[v, u]`. -/
theorem liveReachEvent_subset (hG : G.Connected) {u v : V} (huv : G.Adj u v) {R : ℕ}
    (hR : 1 ≤ R) :
    liveReachEvent π u v R ⊆ ⋃ l ∈ NodupExt G [v, u] (R - 1), liveRevSet π l := by
  intro ρ hρ
  obtain ⟨l, hpath, hlive, hhead, hsecond, w, hw, hdist⟩ := hρ
  obtain ⟨l₁, rfl⟩ := List.head?_eq_some_iff.1 hhead
  obtain ⟨l₂, rfl⟩ : ∃ l₂, l₁ = v :: l₂ := by
    cases l₁ with
    | nil => simp at hsecond
    | cons x l₂ =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsecond
      subst hsecond
      exact ⟨l₂, rfl⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hlen : R + 1 ≤ (u :: v :: l₂).length := by
    have := dist_getElem_le hG _ hpath.2 i hi (by simp)
    simp only [List.getElem_cons_zero] at this
    omega
  rw [Set.mem_iUnion₂]
  refine ⟨((u :: v :: l₂).take (R + 1)).reverse, ?_, liveRev_reverse_take π hlive hlen⟩
  rw [mem_NodupExt_iff (adm_pair huv)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.length_reverse, List.length_take, List.length_cons, List.length_nil] at hlen ⊢
    omega
  · rw [List.drop_reverse]
    have h2 : ((u :: v :: l₂).take (R + 1)).length - (R - 1) = 2 := by
      rw [List.length_take]; omega
    rw [h2, List.take_take, min_eq_left (by omega : 2 ≤ R + 1)]
    simp
  · exact List.nodup_reverse.2 (hpath.1.sublist (List.take_sublist _ _))
  · exact List.isChain_reverse.2 ((hpath.2.take (R + 1)).imp (fun _ _ h => h.symm))

/-- Proposition 4.2. -/
theorem degree_three_passage_proof (P : DoublyPeriodic G) (hG : G.Connected)
    (h3 : ∀ v : V, G.degree v ≤ 3) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (u v : V), G.Adj u v → ∀ R : ℕ, 1 ≤ R →
      uniformLaw π (liveReachEvent π u v R) ≤ ENNReal.ofReal (C * Real.exp (-c * R)) := by
  obtain ⟨Cb, hCb, hball⟩ := exists_ball_bound P hG
  obtain ⟨h, -, hh⟩ := exists_two_pow_gt Cb hCb
  set m : ℕ := 2 * h - 1 with hm
  have hstuck : ∀ q : List V, Adm G q → ∃ j ≤ m, ∃ q' ∈ NodupExt G q j, Stuck G q' :=
    fun q hq => exists_stuck_of_ball_bound h3 hG hball hh q hq
  set θ : ℝ := 1 - (1 / 3) ^ m / 3 with hθ
  have hθ0 : 0 < θ := by
    have : (1 / 3 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [hθ]; linarith
  have hθ1 : θ < 1 := by
    have : (0 : ℝ) < (1 / 3) ^ m := by positivity
    rw [hθ]; linarith
  set c : ℝ := -Real.log θ / (m + 1) with hc
  have hlog : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hc0 : 0 < c := by
    rw [hc]; exact div_pos (by linarith) (by positivity)
  refine ⟨c, θ⁻¹ ^ 2, hc0, by positivity, fun u v huv R hR => ?_⟩
  have hadm : Adm G [v, u] := adm_pair huv
  calc uniformLaw π (liveReachEvent π u v R)
      ≤ uniformLaw π (⋃ l ∈ NodupExt G [v, u] (R - 1), liveRevSet π l) :=
        measure_mono (liveReachEvent_subset π hG huv hR)
    _ ≤ ∑ l ∈ NodupExt G [v, u] (R - 1), uniformLaw π (liveRevSet π l) :=
        measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal (W π [v, u] (R - 1)) := by
        rw [W, ENNReal.ofReal_sum_of_nonneg (fun l _ => wt_nonneg π l)]
        exact sum_congr rfl (fun l hl => uniformLaw_liveRevSet π l (adm_of_mem_NodupExt hadm hl).1)
    _ ≤ ENNReal.ofReal (θ⁻¹ ^ 2 * Real.exp (-c * R)) := by
        apply ENNReal.ofReal_le_ofReal
        set n : ℕ := (R - 1) / (m + 1) with hn
        have h1 : W π [v, u] (R - 1) ≤ W π [v, u] (n * (m + 1)) :=
          W_antitone π h3 hadm (Nat.div_mul_le_self _ _)
        have h2 : W π [v, u] (n * (m + 1)) ≤ θ ^ n * wt π [v, u] := W_blocks π h3 hstuck hadm n
        rw [wt_pair, mul_one] at h2
        have hdm := Nat.div_add_mod (R - 1) (m + 1)
        have hmod := Nat.mod_lt (R - 1) (by omega : 0 < m + 1)
        have hnR : R ≤ (m + 1) * n + (m + 1) := by rw [← hn] at hdm; omega
        have hnR' : (R : ℝ) / (m + 1) - 2 ≤ n := by
          have hm1 : (0 : ℝ) < m + 1 := by positivity
          have : (R : ℝ) ≤ (m + 1) * n + (m + 1) := by exact_mod_cast hnR
          rw [div_sub' hm1.ne', div_le_iff₀ hm1]
          linarith
        have hle : θ ^ (n : ℝ) ≤ θ ^ ((R : ℝ) / (m + 1) - 2) :=
          Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1.le hnR'
        rw [Real.rpow_natCast] at hle
        have heq : θ ^ ((R : ℝ) / (m + 1) - 2) = θ⁻¹ ^ 2 * Real.exp (-c * R) := by
          rw [Real.rpow_def_of_pos hθ0, hc]
          have e1 : Real.log θ * ((R : ℝ) / (m + 1) - 2)
              = (2 : ℕ) * (-Real.log θ) + -(-Real.log θ / (m + 1)) * R := by
            push_cast; ring
          rw [e1, Real.exp_add, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hθ0]
        linarith [h1, h2, hle, heq]

end Rotor
