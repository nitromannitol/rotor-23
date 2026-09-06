import Rotor.Support.CyclicRank
import Rotor.Law

/-!
The transition probabilities of the killed nonbacktracking chain,
`rotor.tex:1295-1330`: for `a, c ∼ b`, `p(a,b,c) = P{r_b(c) < r_b(a)}`, computed from
the uniform initial rotor at `b`.  `eq:mean-continuations`: `Σ_{c} p(a,b,c) = (deg b - 1)/2`.
-/

open Finset MeasureTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

omit [G.LocallyFinite] in
theorem rank_eq_cycRank (ρ : Config G) (v : V) (w : G.neighborSet v) :
    rank π ρ v w = cycRank (π.next v) (π.cyclic v) (ρ v) w := rfl

/-- The initial rotors at `b` for which the exit `c` precedes the entrance `a`. -/
noncomputable def stepSet (b : V) (a c : G.neighborSet b) : Finset (G.neighborSet b) :=
  univ.filter (fun x => cycRank (π.next b) (π.cyclic b) x c < cycRank (π.next b) (π.cyclic b) x a)

open Classical in
/-- `p(a,b,c) = P{r_b(c) < r_b(a)}`, and `0` unless `a, c ∼ b`. -/
noncomputable def pStep (a b c : V) : ℝ :=
  if h : G.Adj b a ∧ G.Adj b c then ((stepSet π b ⟨a, h.1⟩ ⟨c, h.2⟩).card : ℝ) / G.degree b
  else 0

theorem pStep_nonneg (a b c : V) : 0 ≤ pStep π a b c := by
  unfold pStep
  split_ifs
  · positivity
  · exact le_rfl

theorem card_stepSet_le (b : V) (a c : G.neighborSet b) : (stepSet π b a c).card ≤ G.degree b := by
  rw [← G.card_neighborSet_eq_degree]
  exact (card_le_univ _)

theorem pStep_le_one (a b c : V) : pStep π a b c ≤ 1 := by
  unfold pStep
  split_ifs with h
  · have hd : (0 : ℝ) < G.degree b := by
      rw [← G.card_neighborSet_eq_degree]
      exact_mod_cast (Fintype.card_pos_iff (α := G.neighborSet b)).2 ⟨⟨a, h.1⟩⟩
    rw [div_le_one hd]
    exact_mod_cast card_stepSet_le π b _ _
  · exact zero_le_one

theorem stepSet_self (b : V) (a : G.neighborSet b) : stepSet π b a a = ∅ := by
  ext x
  simp [stepSet]

theorem pStep_self (a b : V) : pStep π a b a = 0 := by
  unfold pStep
  split_ifs with h
  · simp [stepSet_self]
  · rfl

theorem pStep_of_not_adj {a b c : V} (h : ¬ (G.Adj b a ∧ G.Adj b c)) : pStep π a b c = 0 := by
  unfold pStep
  rw [dif_neg h]

/-- `eq:mean-continuations`. -/
theorem sum_pStep {a b : V} (ha : G.Adj b a) :
    ∑ c ∈ G.neighborFinset b, pStep π a b c = ((G.degree b : ℝ) - 1) / 2 := by
  rw [Finset.sum_subtype (G.neighborFinset b) (fun c => G.mem_neighborFinset b c)]
  have h1 : ∀ c : G.neighborSet b, pStep π a b c =
      ((stepSet π b ⟨a, ha⟩ c).card : ℝ) / G.degree b := by
    intro c
    unfold pStep
    rw [dif_pos ⟨ha, c.2⟩]
  simp only [h1]
  rw [← Finset.sum_div]
  have h2 := two_mul_sum_card_filter_lt (π.next b) (π.cyclic b) (⟨a, ha⟩ : G.neighborSet b)
  rw [G.card_neighborSet_eq_degree] at h2
  have hd : 1 ≤ G.degree b := by
    rw [← G.card_neighborSet_eq_degree]
    exact (Fintype.card_pos_iff (α := G.neighborSet b)).2 ⟨⟨a, ha⟩⟩
  have h3 : (2 : ℝ) * ∑ c : G.neighborSet b, ((stepSet π b ⟨a, ha⟩ c).card : ℝ) =
      (G.degree b : ℝ) * ((G.degree b : ℝ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, Nat.cast_sub hd, Nat.cast_one] at this
    exact this
  have hd' : (0 : ℝ) < G.degree b := by exact_mod_cast hd
  rw [div_eq_div_iff hd'.ne' two_ne_zero]
  have h4 : (∑ c : G.neighborSet b, ((stepSet π b ⟨a, ha⟩ c).card : ℝ)) * 2 =
      ((G.degree b : ℝ) - 1) * G.degree b := by linarith
  convert h4 using 2

theorem one_div_degree_le_pStep {a b c : V} (ha : G.Adj b a) (hc : G.Adj b c) (hne : c ≠ a) :
    1 / (G.degree b : ℝ) ≤ pStep π a b c := by
  unfold pStep
  rw [dif_pos ⟨ha, hc⟩]
  have hd : (0 : ℝ) < G.degree b := by
    rw [← G.card_neighborSet_eq_degree]
    exact_mod_cast (Fintype.card_pos_iff (α := G.neighborSet b)).2 ⟨⟨a, ha⟩⟩
  rw [div_le_div_iff_of_pos_right hd]
  have hmem : (⟨a, ha⟩ : G.neighborSet b) ∈ stepSet π b ⟨a, ha⟩ ⟨c, hc⟩ := by
    simp only [stepSet, mem_filter, mem_univ, true_and]
    rw [cycRank_self]
    exact cycRank_lt_card _ _ (fun h => hne (congrArg Subtype.val h))
  exact_mod_cast card_pos.2 ⟨_, hmem⟩

/-- The live condition at `b`, entering from `a` and leaving to `c`, in terms of the
initial rotor at `b`. -/
theorem liveAt_iff (ρ : Config G) (a b c : V) :
    LiveAt π ρ a b c ↔ ∃ h : G.Adj b a ∧ G.Adj b c, ρ b ∈ stepSet π b ⟨a, h.1⟩ ⟨c, h.2⟩ := by
  unfold LiveAt rank'
  constructor
  · rintro ⟨hc, ha, hlt⟩
    exact ⟨⟨ha, hc⟩, by simpa [stepSet, rank_eq_cycRank] using hlt⟩
  · rintro ⟨⟨ha, hc⟩, hmem⟩
    exact ⟨hc, ha, by simpa [stepSet, rank_eq_cycRank] using hmem⟩

/-- The uniform rotor at `b` lies in `stepSet` with probability `p(a,b,c)`. -/
theorem uniformAt_stepSet {a b c : V} (h : G.Adj b a ∧ G.Adj b c) :
    uniformAt π b ↑(stepSet π b ⟨a, h.1⟩ ⟨c, h.2⟩) = ENNReal.ofReal (pStep π a b c) := by
  unfold uniformAt pStep
  rw [dif_pos h, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, sum_const, nsmul_eq_mul, G.card_neighborSet_eq_degree]
  have hd : (0 : ℝ) < G.degree b := by
    rw [← G.card_neighborSet_eq_degree]
    exact_mod_cast (Fintype.card_pos_iff (α := G.neighborSet b)).2 ⟨⟨a, h.1⟩⟩
  rw [ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]

end Rotor
