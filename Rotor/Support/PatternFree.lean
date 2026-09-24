import Rotor.Support.ExplProb
import Rotor.Support.DualGuards

/-!
Proposition 5.1 (`prop:square-passage`), part 1: a directed path of open dual edges contains
no translate of `P_⋆` in either direction (`rotor.tex:1673-1676`): three consecutive dual edges
of the pattern share a primal tail, and at most two edges at a vertex have rank `2` or `3`.
-/

open Finset MeasureTheory ENNReal

namespace Rotor

/-! ### No open directed dual path contains the pattern -/

theorem openAt_three (d k₁ k₂ k₃ : Dir) (h12 : k₁ ≠ k₂) (h23 : k₂ ≠ k₃) (h13 : k₁ ≠ k₃) :
    ¬ (openAt k₁ d = true ∧ openAt k₂ d = true ∧ openAt k₃ d = true) := by
  revert d k₁ k₂ k₃; decide

theorem primalTail_add (z a b : Site) : primalTail (z + a) (z + b) = z + primalTail a b := by
  have : z + b - (z + a) = b - a := by abel
  simp only [primalTail, this]
  try (ext <;> simp <;> ring)

theorem primalDir_add (z a b : Site) : primalDir (z + a) (z + b) = primalDir a b := by
  have : z + b - (z + a) = b - a := by abel
  simp only [primalDir, this]

theorem dualOpen_iff_openAt_tail (ρ : Config squareGraph) {a b : Site} (h : squareGraph.Adj a b) :
    DualOpen ρ a b ↔ openAt (primalDir a b) (dir0 ρ (primalTail a b)) = true := by
  have := dualOpen_iff_openAt ρ (primalTail a b) (primalDir a b)
  rw [dualEdge_primal h] at this
  rw [this]

theorem isChain_dualOpen_getElem {ρ : Config squareGraph} {q : List Site}
    (hq : q.IsChain (DualOpen ρ)) {i : ℕ} {a b : Site} (ha : q[i]? = some a)
    (hb : q[i + 1]? = some b) : DualOpen ρ a b := by
  rw [List.isChain_iff_getElem] at hq
  have hi := (List.getElem?_eq_some_iff.1 hb).1
  have := hq i hi
  rw [List.getElem?_eq_getElem (by omega)] at ha
  rw [List.getElem?_eq_getElem hi] at hb
  simp only [Option.some.injEq] at ha hb
  rw [← ha, ← hb]; exact this

/-- Adjacency of two sites differing by a unit vector, by trying the four directions. -/
macro "adj_unit_tac" : tactic => `(tactic| (apply adj_of_unit; first | (left; ext <;> simp <;> omega) | (right; left; ext <;> simp <;> omega) | (right; right; left; ext <;> simp <;> omega) | (right; right; right; ext <;> simp <;> omega)))

/-- Three consecutive open dual edges with a common primal tail are impossible. -/
theorem no_three_open (ρ : Config squareGraph) {v : Site} {a₀ a₁ a₂ a₃ : Site}
    (h01 : squareGraph.Adj a₀ a₁) (h12 : squareGraph.Adj a₁ a₂) (h23 : squareGraph.Adj a₂ a₃)
    (t0 : primalTail a₀ a₁ = v) (t1 : primalTail a₁ a₂ = v) (t2 : primalTail a₂ a₃ = v)
    (d01 : primalDir a₀ a₁ ≠ primalDir a₁ a₂) (d12 : primalDir a₁ a₂ ≠ primalDir a₂ a₃)
    (d02 : primalDir a₀ a₁ ≠ primalDir a₂ a₃)
    (o0 : DualOpen ρ a₀ a₁) (o1 : DualOpen ρ a₁ a₂) (o2 : DualOpen ρ a₂ a₃) : False := by
  rw [dualOpen_iff_openAt_tail ρ h01, t0] at o0
  rw [dualOpen_iff_openAt_tail ρ h12, t1] at o1
  rw [dualOpen_iff_openAt_tail ρ h23, t2] at o2
  exact openAt_three (dir0 ρ v) _ _ _ d01 d12 d02 ⟨o0, o1, o2⟩

theorem pattern_getElem? {q : List Site} {i : ℕ} {P : List Site} (h : (q.drop i).take 6 = P)
    {j : ℕ} (hj : j < 6) : q[i + j]? = P[j]? := by
  rw [← h, List.getElem?_take_of_lt hj, List.getElem?_drop]

/-- `rotor.tex:1673-1676`: no open directed dual path contains a translate of `P_⋆` in either
direction. -/
theorem openDualPath_no_pattern (ρ : Config squareGraph) {q : List Site}
    (hq : IsOpenDualPath ρ q) : ¬ ContainsPattern q := by
  rintro ⟨i, z, h | h⟩
  · have hP : pstar.map (· + z) = [z + (0, 0), z + (1, 0), z + (1, 1), z + (0, 1), z + (0, 2),
        z + (1, 2)] := by simp [pstar, add_comm]
    rw [hP] at h
    have e0 := pattern_getElem? h (j := 0) (by norm_num)
    have e1 := pattern_getElem? h (j := 1) (by norm_num)
    have e2 := pattern_getElem? h (j := 2) (by norm_num)
    have e3 := pattern_getElem? h (j := 3) (by norm_num)
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at e0 e1 e2 e3
    have e2' : q[i + 1 + 1]? = q[i + 2]? := rfl
    have e3' : q[i + 2 + 1]? = q[i + 3]? := rfl
    have o0 := isChain_dualOpen_getElem hq.2 e0 e1
    have o1 := isChain_dualOpen_getElem hq.2 e1 (e2'.trans e2)
    have o2 := isChain_dualOpen_getElem hq.2 e2 (e3'.trans e3)
    refine no_three_open ρ (v := z + (1, 1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ o0 o1 o2
    · adj_unit_tac
    · adj_unit_tac
    · adj_unit_tac
    · rw [primalTail_add]; congr 1
    · rw [primalTail_add]; congr 1
    · rw [primalTail_add]; congr 1
    · rw [primalDir_add, primalDir_add]; decide
    · rw [primalDir_add, primalDir_add]; decide
    · rw [primalDir_add, primalDir_add]; decide
  · have hP : (pstar.map (· + z)).reverse = [z + (1, 2), z + (0, 2), z + (0, 1), z + (1, 1),
        z + (1, 0), z + (0, 0)] := by simp [pstar, add_comm]
    rw [hP] at h
    have e0 := pattern_getElem? h (j := 0) (by norm_num)
    have e1 := pattern_getElem? h (j := 1) (by norm_num)
    have e2 := pattern_getElem? h (j := 2) (by norm_num)
    have e3 := pattern_getElem? h (j := 3) (by norm_num)
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at e0 e1 e2 e3
    have e2' : q[i + 1 + 1]? = q[i + 2]? := rfl
    have e3' : q[i + 2 + 1]? = q[i + 3]? := rfl
    have o0 := isChain_dualOpen_getElem hq.2 e0 e1
    have o1 := isChain_dualOpen_getElem hq.2 e1 (e2'.trans e2)
    have o2 := isChain_dualOpen_getElem hq.2 e2 (e3'.trans e3)
    refine no_three_open ρ (v := z + (1, 2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ o0 o1 o2
    · adj_unit_tac
    · adj_unit_tac
    · adj_unit_tac
    · rw [primalTail_add]; congr 1
    · rw [primalTail_add]; congr 1
    · rw [primalTail_add]; congr 1
    · rw [primalDir_add, primalDir_add]; decide
    · rw [primalDir_add, primalDir_add]; decide
    · rw [primalDir_add, primalDir_add]; decide

end Rotor
