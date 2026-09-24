import Rotor.Support.SquareExits
import Rotor.Support.SquareDual

/-!
The finite computation behind Lemma 5.4 (iii) (`rotor.tex:1530-1540`): around a lattice vertex
with initial rotor direction `d`, the side `k` of the dual square is open when the rank of the
primal edge in direction `k` is `2` or `3`.  Opposite sides have opposite states, and the
current side `E = a` is open with probability exactly `1/2` given any information about the
sides `N = a - 1` and `S = a + 1`.
-/

open Finset

namespace Rotor

/-- The side `k` of the dual square at a vertex with initial rotor direction `d` is open. -/
def openAt (k d : Dir) : Bool :=
  decide (((k - d).val + 3) % 4 + 1 = 2 ∨ ((k - d).val + 3) % 4 + 1 = 3)

theorem dualOpen_iff_openAt (ρ : Config squareGraph) (v : Site) (k : Dir) :
    DualOpen ρ (dualEdge v k).1 (dualEdge v k).2 ↔ openAt k (dir0 ρ v) = true := by
  rw [dualEdge, dualOpen_iff, rank_clockwise, openAt, decide_eq_true_iff]
  rfl

/-- Opposite sides have opposite states. -/
theorem openAt_opp (a d : Dir) : openAt (a + 2) d = !openAt a d := by
  revert a d; decide

/-- The information about one side: `mt` says it was tested open, `mf` tested closed. -/
def sideOK (mt mf x : Bool) : Prop := (mt = true → x = true) ∧ (mf = true → x = false)

instance (mt mf x : Bool) : Decidable (sideOK mt mf x) := by unfold sideOK; infer_instance

/-- Given any information about the sides `N` and `S`, exactly half of the consistent rotor
directions open the side `E`. -/
theorem half_count (a : Dir) (m₁t m₁f m₂t m₂f : Bool) :
    2 * (univ.filter (fun d : Dir => (sideOK m₁t m₁f (openAt (a - 1) d) ∧
        sideOK m₂t m₂f (openAt (a + 1) d)) ∧ openAt a d = true)).card =
      (univ.filter (fun d : Dir => sideOK m₁t m₁f (openAt (a - 1) d) ∧
        sideOK m₂t m₂f (openAt (a + 1) d))).card := by
  revert a m₁t m₁f m₂t m₂f; decide

/-- A side other than `E` and `W` is `N` or `S`. -/
theorem side_cases (a k : Dir) (h1 : k ≠ a) (h2 : k ≠ a + 2) : k = a - 1 ∨ k = a + 1 := by
  revert a k; decide

end Rotor
