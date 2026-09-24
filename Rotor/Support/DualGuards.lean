/-
Computable guards for the dual configuration and the exploration's square
sides, checked against `rotor.tex:1545-1549` and `rotor.tex:1897-1900`.

Around the origin, the four dual edges are the sides of the unit square with
corners `(0,0), (-1,0), (-1,-1), (0,-1)`: "east side `E` directed north, north
side `N` directed west, west side `W` directed south, and south side `S`
directed east".  When the current edge is the east side, its square's sides
`W` and `S` are the west and south sides; the direction indices run
clockwise (`N, E, S, W` = `0, 1, 2, 3`), so counterclockwise from `E` the
sides are `N, W, S` = `d - 1, d + 2, d + 1`.
-/
import Rotor.Exploration

namespace Rotor

theorem dualEdge_E : dualEdge (0, 0) 1 = ((0, -1), (0, 0)) := by decide
theorem dualEdge_N : dualEdge (0, 0) 0 = ((0, 0), (-1, 0)) := by decide
theorem dualEdge_W : dualEdge (0, 0) 3 = ((-1, 0), (-1, -1)) := by decide
theorem dualEdge_S : dualEdge (0, 0) 2 = ((-1, -1), (0, -1)) := by decide

/-- Every dual edge is the rotation of exactly the primal edge that
`primalTail`/`primalDir` recover. -/
theorem primal_of_dualEdge : ∀ a : Dir,
    primalTail (dualEdge (0, 0) a).1 (dualEdge (0, 0) a).2 = (0, 0) ∧
    primalDir (dualEdge (0, 0) a).1 (dualEdge (0, 0) a).2 = a := by decide

/-- With the east side as the current edge, `sideW` is the west side. -/
theorem sideW_of_E : sideW (0, -1) (0, 0) = ((-1, 0), (-1, -1)) := by decide

/-- With the east side as the current edge, `sideS` is the south side. -/
theorem sideS_of_E : sideS (0, -1) (0, 0) = ((-1, -1), (0, -1)) := by decide

/-- With the north side as the current edge, `sideW` is the south side and
`sideS` is the east side: the relabeling rotates with the current edge. -/
theorem sideW_of_N : sideW (0, 0) (-1, 0) = ((-1, -1), (0, -1)) := by decide
theorem sideS_of_N : sideS (0, 0) (-1, 0) = ((0, -1), (0, 0)) := by decide

/-- The forbidden path `P_⋆` has six vertices, consecutive ones adjacent. -/
theorem pstar_isPath : IsPath squareGraph pstar := by
  refine ⟨by decide, ?_⟩
  decide

end Rotor
