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

/-!
# Dual-edge and square-side identities

Computable checks, verified by `decide`, of the correspondence between the four directions
around a vertex and the dual edges forming the sides of the unit square used by the
exploration process, together with how the west and south sides of that square relabel as
the current edge rotates. Also checks that the forbidden path `pstar` is a genuine path.
-/

namespace Rotor

/-- The dual edge in direction `E` (index `1`) around the origin is the east side of the
unit square, directed north: from `(0, -1)` to `(0, 0)`. -/
theorem dualEdge_E : dualEdge (0, 0) 1 = ((0, -1), (0, 0)) := by decide

/-- The dual edge in direction `N` (index `0`) around the origin is the north side of the
unit square, directed west: from `(0, 0)` to `(-1, 0)`. -/
theorem dualEdge_N : dualEdge (0, 0) 0 = ((0, 0), (-1, 0)) := by decide

/-- The dual edge in direction `W` (index `3`) around the origin is the west side of the
unit square, directed south: from `(-1, 0)` to `(-1, -1)`. -/
theorem dualEdge_W : dualEdge (0, 0) 3 = ((-1, 0), (-1, -1)) := by decide

/-- The dual edge in direction `S` (index `2`) around the origin is the south side of the
unit square, directed east: from `(-1, -1)` to `(0, -1)`. -/
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

/-- With the north side as the current edge, `sideS` is the east side. -/
theorem sideS_of_N : sideS (0, 0) (-1, 0) = ((0, -1), (0, 0)) := by decide

/-- The forbidden path `P_⋆` has six vertices, consecutive ones adjacent. -/
theorem pstar_isPath : IsPath squareGraph pstar := by
  refine ⟨by decide, ?_⟩
  decide

end Rotor
