/-
The dual configuration on the square lattice, `rotor.tex:1517-1556`
(Section 5.1, `ssec:faces`):

  "The dual lattice has the faces of `ℤ²` as its vertices, with two faces
   adjacent when they share an edge.  Identify the face centered at
   `z + (1/2, 1/2)` with `z ∈ ℤ²`.  Rotate each directed edge `e = v → w`
   counterclockwise through `90°` about its midpoint.  The resulting dual edge
   runs from the face on the right of `e` to the face on its left, and is open
   when `r_v(w) ∈ {2, 3}`."

  M-019  Faces are indexed by `Site`; the face on the right of `v → v + d`,
         `d = (dx, dy)`, is `v + ((dx + dy - 1)/2, (dy - dx - 1)/2)` and the
         face on the left is that face moved across the edge, `- (dy, -dx)`.
         Every directed dual edge `f → g` between adjacent faces is the
         rotation of exactly one directed primal edge, `primalTail f g →
         primalTail f g + dirVec (primalDir f g)`, and it is open when the rank
         of that primal edge is `2` or `3`.
-/
import Rotor.Percolation

namespace Rotor

/-- The face on the right of the directed edge `v → v + dirVec a`. -/
def rightFace (v : Site) (a : Dir) : Site :=
  let d := dirVec a
  (v.1 + (d.1 + d.2 - 1) / 2, v.2 + (d.2 - d.1 - 1) / 2)

/-- The face on the left of the directed edge `v → v + dirVec a`. -/
def leftFace (v : Site) (a : Dir) : Site :=
  let d := dirVec a
  (rightFace v a).1 - d.2 + 0 * d.1 |> fun x => (x, (rightFace v a).2 + d.1)

/-- The dual edge of `v → v + dirVec a`, from the right face to the left face. -/
def dualEdge (v : Site) (a : Dir) : Site × Site := (rightFace v a, leftFace v a)

/-- The tail of the primal edge whose rotation is the dual edge `f → g`. -/
def primalTail (f g : Site) : Site :=
  let δ := g - f
  (f.1 + (δ.1 - δ.2 + 1) / 2, f.2 + (δ.1 + δ.2 + 1) / 2)

/-- The direction of the primal edge whose rotation is the dual edge `f → g`:
`δ` rotated clockwise. -/
def primalDir (f g : Site) : Dir :=
  let δ := g - f
  dirOf (δ.2, -δ.1)

/-- The dual edge `f → g` is open: the primal edge it rotates has rank `2` or
`3` after the initial rotor (ruling M-019). -/
def DualOpen (ρ : Config squareGraph) (f g : Site) : Prop :=
  let v := primalTail f g
  let a := primalDir f g
  rank clockwise ρ v (nbr v a) = 2 ∨ rank clockwise ρ v (nbr v a) = 3

/-- A directed path of open dual edges: distinct faces, consecutive ones
adjacent, each step an open dual edge. -/
def IsOpenDualPath (ρ : Config squareGraph) (q : List Site) : Prop :=
  IsPath squareGraph q ∧ q.IsChain (DualOpen ρ)

/-- The five-edge path `P_⋆` of `eq:square-five-edge-path`. -/
def pstar : List Site := [(0, 0), (1, 0), (1, 1), (0, 1), (0, 2), (1, 2)]

/-- `l` contains a translate of `P_⋆`, in either direction, as a consecutive
subpath. -/
def ContainsPattern (l : List Site) : Prop :=
  ∃ (i : ℕ) (z : Site), (l.drop i).take 6 = pstar.map (· + z) ∨
    (l.drop i).take 6 = (pstar.map (· + z)).reverse

/-- `x` is joined to `{y : |y-x|_∞ = r}` inside the box by an open path
containing no translate of `P_⋆` in either direction as a consecutive subpath
(`eq:square-constrained-bond-tail`). -/
def constrainedCrossing (x : Site) (r : ℕ) : Set BondConfig :=
  {ω | ∃ l : List Site, IsOpenPath ω l ∧ l.head? = some x ∧ (∀ y ∈ l, linfDist y x ≤ r) ∧
    (∃ y ∈ l.getLast?, linfDist y x = r) ∧ ¬ ContainsPattern l}

/-- The directed edge from `l[i]` to `l[i+1]` as a direction. -/
def stepDir (l : List Site) (i : ℕ) : Dir :=
  match l[i]?, l[i + 1]? with
  | some u, some v => dirOf (v - u)
  | _, _ => 0

end Rotor
