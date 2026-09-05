/-
Lemma 5.2 of rotor.tex, frozen.  `rotor.tex:1638-1644` (label `lem:square-dual-path`):

  "Let $m\geq1$ be an integer and let $x_0,\ldots,x_m$ be a live
   nearest-neighbor path in $\Z^2$.  Then there is a directed path of open dual
   edges from the face on the right of $x_0\to x_1$ to the face on the right of
   $x_{m-1}\to x_m$."

The path is `l = [x_0, …, x_m]` with `m + 1 = l.length ≥ 2`; its first and
last edges are read off through `l[i]?`.  The dual path has distinct faces
(`IsOpenDualPath`), as the word "path" requires (`rotor.tex:405-407`).
-/
import Rotor.Dual

open Rotor

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.square_dual_path (ρ : Config squareGraph) (l : List Site)
    (hl : IsPath squareGraph l) (hlive : IsLive clockwise ρ l) (hm : 2 ≤ l.length)
    (x₀ x₁ y₀ y₁ : Site) (h0 : l[0]? = some x₀) (h1 : l[1]? = some x₁)
    (hy0 : l[l.length - 2]? = some y₀) (hy1 : l[l.length - 1]? = some y₁) :
    ∃ q : List Site, IsOpenDualPath ρ q ∧
      q.head? = some (rightFace x₀ (dirOf (x₁ - x₀))) ∧
      q.getLast? = some (rightFace y₀ (dirOf (y₁ - y₀)))
-- FROZEN-STATEMENT-END
:= by sorry
