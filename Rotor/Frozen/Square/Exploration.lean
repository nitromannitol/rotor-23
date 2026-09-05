/-
Lemma 5.4 of rotor.tex, frozen.  `rotor.tex:1902-1913` (label `lem:square-exploration`):

  "(i) No bond is tested twice.
   (ii) If the exploration terminates, then every face reachable from $f$ by
   an open directed path is visited or lies in a finite component of the
   complement of the visited set.
   (iii) Given the outcomes of all earlier tests, $E$ is open with probability
   $1$, $0$, or $1/2$ according as $W$ was tested closed, tested open, or not
   tested."

The exploration starts at the face `f` along the dual edge `f → f + d`.  In
(i) a bond is the undirected dual edge `s(a, b)`.  In (iii) the earlier
outcomes are a history `h`, the state given `h` is `replay f d h` (ruling
M-021), and the three cases are three conjuncts: on the event that the first
`h.length` outcomes are `h`, the current edge `E` is open with probability
`1`, `0`, or `1/2` of that event.
-/
import Rotor.Exploration

open Rotor MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.square_exploration (f d : Site) (hd : squareGraph.Adj f (f + d)) :
    (∀ (ρ : Config squareGraph) (n : ℕ),
        ((explore ρ f d n).tested.map (fun t => s(t.1, t.2.1))).Nodup) ∧
    (∀ (ρ : Config squareGraph) (n : ℕ), (explore ρ f d n).active = [] →
        ∀ g : Site, DualReachable ρ f g →
          g ∈ (explore ρ f d n).visited ∨ InFiniteComponent (explore ρ f d n).visited g) ∧
    (∀ (h : List Bool) (e : Site × Site) (rest : List (Site × Site)),
        (replay f d h).active = e :: rest →
        (TestedAs (replay f d h).tested (sideW e.1 e.2) false →
          uniformLaw clockwise {ρ | history ρ f d h.length = h ∧ DualOpen ρ e.1 e.2} =
            uniformLaw clockwise {ρ | history ρ f d h.length = h}) ∧
        (TestedAs (replay f d h).tested (sideW e.1 e.2) true →
          uniformLaw clockwise {ρ | history ρ f d h.length = h ∧ DualOpen ρ e.1 e.2} = 0) ∧
        (¬ TestedAs (replay f d h).tested (sideW e.1 e.2) false →
          ¬ TestedAs (replay f d h).tested (sideW e.1 e.2) true →
          uniformLaw clockwise {ρ | history ρ f d h.length = h ∧ DualOpen ρ e.1 e.2} =
            (1 / 2) * uniformLaw clockwise {ρ | history ρ f d h.length = h}))
-- FROZEN-STATEMENT-END
:= by sorry
