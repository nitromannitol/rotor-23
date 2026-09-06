/-
Lemma 5.5 of rotor.tex, frozen.  `rotor.tex:1945-1949` (label `lem:square-active-list`):

  "If $W$ or $S$ was tested closed before $E$ is tested, then the active list
   is $(E)$ immediately before $E$ is selected for testing.  At most one of $W$
   and $S$ was tested closed earlier."

Two sentences, two conjuncts, for every stage `n` at which a current edge `E`
exists; `sideW` and `sideS` are the sides `W` and `S` of the square of `E`.
-/
import Rotor.Exploration
import Rotor.Support.ActiveListLemma

open Rotor

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.square_active_list (f d : Site) (hd : squareGraph.Adj f (f + d))
    (ρ : Config squareGraph) (n : ℕ) (e : Site × Site) (rest : List (Site × Site))
    (he : (explore ρ f d n).active = e :: rest) :
    ((TestedAs (explore ρ f d n).tested (sideW e.1 e.2) false ∨
        TestedAs (explore ρ f d n).tested (sideS e.1 e.2) false) → rest = []) ∧
    ¬ (TestedAs (explore ρ f d n).tested (sideW e.1 e.2) false ∧
        TestedAs (explore ρ f d n).tested (sideS e.1 e.2) false)
-- FROZEN-STATEMENT-END
:= square_active_list_proof f d hd ρ n e rest he
