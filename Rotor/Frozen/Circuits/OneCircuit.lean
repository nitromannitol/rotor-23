/-
Lemma 2.1 of rotor.tex, frozen.  `rotor.tex:691-697` (label `lem:one-circuit`):

  "For every integer $n\geq0$ such that $T(n)<\infty$, the walk traverses each
   directed edge at most once during the time interval $T(n)\leq t<T(n+1)$.
   If $T(n+1)<\infty$, then during this interval the walk departs from every
   vertex $x\in A_n$ exactly $\deg(x)$ times."

The paper cites FLP Lemmas 2.1 and 2.4 for this and gives no proof; the
external input `External.OneCircuit` (ruling X-001) is its hypothesis.  The
standing assumptions of Section 2 (`rotor.tex:678-680`) are the binders
`[Infinite V]` and `hG`.  "During `T(n) ≤ t < T(n+1)`" with `T(n+1) = ∞`
is the half-line, which the `ℕ∞` comparison expresses.
-/
import Rotor.Traversal
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.one_circuit (hFLP : External.OneCircuit G) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (ρ : Config G) (o : V) (n : ℕ) (hn : T π ρ o n < ⊤) :
    (∀ s t : ℕ, T π ρ o n ≤ (s : ℕ∞) → s < t → (t : ℕ∞) < T π ρ o (n + 1) →
        traversal π ρ o s ≠ traversal π ρ o t) ∧
    (T π ρ o (n + 1) < ⊤ → ∀ x ∈ A π ρ o n,
        departures π ρ o x (T π ρ o n).toNat (T π ρ o (n + 1)).toNat = G.degree x)
-- FROZEN-STATEMENT-END
:= hFLP π inferInstance hG ρ o n hn
