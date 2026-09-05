/-
Lemma 2.7 of rotor.tex, frozen.  `rotor.tex:883-896` (label `lem:decreasing-positions`):

  "(i) Let $S\subseteq V$ be nonempty and finite and let $y\notin S$.  If a
   particle in a one-particle-at-a-time boundary routing of $S$ visits $y$,
   counting its initial boundary edge as its first step, then there is a live
   path $x_0,x_1,\ldots,x_m=y$ such that $x_0\in S$ and $x_i\notin S$ for
   $1\leq i\leq m$.
   (ii) Let $n\geq1$, suppose that $\Phi^i(\{x\})$ is defined for
   $1\leq i\leq n$, and let $y\in\Phi^n(\{x\})$.  There is a path from $x$ to
   $y$, contained in $\Phi^n(\{x\})$, that is live at all but at most $n-1$
   internal vertices."

In (i) the path has at least two vertices, since $y\notin S$ while $x_0\in S$.
The proof of (ii) uses complete one-particle-at-a-time routings, hence
`lem:boundary-routing` and `External.Abelian`.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed in
phase one (ruling X-001): they are not derived here and the certificate lists them.
`[Infinite V]` and `hG` are the standing assumptions of Section 2 (`rotor.tex:678-680`:
"Throughout this section, `G` is infinite, connected, and locally finite, the rotor
mechanism and initial rotor configuration are fixed and arbitrary").
-/
import Rotor.Traversal
import Rotor.Support.DecreasingPositionsII
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.decreasing_positions (hAb : External.Abelian G) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (ρ : Config G) :
    (∀ (S : Finset V), S.Nonempty → ∀ y ∉ S, ∀ es : List (V × V), IsBoundaryOrder G S es →
        OneVisits π S ρ es y →
        ∃ l : List V, IsPath G l ∧ IsLive π ρ l ∧ 2 ≤ l.length ∧
          (∀ h : 0 < l.length, l.get ⟨0, h⟩ ∈ S) ∧
          (∀ (i : ℕ) (h : i < l.length), 1 ≤ i → l.get ⟨i, h⟩ ∉ S) ∧
          l.getLast? = some y) ∧
    (∀ (x y : V) (n : ℕ), 1 ≤ n → IteratesDefined π ρ {x} n → y ∈ (Φ π ρ)^[n] {x} →
        ∃ l : List V, IsPath G l ∧ l.head? = some x ∧ l.getLast? = some y ∧
          (∀ v ∈ l, v ∈ (Φ π ρ)^[n] {x}) ∧ (liveFailures π ρ l).card ≤ n - 1)
-- FROZEN-STATEMENT-END
:= ⟨fun S _ y hy es hes hvis => decreasing_positions_i π S ρ y hy es hes hvis,
    fun x y n _ hdef hy => decreasing_positions_ii π hAb hG ρ x n y hdef hy⟩
