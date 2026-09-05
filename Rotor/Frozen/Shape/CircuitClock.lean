/-
Proposition 3.4 of rotor.tex, frozen.  `rotor.tex:1148-1176` (label `prop:circuit-clock`):

  "Suppose $T(n)<\infty$ for every $n$ for a rotor walk on a connected locally
   finite graph.  Then, for every integer $n\geq0$,
   $\sum_{x\in A_n}\deg(x)\leq T(n+1)-T(n)\leq\sum_{x\in A_{n+1}}\deg(x)$.
   Suppose that, for some $\alpha,\beta>0$, $|A_n|=\alpha n^2+o(n^2)$ and
   $\sum_{x\in A_n}\deg(x)=\beta n^2+o(n^2)$.  Then
   $T(n)=\frac\beta3n^3+o(n^3)$ and $\lim_{t\to\infty}|R_t|/t^{2/3}
   =\alpha(3/\beta)^{2/3}$.  If $n^{-1}A_n\to B$ in Hausdorff distance for a
   compact set $B$, then $t^{-1/3}R_t\to(3/\beta)^{1/3}B$ in Hausdorff
   distance."

Deterministic; `emb` is any drawing of the vertices in the plane.  Three
sentences of conclusions, three conjuncts; the `o(·)` statements are limits
of ratios.  The graph is connected and locally finite, finite or infinite, as
the paper says.  The proof uses `lem:one-circuit`, hence the external input
`hFLP` (ruling X-001).
The `External.*` hypotheses are the cited results the paper's proof uses, assumed in
phase one (ruling X-001): they are not derived here and the certificate lists them.
-/
import Rotor.Events
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp
import Rotor.External.Kingman
import Rotor.External.LSS

open Rotor MeasureTheory Filter Topology
open scoped Pointwise

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.circuit_clock (hFLP : External.OneCircuit G) (π : Mechanism G)
    (hG : G.Connected) (ρ : Config G) (o : V) (hT : ∀ n : ℕ, T π ρ o n < ⊤) :
    (∀ n : ℕ, ∑ x ∈ A π ρ o n, G.degree x ≤ (T π ρ o (n + 1)).toNat - (T π ρ o n).toNat ∧
      (T π ρ o (n + 1)).toNat - (T π ρ o n).toNat ≤ ∑ x ∈ A π ρ o (n + 1), G.degree x) ∧
    (∀ α β : ℝ, 0 < α → 0 < β →
      Tendsto (fun n : ℕ => ((A π ρ o n).card : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 α) →
      Tendsto (fun n : ℕ => ((∑ x ∈ A π ρ o n, G.degree x : ℕ) : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 β) →
      Tendsto (fun n : ℕ => (((T π ρ o n).toNat : ℕ) : ℝ) / (n : ℝ) ^ 3) atTop (𝓝 (β / 3)) ∧
      Tendsto (fun t : ℕ => ((R π ρ o t).card : ℝ) / (t : ℝ) ^ (2 / 3 : ℝ)) atTop
        (𝓝 (α * (3 / β) ^ (2 / 3 : ℝ)))) ∧
    (∀ α β : ℝ, 0 < α → 0 < β →
      Tendsto (fun n : ℕ => ((A π ρ o n).card : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 α) →
      Tendsto (fun n : ℕ => ((∑ x ∈ A π ρ o n, G.degree x : ℕ) : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 β) →
      ∀ (emb : V → Plane) (B : Set Plane), IsCompact B →
      Tendsto (fun n : ℕ => Metric.hausdorffDist ((n : ℝ)⁻¹ • (emb '' (A π ρ o n : Set V))) B)
        atTop (𝓝 0) →
      Tendsto (fun t : ℕ => Metric.hausdorffDist
        (((t : ℝ) ^ (-(1 / 3 : ℝ))) • (emb '' (R π ρ o t : Set V))) (((3 / β) ^ (1 / 3 : ℝ)) • B))
        atTop (𝓝 0))
-- FROZEN-STATEMENT-END
:= by sorry
