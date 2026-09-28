import Rotor.External.Kingman
import LatticeProb.Prob.Kingman

/-!
# Kingman's subadditive ergodic theorem from the library

`External.Kingman` proved from the shared library's Kingman subadditive ergodic theorem
(`LatticeProb.Prob.Kingman`, Kingman 1968 Theorems 3 and 5).

Rotor's two-index array `X m n` reduces to the library's single-index family `g n := X 0 n` by
the standard textbook substitution: the stationarity identity `X p q (θ ω) = X (p+1) (q+1) ω`,
iterated `m` times, gives `X p q (θ^[m] ω) = X (p+m) (q+m) ω`, so `g n (θ^[m] x) = X 0 n (θ^[m] x)
= X m (m+n) x`, and `X`'s own subadditivity (with left index `0`, middle index `m`, right index
`m + n`) gives exactly `SubadditiveAlong θ g`.  The family is already nonnegative, so the limit is
the library's lower limit `LatticeProb.gLow g`, which `LatticeProb.measurable_gLow` shows
measurable, `LatticeProb.ae_gLow_comp` shows almost everywhere `θ`-invariant, and
`LatticeProb.ae_tendsto_gLow` shows is the almost everywhere limit of `g n / n`.  No new estimates
are needed; the array's linear mean bound is not used by this route.
-/

open MeasureTheory Filter Topology

namespace Rotor.Bridge

universe u

/-- Iterating the stationarity identity `X p q (θ ω) = X (p + 1) (q + 1) ω` shifts both indices
of `X` by the number of iterations. -/
private theorem kingman_shift_iterate {Ω : Type u} (θ : Ω → Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hstat : ∀ p q ω, X p q (θ ω) = X (p + 1) (q + 1) ω) :
    ∀ (m p q : ℕ) (ω : Ω), X p q (θ^[m] ω) = X (p + m) (q + m) ω
  | 0, p, q, ω => by simp
  | (m + 1), p, q, ω => by
      have e1 : p + 1 + m = p + (m + 1) := by omega
      have e2 : q + 1 + m = q + (m + 1) := by omega
      rw [Function.iterate_succ_apply', hstat, kingman_shift_iterate θ X hstat m (p + 1) (q + 1) ω,
        e1, e2]

-- FROZEN-STATEMENT-BEGIN
/-- Kingman's subadditive ergodic theorem (Kingman 1968, Theorems 3 and 5,
`external input, Kingman 1968 Theorems 3 and 5, used in the proof of
prop:passage-limit`), proved rather than assumed. -/
theorem kingman_holds : External.Kingman
-- FROZEN-STATEMENT-END
:= by
  intro Ω _ μ hμ θ hθ X hXm hXi hXnn hXstat hXsub _hXbound
  haveI := hμ
  have hgm : ∀ n, Measurable (fun x => X 0 n x) := fun n => hXm 0 n
  have hg1 : Integrable (fun x => X 0 1 x) μ := hXi 0 1
  have hgnn : ∀ n y, 1 ≤ n → 0 ≤ (fun x => X 0 n x) y := fun n y _ => hXnn 0 n y
  have hshift : ∀ (m n : ℕ) (x : Ω), X 0 n (θ^[m] x) = X m (m + n) x := by
    intro m n x
    have h := kingman_shift_iterate θ X hXstat m 0 n x
    rw [show (0 : ℕ) + m = m from by omega, show n + m = m + n from by omega] at h
    exact h
  have hsub : LatticeProb.SubadditiveAlong θ (fun n x => X 0 n x) := by
    intro m n x
    show X 0 (m + n) x ≤ X 0 m x + X 0 n (θ^[m] x)
    rw [hshift m n x]
    exact hXsub 0 m (m + n) x (Nat.zero_le m) (Nat.le_add_right m n)
  exact ⟨LatticeProb.gLow (fun n x => X 0 n x), LatticeProb.measurable_gLow hgm,
    LatticeProb.ae_gLow_comp hθ hsub hgnn hgm hg1,
    LatticeProb.ae_tendsto_gLow hθ hsub hgnn hgm hg1⟩

end Rotor.Bridge
