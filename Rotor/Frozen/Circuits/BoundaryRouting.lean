/-
Lemma 2.3 of rotor.tex, frozen.  `rotor.tex:747-752` (label `lem:boundary-routing`):

  "No legal boundary routing traverses a directed edge more than once, counting
   the initial edges from $S$.  Every one-particle-at-a-time boundary routing is
   finite if and only if the boundary routing of $S$ terminates.  If so, each is
   complete and has the same actuation counts as every complete boundary
   routing."

Three assertions, three conjuncts.  A one-particle-at-a-time routing is
determined by an ordering `es` of the boundary edges (`IsBoundaryOrder`); it
is finite when it finishes at some stage (`OneFinite`), and "each is complete"
says that its list of actuated vertices at any finishing stage is a complete
boundary routing.  The proof uses `lem:least-action`, hence `External.Abelian`.
The `External.*` hypotheses are the cited results the paper's proof uses, assumed in
phase one (ruling X-001): they are not derived here and the certificate lists them.
`[Infinite V]` and `hG` are the standing assumptions of Section 2 (`rotor.tex:678-680`:
"Throughout this section, `G` is infinite, connected, and locally finite, the rotor
mechanism and initial rotor configuration are fixed and arbitrary").
-/
import Rotor.Traversal
import Rotor.Support.NoRepeat
import Rotor.Support.BoundaryRouting
import Rotor.External.OneCircuit
import Rotor.External.Abelian
import Rotor.External.HolroydPropp

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem Rotor.Frozen.boundary_routing (hAb : External.Abelian G) (π : Mechanism G)
    [Infinite V] (hG : G.Connected) (S : Finset V) (hS : S.Nonempty) (ρ : Config G) :
    (∀ (es : List (V × V)) (vs : List V), IsBoundaryOrder G S es →
        IsLegal π S (boundaryInit S ρ) vs → (boundaryTraversed π S ρ es vs).Nodup) ∧
    (∀ es : List (V × V), IsBoundaryOrder G S es → (OneFinite π S ρ es ↔ Terminates π S ρ)) ∧
    (Terminates π S ρ → ∀ es : List (V × V), IsBoundaryOrder G S es → ∀ n, OneDone π S ρ es n →
        IsComplete π S (boundaryInit S ρ) (oneActed π S ρ es n) ∧
        ∀ ws : List V, IsComplete π S (boundaryInit S ρ) ws →
          ∀ v, (oneActed π S ρ es n).count v = ws.count v)
-- FROZEN-STATEMENT-END
:= by
  refine ⟨fun es vs hes hleg => boundaryTraversed_nodup π S ρ es vs hes hleg,
    fun es hes => ?_, fun hT es hes n hd => ?_⟩
  · exact ⟨terminates_of_oneFinite π S ρ es hes, oneFinite_of_terminates π hAb hG S hS ρ es hes⟩
  · exact ⟨oneDone_complete π S ρ es hes n hd,
      fun ws hws => oneActed_count_eq π hAb hG S hS ρ es hes n hd ws hws⟩
