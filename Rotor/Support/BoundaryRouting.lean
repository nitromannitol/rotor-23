/-
The second and third assertions of `lem:boundary-routing` (`rotor.tex:747-763`),
from the state-machine invariants and the abelian property:

  "Every one-particle-at-a-time boundary routing is finite if and only if the
   boundary routing of `S` terminates.  If so, each is complete and has the
   same actuation counts as every complete boundary routing."
-/
import Rotor.Support.OneParticle
import Rotor.External.Abelian

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-- A finite one-particle-at-a-time routing shows that the boundary routing
terminates. -/
theorem terminates_of_oneFinite (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (h : OneFinite π S ρ es) : Terminates π S ρ := by
  obtain ⟨n, hd⟩ := h
  exact ⟨_, oneDone_complete π S ρ es hes n hd⟩

/-- If the boundary routing terminates, every one-particle-at-a-time routing
is finite: its actuation list is a legal routing, hence no longer than a
complete one (abelian property (a)), while before finishing it grows
linearly. -/
theorem oneFinite_of_terminates (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (S : Finset V) (hS : S.Nonempty) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (hT : Terminates π S ρ) : OneFinite π S ρ es := by
  by_contra hnf
  have hnd : ∀ n, ¬ OneDone π S ρ es n := fun n hd => hnf ⟨n, hd⟩
  obtain ⟨ws, hws⟩ := hT
  set N := 2 * ws.length + es.length + 1 with hN
  have h1 := oneRouting_length π S ρ es hes N (fun m _ => hnd m)
  have hleg := (oneInv_all π S ρ es hes N).legal
  have h2 := ((hAb π inferInstance hG S hS (boundaryInit S ρ) ws
    (oneRouting π S ρ es N).acted.reverse hws.1 hleg).1 hws.2).1
  rw [List.length_reverse] at h2
  omega

/-- At a finishing stage, the actuation counts agree with those of every
complete boundary routing (abelian property (b)). -/
theorem oneActed_count_eq (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (S : Finset V) (hS : S.Nonempty) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (n : ℕ) (hd : OneDone π S ρ es n) (ws : List V)
    (hws : IsComplete π S (boundaryInit S ρ) ws) :
    ∀ v, (oneActed π S ρ es n).count v = ws.count v := by
  have hc := oneDone_complete π S ρ es hes n hd
  exact ((hAb π inferInstance hG S hS (boundaryInit S ρ) ws (oneActed π S ρ es n) hws.1 hc.1).2
    hws.2 hc.2).2.2

end Rotor
