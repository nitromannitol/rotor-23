import Rotor.Support.ExplCover
import Rotor.Support.ExplProb

/-!
Lemma 5.4 (`lem:square-exploration`, `rotor.tex:1902-1913`), assembled from
`tested_bonds_nodup` (i), `square_exploration_ii` (ii) and `testEvent_inter_open` with the
history event identity `history_event` (iii).
-/

open MeasureTheory

namespace Rotor

theorem square_exploration_proof (f d : Site) (hd : squareGraph.Adj f (f + d)) :
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
            (1 / 2) * uniformLaw clockwise {ρ | history ρ f d h.length = h})) := by
  have hdu : IsUnit d := by
    have := isUnit_of_adj hd
    rwa [add_sub_cancel_left] at this
  refine ⟨fun ρ n => tested_bonds_nodup ρ f hdu n,
    fun ρ n hterm g hg => square_exploration_ii f hdu ρ n hterm g hg, ?_⟩
  intro h e rest hact
  have hne : (replay f d h).active ≠ [] := by rw [hact]; exact List.cons_ne_nil _ _
  have hinv := explInv_replay f hdu h
  have hev : {ρ | history ρ f d h.length = h} = testEvent (replay f d h).tested :=
    history_event f d h (fun i _ => replay_active_ne_nil_of_take f d h hne i)
  have hev2 : {ρ | history ρ f d h.length = h ∧ DualOpen ρ e.1 e.2} =
      testEvent (replay f d h).tested ∩ {ρ | DualOpen ρ e.1 e.2} := by
    rw [← hev]; rfl
  have he : e ∈ (replay f d h).active := by rw [hact]; exact List.mem_cons_self
  have key := testEvent_inter_open (replay f d h).tested hinv.tested_adj e (hinv.active_adj e he)
    (fun t ht => hinv.active_tested e he t ht)
  simp only at key
  obtain ⟨c1, c2, c3⟩ := key
  rw [hev2, hev]
  exact ⟨fun hW => c1 hW, fun hW => c2 hW, fun h1 h2 => by rw [one_div]; exact c3 h1 h2⟩

end Rotor
