import Rotor.External.HolroydPropp
import Rotor.Support.WalkBasics

/-!
# Holroyd–Propp Lemma 6: one vertex visited infinitely often visits every vertex

A rotor walk that visits one vertex infinitely often visits every vertex infinitely often.
Proved unconditionally by propagating the infinitely-many-visits property one edge at a time
along a walk between any two vertices of the graph, using the closed form for the rotor value at
a vertex visited infinitely often.
-/

namespace Rotor.Bridge

open Rotor

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- The rotor at `x` after `t` steps is obtained from the initial rotor by iterating the
mechanism's next map once for every visit to `x` before time `t`. -/
theorem rot_eq_pow_visits (π : Mechanism G) (ρ : Config G) (o x : V) (t : ℕ) :
    rot π ρ o t x =
      ((π.next x) ^ ((Finset.range t).filter (fun s => X π ρ o s = x)).card) (ρ x) := by
  induction t with
  | zero => simp [rot, walk]
  | succ t ih =>
      rw [rot_succ]
      by_cases h : X π ρ o t = x
      · subst x
        rw [Function.update_self, ih]
        simp [Finset.range_add_one, Finset.filter_insert, pow_succ']
      · simp [Function.update_of_ne (Ne.symm h), ih, Finset.range_add_one, Finset.filter_insert, h]

omit [G.LocallyFinite] in
/-- If `x` is visited infinitely often, every visit at time `t` has a next visit `u > t` with no
intervening visit to `x`. -/
theorem exists_next_visit (π : Mechanism G) (ρ : Config G) (o x : V)
    (h : Set.Infinite {s : ℕ | X π ρ o s = x}) (t : ℕ) :
    ∃ u, t < u ∧ X π ρ o u = x ∧
      ∀ s, t < s → s < u → X π ρ o s ≠ x := by
  have hex : ∃ s, t < s ∧ X π ρ o s = x := by
    obtain ⟨s, hs, hst⟩ := h.exists_gt t
    exact ⟨s, hst, hs⟩
  let u := Nat.find hex
  have hu : t < u ∧ X π ρ o u = x := Nat.find_spec hex
  refine ⟨u, hu.1, hu.2, ?_⟩
  intro s hts hsu hsx
  have hle : u ≤ s := Nat.find_min' hex ⟨hts, hsx⟩
  exact (Nat.not_lt_of_ge hle) hsu

omit [G.LocallyFinite] in
/-- Between two consecutive visits to `x`, the rotor at `x` advances by exactly one application
of the mechanism's next map. -/
theorem rot_eq_next_of_next_visit (π : Mechanism G) (ρ : Config G) (o x : V)
    {t u : ℕ} (htu : t < u) (ht : X π ρ o t = x)
    (hnext : ∀ s, t < s → s < u → X π ρ o s ≠ x) :
    rot π ρ o u x = π.next x (rot π ρ o t x) := by
  have hfilter :
      (Finset.range u).filter (fun s => X π ρ o s = x) =
        insert t ((Finset.range t).filter (fun s => X π ρ o s = x)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · intro hs
      by_cases hst : s < t
      · exact Or.inr ⟨hst, hs.2⟩
      · by_cases hts : t < s
        · exact (hnext s hts hs.1 hs.2).elim
        · left
          have : s = t := by omega
          exact this
    · intro hs
      rcases hs with rfl | hs
      · exact ⟨htu, ht⟩
      · exact ⟨Nat.lt_trans hs.1 htu, hs.2⟩
  rw [rot_eq_pow_visits, rot_eq_pow_visits, hfilter]
  simp [Finset.card_insert_of_notMem, pow_succ']

omit [G.LocallyFinite] in
/-- If `x` is visited infinitely often, then from any visit at time `t` there is, for every `n`,
a later visit at which the rotor at `x` has advanced by exactly `n` applications of the next
map. -/
theorem exists_visit_rot_eq_pow (π : Mechanism G) (ρ : Config G) (o x : V)
    (h : Set.Infinite {s : ℕ | X π ρ o s = x}) (t : ℕ) (ht : X π ρ o t = x) :
    ∀ n, ∃ u, t ≤ u ∧ X π ρ o u = x ∧
      rot π ρ o u x = ((π.next x) ^ n) (rot π ρ o t x) := by
  intro n
  induction n with
  | zero => exact ⟨t, le_rfl, ht, by simp⟩
  | succ n ih =>
      obtain ⟨u, htu, hu, hrot⟩ := ih
      obtain ⟨v, huv, hv, hnext⟩ := exists_next_visit (G := G) π ρ o x h u
      refine ⟨v, htu.trans (Nat.le_of_lt huv), hv, ?_⟩
      rw [rot_eq_next_of_next_visit (G := G) π ρ o x huv hu hnext, hrot]
      simp [pow_succ']

omit [G.LocallyFinite] in
/-- If `x` is visited infinitely often, the walk eventually departs from `x` toward any
prescribed neighbor `b` of `x`, at some visit no earlier than a given time `t`. -/
theorem exists_visit_step_eq (π : Mechanism G) (ρ : Config G) (o x : V)
    (h : Set.Infinite {s : ℕ | X π ρ o s = x}) (t : ℕ) (ht : X π ρ o t = x)
    (b : G.neighborSet x) :
    ∃ s, t ≤ s ∧ X π ρ o s = x ∧ X π ρ o (s + 1) = b.1 := by
  obtain ⟨k, hk, hpow⟩ := rank_exists π (rot π ρ o t) x b
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  obtain ⟨s, hts, hs, hrot⟩ :=
    exists_visit_rot_eq_pow (G := G) π ρ o x h t ht n
  refine ⟨s, hts, hs, ?_⟩
  rw [X_succ, hs, hrot]
  have hsel : ((π.next x) ^ (n + 1)) (rot π ρ o t x) = b := hpow
  simpa [pow_succ'] using congrArg Subtype.val hsel

omit [G.LocallyFinite] in
/-- If `x` is visited infinitely often, so is every neighbor `y` of `x`. -/
theorem infinite_visits_of_adj (π : Mechanism G) (ρ : Config G) (o x : V)
    (h : Set.Infinite {s : ℕ | X π ρ o s = x}) {y : V} (hxy : G.Adj x y) :
    Set.Infinite {s : ℕ | X π ρ o s = y} := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨t, ht, hNt⟩ := h.exists_gt N
  let b : G.neighborSet x := ⟨y, hxy⟩
  obtain ⟨s, hts, hs, hdep⟩ :=
    exists_visit_step_eq (G := G) π ρ o x h t ht b
  refine ⟨s + 1, ?_, ?_⟩
  · simpa [b] using hdep
  · omega

omit [G.LocallyFinite] in
/-- Infinitely many visits to `u` propagate along any walk from `u` to `v` in `G`, giving
infinitely many visits to `v`. -/
theorem infinite_visits_of_walk (π : Mechanism G) (ρ : Config G) (o : V)
    {u v : V} (p : G.Walk u v) :
    Set.Infinite {s : ℕ | X π ρ o s = u} → Set.Infinite {s : ℕ | X π ρ o s = v} := by
  induction p with
  | nil => intro h; exact h
  | cons huv p ih =>
      intro h
      exact ih (infinite_visits_of_adj (G := G) π ρ o _ h huv)

omit [G.LocallyFinite] in
-- FROZEN-STATEMENT-BEGIN
/-- Holroyd–Propp Lemma 6 (`external input, Holroyd-Propp Lemma 6, used in the proof of
prop:live-recurrence`), proved rather than assumed. -/
theorem visitsAllOfVisitsOne_holds : Rotor.External.VisitsAllOfVisitsOne G
-- FROZEN-STATEMENT-END
:= by
  unfold Rotor.External.VisitsAllOfVisitsOne
  intro π _ hG ρ o x hx y
  apply (hG.preconnected x y).elim
  intro p
  exact infinite_visits_of_walk (G := G) π ρ o p hx

end Rotor.Bridge
