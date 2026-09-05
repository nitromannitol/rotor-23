/-
Invariants of the one-particle-at-a-time state machine (`rotor.tex:742-753`),
for `lem:boundary-routing` (2) and (3) and `lem:decreasing-positions` (i).
-/
import Rotor.Support.NoRepeat

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-- The invariant of the state machine: its particle-and-rotor state is the
run of its actuation list, that list is legal, the queue is a suffix of the
order, and the particles outside `S` are exactly the queued heads and the
tracked particle. -/
structure OneInv (S : Finset V) (ρ : Config G) (es : List (V × V)) (s : OneState G) : Prop where
  run_eq : s.ξ = run π S (boundaryInit S ρ) s.acted.reverse
  legal : IsLegal π S (boundaryInit S ρ) s.acted.reverse
  queue_suffix : s.queue <:+ es
  count : ∀ x, x ∉ S →
    s.ξ.σ x = s.queue.countP (fun e => e.2 = x) + (if s.tracked = some x then 1 else 0)

open Classical in
/-- The heads of a boundary order at `x ∉ S` number the in-edges of `x` from `S`. -/
theorem countP_boundaryOrder (S : Finset V) (es : List (V × V)) (hes : IsBoundaryOrder G S es)
    (x : V) (hx : x ∉ S) :
    es.countP (fun e => e.2 = x) = (S.filter (fun s => G.Adj s x)).card := by
  rw [List.countP_eq_length_filter]
  have hnd : ((es.filter (fun e => decide (e.2 = x))).map Prod.fst).Nodup := by
    refine List.Nodup.map_on ?_ (hes.1.filter _)
    intro e₁ he₁ e₂ he₂ h
    rw [List.mem_filter, decide_eq_true_eq] at he₁ he₂
    exact Prod.ext h (he₁.2.trans he₂.2.symm)
  have hset : ((es.filter (fun e => decide (e.2 = x))).map Prod.fst).toFinset =
      S.filter (fun s => G.Adj s x) := by
    ext s
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq,
      Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨he, hex⟩, rfl⟩
      have := (hes.2 e).1 he
      exact ⟨this.1, hex ▸ this.2.2⟩
    · rintro ⟨hsS, hadj⟩
      exact ⟨(s, x), ⟨(hes.2 (s, x)).2 ⟨hsS, hx, hadj⟩, rfl⟩, rfl⟩
  rw [← hset, List.toFinset_card_of_nodup hnd, List.length_map]

/-- The invariant holds initially. -/
theorem oneInv_init (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) :
    OneInv π S ρ es { ξ := boundaryInit S ρ, queue := es, tracked := none, acted := [], route := [] } where
  run_eq := rfl
  legal := trivial
  queue_suffix := List.suffix_refl es
  count x hx := by
    classical
    simp only [boundaryInit, hx, if_false, reduceCtorEq, add_zero]
    exact (countP_boundaryOrder S es hes x hx).symm

/-- The invariant is preserved by one move. -/
theorem oneInv_step (S : Finset V) (ρ : Config G) (es : List (V × V)) (s : OneState G)
    (h : OneInv π S ρ es s) : OneInv π S ρ es (oneStep π S s) := by
  obtain ⟨hrun, hleg, hsuf, hcount⟩ := h
  cases htr : s.tracked with
  | some p =>
    by_cases hp : p ∈ S
    · -- the particle has entered `S`: it is dropped
      simp only [oneStep, htr, hp, if_true]
      refine ⟨hrun, hleg, hsuf, fun x hx => ?_⟩
      rw [hcount x hx, htr]
      have : ¬ (some p = some x) := fun h => hx (Option.some_inj.1 h ▸ hp)
      simp [this]
    · -- the particle is routed one step
      simp only [oneStep, htr, hp, if_false]
      have hσ : 0 < s.ξ.σ p := by rw [hcount p hp, htr]; simp
      refine ⟨?_, ?_, hsuf, fun x hx => ?_⟩
      · rw [List.reverse_cons, run_append, ← hrun]; rfl
      · rw [List.reverse_cons, isLegal_append]
        exact ⟨hleg, by rw [← hrun]; exact ⟨hp, hσ, trivial⟩⟩
      · rw [actuate_σ, hcount x hx, htr]
        by_cases hxp : x = p
        · subst hxp
          have hne : (π.next x (s.ξ.ρ x)).1 ≠ x := next_head_ne π s.ξ x
          have hne' : ¬ (x = (π.next x (s.ξ.ρ x)).1 ∧ (π.next x (s.ξ.ρ x)).1 ∉ S) :=
            fun h => hne h.1.symm
          simp [hne, hne']
        · have hpx : ¬ (some p = some x) := fun h => hxp (Option.some_inj.1 h).symm
          simp only [hxp, if_false, hpx, add_zero]
          by_cases hh : (π.next p (s.ξ.ρ p)).1 = x
          · simp [hh, hx]
          · have hh' : ¬ (x = (π.next p (s.ξ.ρ p)).1 ∧ (π.next p (s.ξ.ρ p)).1 ∉ S) :=
              fun h => hh h.1.symm
            simp [hh, hh']
  | none =>
    cases hq : s.queue with
    | nil =>
      simp only [oneStep, htr, hq]
      exact ⟨hrun, hleg, hq ▸ hsuf, fun x hx => by rw [hcount x hx, hq]⟩
    | cons e rest =>
      obtain ⟨t, y⟩ := e
      simp only [oneStep, htr, hq]
      refine ⟨hrun, hleg, ?_, fun x hx => ?_⟩
      · exact (List.suffix_cons (t, y) rest).trans (hq ▸ hsuf)
      · rw [hcount x hx, hq, htr]
        simp [List.countP_cons]

/-- The invariant holds at every stage. -/
theorem oneInv_all (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (n : ℕ) : OneInv π S ρ es (oneRouting π S ρ es n) := by
  induction n with
  | zero => exact oneInv_init π S ρ es hes
  | succ n ih =>
    rw [oneRouting, Function.iterate_succ', Function.comp_apply]
    exact oneInv_step π S ρ es _ ih

/-- At a finishing stage, the actuation list is a complete boundary routing. -/
theorem oneDone_complete (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (n : ℕ) (hd : OneDone π S ρ es n) :
    IsComplete π S (boundaryInit S ρ) (oneActed π S ρ es n) := by
  obtain ⟨hrun, hleg, -, hcount⟩ := oneInv_all π S ρ es hes n
  refine ⟨hleg, fun x hx => ?_⟩
  rw [oneActed, ← hrun, hcount x hx, hd.1, hd.2]
  simp

/-- A finishing stage stays finished. -/
theorem oneDone_succ (S : Finset V) (ρ : Config G) (es : List (V × V)) (n : ℕ)
    (hd : OneDone π S ρ es n) : OneDone π S ρ es (n + 1) := by
  unfold OneDone at *
  rw [oneRouting, Function.iterate_succ', Function.comp_apply, ← oneRouting]
  obtain ⟨hq, ht⟩ := hd
  simp [oneStep, ht, hq]

/-- The indicator that the tracked particle sits in `S`. -/
def trackedIn (S : Finset V) (s : OneState G) : ℤ :=
  match s.tracked with
  | some p => if p ∈ S then 1 else 0
  | none => 0

/-- The potential of a state. -/
def pot (S : Finset V) (es : List (V × V)) (s : OneState G) : ℤ :=
  2 * s.acted.length + ((es.length : ℤ) - s.queue.length) - trackedIn S s

theorem trackedIn_nonneg (S : Finset V) (s : OneState G) : 0 ≤ trackedIn S s := by
  unfold trackedIn
  split
  · split_ifs <;> simp
  · simp

theorem trackedIn_le_one (S : Finset V) (s : OneState G) : trackedIn S s ≤ 1 := by
  unfold trackedIn
  split
  · split_ifs <;> simp
  · simp

/-- Every move before finishing raises the potential by at least one. -/
theorem pot_step (S : Finset V) (ρ : Config G) (es : List (V × V)) (hes : IsBoundaryOrder G S es)
    (s : OneState G) (hinv : OneInv π S ρ es s) (hnd : ¬ (s.queue = [] ∧ s.tracked = none)) :
    pot S es s + 1 ≤ pot S es (oneStep π S s) := by
  cases htr : s.tracked with
  | some p =>
    by_cases hp : p ∈ S
    · simp [oneStep, htr, hp, pot, trackedIn]
    · simp only [oneStep, htr, hp, if_false, pot, List.length_cons, trackedIn]
      push_cast
      split_ifs <;> linarith
  | none =>
    cases hq : s.queue with
    | nil => exact absurd ⟨hq, htr⟩ hnd
    | cons e rest =>
      have he : e ∈ es := (hq ▸ hinv.queue_suffix).subset (List.mem_cons_self ..)
      have hy : e.2 ∉ S := ((hes.2 e).1 he).2.1
      obtain ⟨t, y⟩ := e
      simp only at hy
      simp [oneStep, htr, hq, pot, trackedIn, hy]
      linarith

/-- Before finishing, the potential is at least the number of moves. -/
theorem pot_ge (S : Finset V) (ρ : Config G) (es : List (V × V)) (hes : IsBoundaryOrder G S es)
    (n : ℕ) (hnd : ∀ m < n, ¬ OneDone π S ρ es m) :
    (n : ℤ) ≤ pot S es (oneRouting π S ρ es n) := by
  induction n with
  | zero => simp [oneRouting, pot, trackedIn]
  | succ n ih =>
    have h1 := pot_step π S ρ es hes _ (oneInv_all π S ρ es hes n) (hnd n (by omega))
    have h2 := ih (fun m hm => hnd m (by omega))
    rw [oneRouting, Function.iterate_succ', Function.comp_apply, ← oneRouting]
    push_cast
    linarith

theorem oneRouting_length (S : Finset V) (ρ : Config G) (es : List (V × V))
    (hes : IsBoundaryOrder G S es) (n : ℕ) (hnd : ∀ m < n, ¬ OneDone π S ρ es m) :
    n ≤ 2 * (oneRouting π S ρ es n).acted.length + es.length := by
  have h1 := pot_ge π S ρ es hes n hnd
  have h2 := trackedIn_nonneg S (oneRouting π S ρ es n)
  unfold pot at h1
  have h3 : (0 : ℤ) ≤ (oneRouting π S ρ es n).queue.length := by positivity
  omega

end Rotor
