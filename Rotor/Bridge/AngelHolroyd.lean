import Rotor.External.AngelHolroyd
import Rotor.Bridge.Abelian
import Rotor.Support.CyclicRank
import Rotor.Support.DecreasingPositionsI
import Rotor.Support.WalkBasics

/-!
# Angel–Holroyd Theorem 1: recurrence does not depend on the starting vertex

If the rotor walk from `o` is recurrent, it is recurrent from every other vertex `o'` as well.
Proved unconditionally along the route of Angel–Holroyd's own argument: recurrence at a vertex
propagates to each neighbor by tracking, for a return to the neighbor, how many particles it has
already received along each of its incoming rotor edges.
-/

namespace Rotor.Bridge

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- The cyclic order that a mechanism `π` imposes on the neighbors of `v` forces `G.neighborSet
v` to be finite, with no ambient `LocallyFinite` assumption on `G`. -/
theorem finite_neighborSet_of_mechanism (π : Mechanism G) (v : V) :
    Finite (G.neighborSet v) := by
  classical
  obtain ⟨a⟩ := π.nonempty v
  let σ : Equiv.Perm (G.neighborSet v) := π.next v
  obtain ⟨k, hk⟩ := π.cyclic v (σ a) a
  let d := k + 1
  have hd : 0 < d := by simp [d]
  have hperiod : (σ ^ d) a = a := by
    simpa [d, pow_succ, Equiv.Perm.mul_apply] using hk
  have hmul : ∀ q : ℕ, (σ ^ (d * q)) a = a := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hperiod, ih]
  have hmod : ∀ n : ℕ, (σ ^ n) a = (σ ^ (n % d)) a := by
    intro n
    conv_lhs =>
      rw [← Nat.div_add_mod n d, add_comm, pow_add, Equiv.Perm.mul_apply, hmul]
  have hsurj : Function.Surjective (fun i : Fin d => (σ ^ (i : ℕ)) a) := by
    intro b
    obtain ⟨n, hn⟩ := π.cyclic v a b
    refine ⟨⟨n % d, Nat.mod_lt _ hd⟩, ?_⟩
    simpa using (hmod n).symm.trans hn
  exact Finite.of_surjective _ hsurj

/-- A mechanism `π` on `G` makes every neighbor set finite, hence supplies a `G.LocallyFinite`
instance. -/
@[reducible] noncomputable def locallyFinite_of_mechanism (π : Mechanism G) : G.LocallyFinite := by
  intro v
  letI : Finite (G.neighborSet v) := finite_neighborSet_of_mechanism π v
  exact Fintype.ofFinite (G.neighborSet v)

/-- The number of times the walk from `o` visits `v` before time `n`. -/
def visitCount (π : Mechanism G) (ρ : Config G) (o v : V) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun s => X π ρ o s = v)).card

/-- The rotor at `v` after `n` steps of the walk is obtained from the initial rotor by iterating
the mechanism's next map once for each visit to `v` before time `n`. -/
theorem rot_eq_pow_visitCount (π : Mechanism G) (ρ : Config G) (o v : V) (n : ℕ) :
    rot π ρ o n v =
      (π.next v ^ visitCount π ρ o v n) (ρ v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rot_succ]
      by_cases h : X π ρ o n = v
      · subst v
        rw [Function.update_self, ih]
        unfold visitCount
        rw [show Finset.range (n + 1) = insert n (Finset.range n) by
          ext s; simp only [Finset.mem_insert, Finset.mem_range]; omega]
        rw [Finset.filter_insert]
        simp only [if_true]
        have hnmem : n ∉ (Finset.range n).filter
            (fun s => X π ρ o s = X π ρ o n) := by
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        rw [Finset.card_insert_of_notMem hnmem]
        rw [← Equiv.Perm.mul_apply, pow_succ']
      · rw [Function.update_of_ne (Ne.symm h), ih]
        unfold visitCount
        rw [show Finset.range (n + 1) = insert n (Finset.range n) by
          ext s; simp only [Finset.mem_insert, Finset.mem_range]; omega]
        rw [Finset.filter_insert]
        simp [h]

/-- If `v` is visited infinitely often, every visit count `n` is attained: some time `t` has `X t
= v` with exactly `n` earlier visits to `v`. -/
theorem exists_visitCount_eq_of_infinite (π : Mechanism G) (ρ : Config G) (o v : V)
    (hinf : Set.Infinite {t : ℕ | X π ρ o t = v}) :
    ∀ n : ℕ, ∃ t : ℕ, X π ρ o t = v ∧
      visitCount π ρ o v t = n := by
  classical
  obtain ⟨t₀, ht₀⟩ := hinf.nonempty
  have hex₀ : ∃ t, X π ρ o t = v := ⟨t₀, ht₀⟩
  let t₀' := Nat.find hex₀
  have ht₀mem : X π ρ o t₀' = v := Nat.find_spec hex₀
  have ht₀min : ∀ s < t₀', X π ρ o s ≠ v := by
    intro s hs hvs
    have hle := Nat.find_min' hex₀ hvs
    omega
  have hzero : visitCount π ρ o v t₀' = 0 := by
    unfold visitCount
    have hempty : (Finset.range t₀').filter (fun s => X π ρ o s = v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro s hs
      exact ht₀min s (Finset.mem_range.1 hs)
    rw [hempty]
    simp
  have hnext : ∀ t, X π ρ o t = v →
      ∃ u, t < u ∧ X π ρ o u = v ∧
        visitCount π ρ o v u =
          visitCount π ρ o v t + 1 := by
    intro t ht
    obtain ⟨u, hu, htu⟩ := hinf.exists_gt t
    have hex : ∃ u, t < u ∧ X π ρ o u = v := ⟨u, htu, hu⟩
    let u' := Nat.find hex
    have hu'mem : X π ρ o u' = v := (Nat.find_spec hex).2
    have htu' : t < u' := (Nat.find_spec hex).1
    have hmin : ∀ s, t < s → s < u' → X π ρ o s ≠ v := by
      intro s hts hsu hvs
      have hle := Nat.find_min' hex ⟨hts, hvs⟩
      omega
    have hfilter :
        (Finset.range u').filter (fun s => X π ρ o s = v) =
          insert t ((Finset.range t).filter (fun s => X π ρ o s = v)) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · intro hs
        by_cases hst : s = t
        · exact Or.inl hst
        · by_cases hst' : s < t
          · right
            exact ⟨hst', hs.2⟩
          · exact False.elim (hmin s (by omega) (by omega) hs.2)
      · intro hs
        rcases hs with rfl | hs
        · exact ⟨by omega, ht⟩
        · exact ⟨by omega, hs.2⟩
    refine ⟨u', htu', hu'mem, ?_⟩
    unfold visitCount
    rw [hfilter]
    have hnot : t ∉ (Finset.range t).filter (fun s => X π ρ o s = v) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [Finset.card_insert_of_notMem hnot]
  intro n
  induction n with
  | zero => exact ⟨t₀', ht₀mem, hzero⟩
  | succ n ih =>
      obtain ⟨t, ht, hv⟩ := ih
      obtain ⟨u, htu, hu, huv⟩ := hnext t ht
      rw [hv] at huv
      exact ⟨u, hu, huv⟩

/-- The visit count to `v` strictly increases between two visit times `a < b`. -/
theorem visitCount_lt_of_lt (π : Mechanism G) (ρ : Config G) (o v : V)
    {a b : ℕ} (hab : a < b) (ha : X π ρ o a = v) (_hb : X π ρ o b = v) :
    visitCount π ρ o v a <
      visitCount π ρ o v b := by
  classical
  let A := (Finset.range a).filter (fun s => X π ρ o s = v)
  let B := (Finset.range b).filter (fun s => X π ρ o s = v)
  have hsub : A ⊆ B := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hslt : s < a := Finset.mem_range.mp hs'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hslt.trans hab), hs'.2⟩
  have hne : A ≠ B := by
    intro heq
    have haB : a ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hab, ha⟩
    have haA : a ∈ A := heq ▸ haB
    exact (by simp [A] at haA)
  unfold visitCount
  exact Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨hsub, hne⟩)

/-- The visit count to `v` increases by one exactly when time `n` is itself a visit to `v`. -/
theorem visitCount_succ (π : Mechanism G) (ρ : Config G) (o v : V) (n : ℕ) :
    visitCount π ρ o v (n + 1) =
      visitCount π ρ o v n +
        if X π ρ o n = v then 1 else 0 := by
  unfold visitCount
  rw [show Finset.range (n + 1) = insert n (Finset.range n) by
    ext s; simp only [Finset.mem_insert, Finset.mem_range]; omega]
  rw [Finset.filter_insert]
  have hnot : n ∉ (Finset.range n).filter (fun s => X π ρ o s = v) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  by_cases h : X π ρ o n = v
  · simp [h]
  · simp [h]

/-- If the walk from `o` visits `o` infinitely often, it is recurrent: every vertex reachable
from `o` is visited infinitely often. -/
theorem recurrent_of_infinite_visits (π : Mechanism G) (_hV : Infinite V)
    (hG : G.Connected) (ρ : Config G) (o : V)
    (ha : Set.Infinite {t : ℕ | X π ρ o t = o}) :
    Recurrent π ρ o := by
  letI : G.LocallyFinite := locallyFinite_of_mechanism π
  have hstep : ∀ {u v : V}, G.Adj u v →
      Set.Infinite {t : ℕ | X π ρ o t = u} →
      Set.Infinite {t : ℕ | X π ρ o t = v} := by
    intro u v huv hu
    let p : Equiv.Perm (G.neighborSet u) := π.next u
    let d := Fintype.card (G.neighborSet u)
    have hd : 0 < d := by
      dsimp [d]
      exact Fintype.card_pos_iff.mpr (π.nonempty u)
    have hcyc : ∀ a b : G.neighborSet u, ∃ k : ℕ, (p ^ k) a = b :=
      π.cyclic u
    have hperiod : ∀ a : G.neighborSet u, (p ^ d) a = a := by
      intro a
      exact pow_card_apply p hcyc a
    obtain ⟨k, hk⟩ := π.cyclic u (p (ρ u)) ⟨v, huv⟩
    have hmul : ∀ (a : G.neighborSet u) (q : ℕ),
        (p ^ (d * q)) a = a := by
      intro a q
      induction q with
      | zero => simp
      | succ q ih =>
          rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hperiod, ih]
    have htimes : ∀ n : ℕ, ∃ t : ℕ,
        X π ρ o t = u ∧ visitCount π ρ o u t = n :=
      exists_visitCount_eq_of_infinite π ρ o u hu
    let τ : ℕ → ℕ := fun n => (htimes n).choose
    have hτ : ∀ n : ℕ, X π ρ o (τ n) = u ∧
        visitCount π ρ o u (τ n) = n := by
      intro n
      exact (htimes n).choose_spec
    have hτinj : Function.Injective τ := by
      intro a b hab
      have ha' := (hτ a).2
      have hb' := (hτ b).2
      rw [hab] at ha'
      exact by omega
    let f : ℕ → ℕ := fun q => τ (k + d * q)
    have hf : Function.Injective f := by
      intro a b hab
      have hab' := hτinj hab
      apply Nat.mul_left_cancel
      · exact hd
      · exact Nat.add_left_cancel hab'
    have hfrange : (Set.range f).Infinite := Set.infinite_range_of_injective hf
    let g : ℕ → ℕ := fun q => f q + 1
    have hg : Function.Injective g := by
      intro a b hab
      apply hf
      dsimp [g] at hab
      omega
    have hgrange : (Set.range g).Infinite := Set.infinite_range_of_injective hg
    have hsub : Set.range g ⊆ {t : ℕ | X π ρ o t = v} := by
      intro t ht
      obtain ⟨q, rfl⟩ := ht
      have hqt := hτ (k + d * q)
      have hrot := rot_eq_pow_visitCount π ρ o u (τ (k + d * q))
      have hdest :
          (p ^ (k + d * q + 1)) (ρ u) = ⟨v, huv⟩ := by
        calc
          (p ^ (k + d * q + 1)) (ρ u) =
              (p ^ (k + 1)) ((p ^ (d * q)) (ρ u)) := by
                rw [show k + d * q + 1 = (k + 1) + d * q by omega,
                  pow_add, Equiv.Perm.mul_apply]
          _ = (p ^ (k + 1)) (ρ u) := by rw [hmul]
          _ = (p ^ k) (p (ρ u)) := by
            rw [pow_succ, Equiv.Perm.mul_apply]
          _ = ⟨v, huv⟩ := hk
      have hX := X_succ π ρ o (τ (k + d * q))
      rw [hqt.1, hrot, hqt.2] at hX
      have hpow :
          p ((p ^ (k + d * q)) (ρ u)) = (p ^ (k + d * q + 1)) (ρ u) := by
        rw [← Equiv.Perm.mul_apply, pow_succ']
      change X π ρ o (f q + 1) = v
      rw [hX, hpow, hdest]
    exact hgrange.mono hsub
  have hwalk : ∀ {u v : V} (p : G.Walk u v),
      Set.Infinite {t : ℕ | X π ρ o t = u} →
      Set.Infinite {t : ℕ | X π ρ o t = v} := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
        intro hu
        exact ih (hstep huv hu)
  intro v
  exact hwalk (hG o v).some ha

/-- The walk after `t + s` steps equals the walk of `s` further steps restarted from the state
reached after `t` steps. -/
theorem walk_add_restart (π : Mechanism G) (ρ : Config G) (o : V)
    (t s : ℕ) :
    walk π ρ o (t + s) = walk π (rot π ρ o t) (X π ρ o t) s := by
  change (step π)^[t + s] ⟨o, ρ⟩ =
    (step π)^[s] ((step π)^[t] ⟨o, ρ⟩)
  rw [← Function.iterate_add_apply, Nat.add_comm]

/-- Recurrence transports along the walk: if the walk from `o` is recurrent, so is the walk
restarted at time `t` from its rotor state and current position. -/
theorem recurrent_rot_of_recurrent (π : Mechanism G) (ρ : Config G) (o : V)
    (hrec : Recurrent π ρ o) (t : ℕ) :
    Recurrent π (rot π ρ o t) (X π ρ o t) := by
  intro x
  by_contra hfinite
  have htail : Set.Finite {s : ℕ | X π (rot π ρ o t) (X π ρ o t) s = x} := by
    change ¬¬ Set.Finite {s : ℕ | X π (rot π ρ o t) (X π ρ o t) s = x} at hfinite
    exact not_not.mp hfinite
  have hsum : Set.Finite
      ((fun s : ℕ => t + s) '' {s : ℕ | X π (rot π ρ o t) (X π ρ o t) s = x}) :=
    htail.image _
  have hsmall : Set.Finite (Set.Iio t) := Set.finite_Iio t
  have hsub : {u : ℕ | X π ρ o u = x} ⊆
      Set.Iio t ∪ ((fun s : ℕ => t + s) ''
        {s : ℕ | X π (rot π ρ o t) (X π ρ o t) s = x}) := by
    intro u hu
    by_cases hut : u < t
    · exact Or.inl hut
    · right
      refine ⟨u - t, ?_, ?_⟩
      · change X π (rot π ρ o t) (X π ρ o t) (u - t) = x
        have hadd := walk_add_restart π ρ o t (u - t)
        have htu : t + (u - t) = u := Nat.add_sub_of_le (Nat.le_of_not_gt hut)
        rw [htu] at hadd
        exact hu ▸ (congrArg State.pos hadd).symm
      · exact Nat.add_sub_of_le (Nat.le_of_not_gt hut)
  exact (hrec x) ((hsmall.union hsum).subset hsub)

/-- The vertices adjacent to, but not contained in, the finite set `R`. -/
noncomputable def outerBoundary [G.LocallyFinite] (R : Finset V) : Finset V :=
  R.biUnion (fun v => (G.neighborFinset v).filter (fun w => w ∉ R))

/-- The vertices the walk moves to immediately after each visit to `x` before time `t`, in order
of occurrence. -/
def sourceList (π : Mechanism G) (ρ : Config G) (o : V) (x : V) (t : ℕ) : List V :=
  ((List.range t).filter (fun s => decide (X π ρ o s = x))).map
    (fun s => X π ρ o (s + 1))

/-- The positions of the walk before time `t`, other than `x` itself, in order of occurrence. -/
def deletedList (π : Mechanism G) (ρ : Config G) (o : V) (x : V) (t : ℕ) : List V :=
  (List.range t).map (X π ρ o) |>.filter (fun v => decide (v ≠ x))

/-- The chip configuration with `ρ` as its rotor state and, at each vertex, as many chips as
`sourceList` sends there. -/
noncomputable def particleState (π : Mechanism G) (ρ : Config G)
    (o x : V) (t : ℕ) : RState G where
  σ := fun v => (sourceList π ρ o x t).count v
  ρ := ρ

/-- `sourceList` grows only by appending as `t` increases: its value at an earlier time is a
sublist of its value at any later time. -/
theorem sourceList_sublist_of_le (π : Mechanism G) (ρ : Config G) (o x : V)
    {n t : ℕ} (hnt : n ≤ t) :
    (sourceList π ρ o x n).Sublist
      (sourceList π ρ o x t) := by
  unfold sourceList
  exact (List.Sublist.filter (fun s => decide (X π ρ o s = x))
    ((List.range_sublist).2 hnt)).map _

/-- `sourceList` at `n + 1` extends `sourceList` at `n` by the walk's position at `n + 1` exactly
when time `n` is a visit to `x`. -/
theorem sourceList_succ (π : Mechanism G) (ρ : Config G) (o x : V) (n : ℕ) :
    sourceList π ρ o x (n + 1) =
      if X π ρ o n = x then
        sourceList π ρ o x n ++ [X π ρ o (n + 1)]
      else sourceList π ρ o x n := by
  unfold sourceList
  rw [List.range_succ]
  rw [List.filter_append, List.map_append]
  by_cases h : X π ρ o n = x
  · simp [h]
  · simp [h]

/-- `deletedList` at `n + 1` extends `deletedList` at `n` by the walk's position at `n` exactly
when that position is not `x`. -/
theorem deletedList_succ (π : Mechanism G) (ρ : Config G) (o x : V) (n : ℕ) :
    deletedList π ρ o x (n + 1) =
      if X π ρ o n = x then
        deletedList π ρ o x n
      else deletedList π ρ o x n ++ [X π ρ o n] := by
  unfold deletedList
  rw [List.range_succ, List.map_append, List.filter_append]
  by_cases h : X π ρ o n = x
  · simp [h]
  · simp [h]

/-- `sourceList` is the list of the first `visitCount` iterates of the mechanism's next map at
`x`, applied to the initial rotor. -/
theorem sourceList_eq_powers (π : Mechanism G) (ρ : Config G)
    (o x : V) (n : ℕ) :
    sourceList π ρ o x n =
      ((List.range (visitCount π ρ o x n)).map
        (fun j => ((π.next x) ^ (j + 1)) (ρ x))).map Subtype.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sourceList_succ]
      by_cases h : X π ρ o n = x
      · rw [if_pos h]
        have hc := visitCount_succ π ρ o x n
        rw [if_pos h] at hc
        rw [hc]
        have hnext : X π ρ o (n + 1) =
            (((π.next x) ^
              (visitCount π ρ o x n + 1)) (ρ x)).1 := by
          rw [X_succ, rot_eq_pow_visitCount, h]
          rw [← Equiv.Perm.mul_apply, pow_succ']
        rw [ih, hnext]
        rw [show visitCount π ρ o x n + 1 =
            (visitCount π ρ o x n).succ by omega]
        rw [List.range_succ, List.map_append]
        simp
      · rw [if_neg h, visitCount_succ, if_neg h, ih]
        simp

/-- Every time before `n` is recorded by exactly one of `deletedList` or `visitCount`, so their
sizes add to `n`. -/
theorem deletedList_length_add_visitCount (π : Mechanism G) (ρ : Config G)
    (o x : V) (n : ℕ) :
    (deletedList π ρ o x n).length +
        visitCount π ρ o x n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [deletedList_succ,
        visitCount_succ]
      by_cases h : X π ρ o n = x
      · rw [if_pos h, if_pos h]
        omega
      · rw [if_neg h, if_neg h]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega

/-- If the walk from `x` returns to `x` at time `t`, the routing `deletedList` run from
`particleState` completely stabilizes `{x}` together with its outer boundary. -/
theorem isComplete_of_return (π : Mechanism G) [G.LocallyFinite]
    (ρ : Config G) (x : V) (t : ℕ) (ht : X π ρ x t = x) :
    IsComplete π ({x} ∪ outerBoundary (G := G) (R π ρ x t))
      (particleState π ρ x x t)
      (deletedList π ρ x x t) := by
  classical
  let R₀ := R π ρ x t
  let B := outerBoundary (G := G) R₀
  let K : Finset V := {x} ∪ B
  let ξ := particleState π ρ x x t
  let H := sourceList π ρ x x t
  let D : ℕ → List V := fun n => deletedList π ρ x x n
  have hB : ∀ {v : V}, v ∈ R₀ → v ∉ B := by
    intro v hv hvm
    obtain ⟨u, hu, hvm⟩ := Finset.mem_biUnion.mp hvm
    have hvm' := (Finset.mem_filter.mp hvm).2
    exact hvm' hv
  have hR : ∀ {n : ℕ}, n ≤ t → X π ρ x n ∈ R₀ := by
    intro n hn
    exact X_mem_R π ρ x n t hn
  have hmain : ∀ n : ℕ, n ≤ t →
      IsLegal π K ξ (D n) ∧
      (∀ v, v ≠ x → (run π K ξ (D n)).ρ v = rot π ρ x n v) ∧
      (∀ v, (run π K ξ (D n)).σ v +
          (sourceList π ρ x x n).count v =
        H.count v + if X π ρ x n = v ∧ v ≠ x then 1 else 0) := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hD : D 0 = [] := by rfl
        have hsource : sourceList π ρ x x 0 = [] := by rfl
        refine ⟨by simp [hD], ?_, ?_⟩
        · intro v hv
          change ρ v = ρ v
          rfl
        · intro v
          change H.count v + 0 = H.count v +
            if x = v ∧ v ≠ x then 1 else 0
          by_cases hvx : x = v
          · subst v
            simp
          · simp [hvx]
    | succ n ih =>
        intro hn
        have hnle : n ≤ t := Nat.le_of_succ_le hn
        obtain ⟨hleg, hrot, hsigma⟩ := ih hnle
        by_cases hnx : X π ρ x n = x
        · have hD' : D (n + 1) = D n := by
            simpa [D, hnx] using deletedList_succ π ρ x x n
          have hS' := sourceList_succ π ρ x x n
          rw [if_pos hnx] at hS'
          have hnextx : X π ρ x (n + 1) ≠ x := by
            intro heq
            have hadj := adj_X_succ π ρ x n
            rw [hnx, heq] at hadj
            exact G.irrefl hadj
          refine ⟨hD' ▸ hleg, ?_, ?_⟩
          · intro v hv
            rw [hD']
            rw [rot_succ]
            rw [Function.update_of_ne (fun h => hv (h.trans hnx))]
            exact hrot v hv
          · intro v
            rw [hD', hS']
            have hs := hsigma v
            have hfalse : ¬(X π ρ x n = v ∧ v ≠ x) := by
              intro h
              exact h.2 (h.1.symm.trans hnx)
            rw [if_neg hfalse] at hs
            by_cases hnv : X π ρ x (n + 1) = v
            · have hcond : X π ρ x (n + 1) = v ∧ v ≠ x := by
                exact ⟨hnv, by intro hvx; exact hnextx (hvx ▸ hnv)⟩
              rw [if_pos hcond]
              have hsplus := congrArg (fun q => q + 1) hs
              simp [List.count_append, hnv] at hsplus ⊢
              omega
            · have hcond : ¬(X π ρ x (n + 1) = v ∧ v ≠ x) := by
                intro h
                exact hnv h.1
              rw [if_neg hcond]
              simpa [List.count_append, List.count_singleton, hcond, hnv] using hs
        · have hD' : D (n + 1) = D n ++ [X π ρ x n] := by
            simpa [D, hnx] using deletedList_succ π ρ x x n
          have hS' : sourceList π ρ x x (n + 1) =
              sourceList π ρ x x n := by
            rw [sourceList_succ, if_neg hnx]
          have huR : X π ρ x n ∈ R₀ := hR hnle
          have huK : X π ρ x n ∉ K := by
            intro hmem
            simp only [K, Finset.mem_union, Finset.mem_singleton] at hmem
            rcases hmem with hmem | hmem
            · exact hnx hmem
            · exact hB huR hmem
          have huσ : 0 < (run π K ξ (D n)).σ (X π ρ x n) := by
            have hs := hsigma (X π ρ x n)
            have hc := (sourceList_sublist_of_le π ρ x x hnle).count_le
              (X π ρ x n)
            have hs' : (run π K ξ (D n)).σ (X π ρ x n) +
                (sourceList π ρ x x n).count (X π ρ x n) =
                (sourceList π ρ x x t).count (X π ρ x n) + 1 := by
              simpa [H, hnx] using hs
            omega
          have hleg' : IsLegal π K ξ (D n ++ [X π ρ x n]) := by
            rw [isLegal_append]
            refine ⟨hleg, ?_⟩
            rw [isLegal_cons]
            exact ⟨huK, huσ, by simp⟩
          refine ⟨hD' ▸ hleg', ?_, ?_⟩
          · intro v hv
            rw [hD', run_append]
            change (actuate π K (run π K ξ (D n)) (X π ρ x n)).ρ v =
              rot π ρ x (n + 1) v
            by_cases huv : v = X π ρ x n
            · subst v
              rw [actuate_ρ_self]
              rw [hrot (X π ρ x n) hnx, rot_succ, Function.update_self]
            · rw [actuate_ρ_of_ne π K (run π K ξ (D n)) _ _ huv]
              rw [hrot v hv, rot_succ, Function.update_of_ne]
              exact huv
          · intro v
            rw [hD', run_append, hS']
            change (actuate π K (run π K ξ (D n)) (X π ρ x n)).σ v +
                (sourceList π ρ x x n).count v =
              H.count v + if X π ρ x (n + 1) = v ∧ v ≠ x then 1 else 0
            rw [actuate_σ]
            have hs := hsigma v
            have hc := (sourceList_sublist_of_le π ρ x x hnle).count_le v
            have hnext : X π ρ x (n + 1) ∈ R₀ := hR hn
            have hhead' :
                (π.next (X π ρ x n)
                  ((run π K ξ (D n)).ρ (X π ρ x n))).1 =
                  X π ρ x (n + 1) := by
              rw [hrot (X π ρ x n) hnx]
              exact (X_succ π ρ x n).symm
            rw [hhead']
            have hnoarr : ¬(X π ρ x n = X π ρ x (n + 1) ∧
                X π ρ x (n + 1) ∉ K) := by
              intro h
              have hadj := adj_X_succ π ρ x n
              rw [h.1] at hadj
              exact G.irrefl hadj
            have hnextK : X π ρ x (n + 1) ∉ B := hB hnext
            by_cases huv : X π ρ x n = v
            · subst v
              have hs' : (run π K ξ (D n)).σ (X π ρ x n) +
                  (sourceList π ρ x x n).count (X π ρ x n) =
                  H.count (X π ρ x n) + 1 := by
                simpa [H, hnx] using hs
              have hne : X π ρ x (n + 1) ≠ X π ρ x n := by
                exact (G.ne_of_adj (adj_X_succ π ρ x n)).symm
              have hnoarrx : ¬(x = X π ρ x (n + 1) ∧
                  X π ρ x (n + 1) ∉ K) := by
                intro h
                have hxK : x ∈ K := by simp [K]
                have hnextK' : X π ρ x (n + 1) ∈ K := by
                  simpa [h.1.symm] using hxK
                exact h.2 hnextK'
              have hright : ¬(X π ρ x (n + 1) = X π ρ x n ∧
                  X π ρ x n ≠ x) := by
                intro h
                exact hne h.1
              rw [if_pos (rfl : X π ρ x n = X π ρ x n),
                if_neg hnoarr, if_neg hright]
              omega
            · have hs' : (run π K ξ (D n)).σ v +
                  (sourceList π ρ x x n).count v =
                  H.count v := by
                simpa [H, huv] using hs
              by_cases hvx : v = x
              · have hfirst : v ≠ X π ρ x n := by
                  intro h
                  exact (Ne.symm hnx) (hvx ▸ h)
                have hnoarrv : ¬(v = X π ρ x (n + 1) ∧
                    X π ρ x (n + 1) ∉ K) := by
                  intro h
                  have hxK : x ∈ K := by simp [K]
                  have hnextK' : X π ρ x (n + 1) ∈ K := by
                    simpa [h.1.symm.trans hvx] using hxK
                  exact h.2 hnextK'
                have hrightv : ¬(X π ρ x (n + 1) = v ∧ v ≠ x) := by
                  intro h
                  exact h.2 hvx
                rw [if_neg hfirst, if_neg hnoarrv, if_neg hrightv]
                exact hs'
              · by_cases hvnext : X π ρ x (n + 1) = v
                · have hnotK : v ∉ K := by
                    intro hvm
                    have hmem' : v = x ∨ v ∈ B := by simpa [K] using hvm
                    rcases hmem' with hmem | hmem
                    · exact hvx hmem
                    · rw [← hvnext] at hmem
                      exact hnextK hmem
                  simp [hvnext, hvx, Ne.symm huv, hnotK]
                  omega
                · simp [hvnext, Ne.symm hvnext, hvx, Ne.symm huv]
                  exact hs'
  have hstate := hmain t le_rfl
  refine ⟨hstate.1, ?_⟩
  intro v hv
  have hvx : v ≠ x := by
    intro hvx
    exact hv (by simp [hvx])
  have hs := hstate.2.2 v
  change (run π K ξ (D t)).σ v + H.count v =
    H.count v + if X π ρ x t = v ∧ v ≠ x then 1 else 0 at hs
  have hcur : ¬(X π ρ x t = v ∧ v ≠ x) := by
    intro h
    apply hvx
    calc
      v = X π ρ x t := h.1.symm
      _ = x := ht
  simp only [hcur, if_false] at hs
  change (run π K ξ (D t)).σ v = 0
  omega

/-- If the walk started at a recurrent vertex `x` is recurrent, so is the walk started at any
neighbor `y` of `x`, by transporting recurrence across the edge through a chip-routing
argument. -/
theorem recurrent_of_adjacent (π : Mechanism G) (hV : Infinite V) (hG : G.Connected)
    (ρ : Config G) (x y : V) (hxy : G.Adj x y) (hx : Recurrent π ρ x) :
    Recurrent π ρ y := by
  classical
  letI : G.LocallyFinite := locallyFinite_of_mechanism π
  let p : Equiv.Perm (G.neighborSet x) := π.next x
  let d := Fintype.card (G.neighborSet x)
  have hd : 0 < d := by
    dsimp [d]
    exact Fintype.card_pos_iff.mpr (π.nonempty x)
  have hperiod : ∀ a : G.neighborSet x, (p ^ d) a = a := by
    intro a
    exact pow_card_apply p (π.cyclic x) a
  have hmul : ∀ (a : G.neighborSet x) (q : ℕ),
      (p ^ (d * q)) a = a := by
    intro a q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hperiod, ih]
  have hmod : ∀ (n : ℕ) (a : G.neighborSet x),
      (p ^ n) a = (p ^ (n % d)) a := by
    intro n a
    conv_lhs =>
      rw [← Nat.div_add_mod n d, add_comm, pow_add, Equiv.Perm.mul_apply, hmul]
  have htimes : ∀ n : ℕ, ∃ t : ℕ,
      X π ρ x t = x ∧ visitCount π ρ x x t = n :=
    exists_visitCount_eq_of_infinite π ρ x x (hx x)
  have hreturn : ∀ m : ℕ, ∃ t : ℕ, X π ρ x t = x ∧
      d + m = visitCount π ρ x x t := by
    intro m
    obtain ⟨t, ht, htc⟩ := htimes (d + m)
    exact ⟨t, ht, htc.symm⟩
  have hySource : ∀ m : ℕ, ∃ t : ℕ, X π ρ x t = x ∧
      d + m = visitCount π ρ x x t ∧
      y ∈ sourceList π ρ x x t := by
    intro m
    obtain ⟨t, ht, htc⟩ := hreturn m
    obtain ⟨k, hk⟩ := π.cyclic x (p (ρ x)) ⟨y, hxy⟩
    let r := k % d
    have hr : r < d := Nat.mod_lt _ hd
    have htarget :
        (((p ^ (r + 1)) (ρ x))).1 = y := by
      calc
        (((p ^ (r + 1)) (ρ x))).1 = (p ^ r) (p (ρ x)) := by
          rw [pow_succ, Equiv.Perm.mul_apply]
        _ = (p ^ k) (p (ρ x)) := by rw [hmod k]
        _ = y := congrArg Subtype.val hk
    obtain ⟨s, hs, hsc⟩ := htimes r
    have hst : s < t := by
      by_contra hnot
      have hle : t ≤ s := Nat.le_of_not_gt hnot
      by_cases hEq : s = t
      · subst s
        omega
      · have hts : t < s := lt_of_le_of_ne hle (Ne.symm hEq)
        have hstrict := visitCount_lt_of_lt π ρ x x hts ht hs
        omega
    have hsmem : s ∈ (List.range t).filter
        (fun q => decide (X π ρ x q = x)) := by
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hst, hs⟩
    refine ⟨t, ht, htc, ?_⟩
    apply List.mem_map.mpr
    refine ⟨s, hsmem, ?_⟩
    have hnext := X_succ π ρ x s
    rw [hnext, rot_eq_pow_visitCount, hs, hsc]
    change (p ((p ^ r) (ρ x))).1 = y
    rw [← Equiv.Perm.mul_apply, ← pow_succ']
    exact htarget
  let L : ℕ → List V := fun n =>
    (List.range n).map (fun j => ((p ^ (j + 1)) (ρ x)).1)
  have hshift : ∀ j : ℕ,
      ((p ^ ((d + j) + 1)) (ρ x)).1 = ((p ^ (j + 1)) (ρ x)).1 := by
    intro j
    rw [show (d + j) + 1 = (j + 1) + d by omega, pow_add,
      Equiv.Perm.mul_apply, hperiod]
  have hL : ∀ k : ℕ, L (d + k) = L d ++ L k := by
    intro k
    dsimp [L]
    rw [List.range_add, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    exact hshift j
  have hsource_mem_R : ∀ (t : ℕ) {v : V},
      v ∈ sourceList π ρ x x t → v ∈ R π ρ x t := by
    intro t v hv
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
    have hs' := List.mem_filter.mp hs
    have hslt : s < t := Finset.mem_range.mp hs'.1
    exact X_mem_R π ρ x (s + 1) t (by omega)
  have hdom : ∀ (m n : ℕ),
      visitCount π ρ y x n ≤ m →
      ∀ v, (y :: sourceList π ρ y x n).count v ≤
        (L (d + m)).count v := by
    intro m n hn v
    have hsrc := sourceList_eq_powers π ρ y x n
    rw [List.map_map] at hsrc
    have hsrc' : sourceList π ρ y x n = L
        (visitCount π ρ y x n) := by
      change sourceList π ρ y x n =
        (List.range (visitCount π ρ y x n)).map
          (fun j => (((p ^ (j + 1)) (ρ x))).1) at hsrc
      simpa [L] using hsrc
    have hsub : List.Sublist (L (visitCount π ρ y x n)) (L m) := by
      dsimp [L]
      exact ((List.range_sublist).2 hn).map _
    have hcount := hsub.count_le v
    have hP : L (d + m) = L d ++ L m := hL m
    have hyL : 1 ≤ (L d).count y := by
      exact (List.count_pos_iff.mpr (by
        obtain ⟨k, hk⟩ := π.cyclic x (p (ρ x)) ⟨y, hxy⟩
        let r := k % d
        refine List.mem_map.mpr ⟨r, List.mem_range.mpr (Nat.mod_lt _ hd), ?_⟩
        have hh : (((p ^ (r + 1)) (ρ x))).1 = y := by
          calc
            (((p ^ (r + 1)) (ρ x))).1 = (p ^ r) (p (ρ x)) := by
              rw [pow_succ, Equiv.Perm.mul_apply]
            _ = (p ^ k) (p (ρ x)) := by rw [hmod k]
            _ = y := congrArg Subtype.val hk
        exact hh))
    rw [hP, List.count_append, List.count_cons]
    have hcount' : (sourceList π ρ y x n).count v ≤
        (L m).count v := by simpa [hsrc'] using hcount
    by_cases hv : v = y
    · subst v
      simp only [beq_self_eq_true, if_true]
      omega
    · simp [Ne.symm hv]
      exact hcount'.trans (Nat.le_add_left _ _)
  have hvisit : ∀ m : ℕ, ∃ n : ℕ,
      m ≤ visitCount π ρ y x n := by
    intro m
    obtain ⟨t, ht, htc, hy⟩ := hySource m
    let R₀ := R π ρ x t
    let B := outerBoundary (G := G) R₀
    let K : Finset V := {x} ∪ B
    let ξ := particleState π ρ x x t
    let P := sourceList π ρ x x t
    let U : ℕ → List V := fun n => y :: sourceList π ρ y x n
    let E : ℕ → List V := fun n => deletedList π ρ y x n
    have hP : P = L (d + m) := by
      have hs := sourceList_eq_powers π ρ x x t
      rw [List.map_map] at hs
      change P = (List.range (visitCount π ρ x x t)).map
        (fun j => (((p ^ (j + 1)) (ρ x))).1) at hs
      rw [← htc] at hs
      simpa [P, L] using hs
    have hdomP : ∀ n, visitCount π ρ y x n ≤ m →
        ∀ v, (U n).count v ≤ P.count v := by
      intro n hn v
      rw [hP]
      exact hdom m n hn v
    have hyx : y ≠ x := (G.ne_of_adj hxy).symm
    have hB : ∀ {v : V}, v ∈ R₀ → v ∉ B := by
      intro v hv hvm
      obtain ⟨u, hu, hvm⟩ := Finset.mem_biUnion.mp hvm
      exact (Finset.mem_filter.mp hvm).2 hv
    have hR : ∀ {n : ℕ}, n ≤ t → X π ρ x n ∈ R₀ := by
      intro n hn
      exact X_mem_R π ρ x n t hn
    have hroute : ∀ n : ℕ,
        visitCount π ρ y x n ≤ m →
        (∀ s ≤ n, X π ρ y s ≠ x →
          X π ρ y s ∉ K) →
        IsLegal π K ξ (E n) ∧
        (∀ v, v ≠ x → (run π K ξ (E n)).ρ v = rot π ρ y n v) ∧
        (∀ v, (run π K ξ (E n)).σ v + (U n).count v =
          P.count v + if X π ρ y n = v ∧ v ≠ x then 1 else 0) := by
      intro n
      induction n with
      | zero =>
          intro hn ha
          refine ⟨by change IsLegal π K ξ []; simp, ?_, ?_⟩
          · intro v hv
            change ρ v = ρ v
            rfl
          · intro v
            have hv0 : X π ρ y 0 = y := rfl
            change P.count v + (y :: []).count v =
              P.count v + if y = v ∧ v ≠ x then 1 else 0
            by_cases hv : v = y
            · subst v
              simp [hyx]
            · simp [Ne.symm hv]
      | succ n ih =>
          intro hn ha
          have hn' : visitCount π ρ y x n ≤ m := by
            have hc := visitCount_succ π ρ y x n
            rw [hc] at hn
            omega
          obtain ⟨hleg, hrot, hsigma⟩ := ih hn'
            (fun s hs hnx => ha s (hs.trans (Nat.le_succ n)) hnx)
          by_cases hnx : X π ρ y n = x
          · have hE' : E (n + 1) = E n := by
              simpa [E, hnx] using deletedList_succ π ρ y x n
            have hU' : U (n + 1) = U n ++ [X π ρ y (n + 1)] := by
              simp [U, sourceList_succ, hnx]
            have hnextx : X π ρ y (n + 1) ≠ x := by
              intro heq
              have hadj := adj_X_succ π ρ y n
              rw [hnx, heq] at hadj
              exact G.irrefl hadj
            refine ⟨hE' ▸ hleg, ?_, ?_⟩
            · intro v hv
              rw [hE', rot_succ,
                Function.update_of_ne (fun h => hv (h.trans hnx))]
              exact hrot v hv
            · intro v
              rw [hE', hU']
              have hs := hsigma v
              have hfalse : ¬(X π ρ y n = v ∧ v ≠ x) := by
                intro h
                exact h.2 (h.1.symm.trans hnx)
              rw [if_neg hfalse] at hs
              by_cases hnv : X π ρ y (n + 1) = v
              · have hcond : X π ρ y (n + 1) = v ∧ v ≠ x :=
                  ⟨hnv, by intro hvx; exact hnextx (hvx ▸ hnv)⟩
                rw [if_pos hcond]
                have hsplus := congrArg (fun q => q + 1) hs
                simp [List.count_append, hnv] at hsplus ⊢
                omega
              · have hcond : ¬(X π ρ y (n + 1) = v ∧ v ≠ x) := by
                  intro h
                  exact hnv h.1
                rw [if_neg hcond]
                simpa [List.count_append, hnv] using hs
          · have hE' : E (n + 1) = E n ++ [X π ρ y n] := by
              simpa [E, hnx] using deletedList_succ π ρ y x n
            have hU' : U (n + 1) = U n := by
              simp [U, sourceList_succ, hnx]
            have huK : X π ρ y n ∉ K := by
              exact ha n (Nat.le_succ n) hnx
            have huσ : 0 < (run π K ξ (E n)).σ (X π ρ y n) := by
              have hs := hsigma (X π ρ y n)
              have hc := hdomP n hn' (X π ρ y n)
              simp [hnx] at hs
              omega
            have hleg' : IsLegal π K ξ (E n ++ [X π ρ y n]) := by
              rw [isLegal_append]
              refine ⟨hleg, ?_⟩
              rw [isLegal_cons]
              exact ⟨huK, huσ, by simp⟩
            refine ⟨hE' ▸ hleg', ?_, ?_⟩
            · intro v hv
              rw [hE', run_append]
              change (actuate π K (run π K ξ (E n)) (X π ρ y n)).ρ v =
                rot π ρ y (n + 1) v
              by_cases huv : v = X π ρ y n
              · subst v
                rw [actuate_ρ_self, hrot (X π ρ y n) hnx, rot_succ,
                  Function.update_self]
              · rw [actuate_ρ_of_ne π K (run π K ξ (E n)) _ _ huv,
                  hrot v hv, rot_succ, Function.update_of_ne]
                exact huv
            · intro v
              rw [hE', run_append, hU']
              change (actuate π K (run π K ξ (E n)) (X π ρ y n)).σ v +
                  (U n).count v =
                P.count v + if X π ρ y (n + 1) = v ∧ v ≠ x then 1 else 0
              rw [actuate_σ]
              have hs := hsigma v
              have hhead :
                  (π.next (X π ρ y n)
                    ((run π K ξ (E n)).ρ (X π ρ y n))).1 =
                    X π ρ y (n + 1) := by
                rw [hrot (X π ρ y n) hnx]
                exact (X_succ π ρ y n).symm
              rw [hhead]
              by_cases huv : X π ρ y n = v
              · subst v
                have hne : X π ρ y n ≠ X π ρ y (n + 1) :=
                  G.ne_of_adj (adj_X_succ π ρ y n)
                have hright : ¬(X π ρ y (n + 1) = X π ρ y n ∧
                    X π ρ y n ≠ x) := fun h => hne h.1.symm
                have hnoarr : ¬(X π ρ y n = X π ρ y (n + 1) ∧
                    X π ρ y (n + 1) ∉ K) := by
                  intro h
                  exact hne h.1
                rw [if_pos (rfl : X π ρ y n = X π ρ y n),
                  if_neg hnoarr, if_neg hright]
                have hs' : (run π K ξ (E n)).σ (X π ρ y n) +
                    (U n).count (X π ρ y n) = P.count (X π ρ y n) + 1 := by
                  simpa [hnx] using hs
                omega
              · by_cases hvx : v = x
                · have hfirst : v ≠ X π ρ y n := by
                    intro h
                    exact (Ne.symm hnx) (hvx ▸ h)
                  have hnoarr : ¬(v = X π ρ y (n + 1) ∧
                      X π ρ y (n + 1) ∉ K) := by
                    intro h
                    exact h.2 (by
                      have hu : x ∈ K := by simp [K]
                      have hu' : X π ρ y (n + 1) ∈ K := by
                        simpa [h.1.symm.trans hvx] using hu
                      exact hu')
                  have hright : ¬(X π ρ y (n + 1) = v ∧ v ≠ x) :=
                    fun h => h.2 hvx
                  rw [if_neg hfirst, if_neg hnoarr, if_neg hright]
                  simpa [hvx] using hs
                · by_cases hvnext : X π ρ y (n + 1) = v
                  · have hvK : v ∉ K := by
                      intro hvm
                      have hmem : v = x ∨ v ∈ B := by simpa [K] using hvm
                      rcases hmem with hmem | hmem
                      · exact hvx hmem
                      · exact (ha (n + 1) le_rfl (by
                          intro heq
                          exact hvx (hvnext.symm.trans heq))) (by
                            simpa [hvnext] using hvm)
                    have hnextNotK : X π ρ y (n + 1) ∉ K := by
                      exact ha (n + 1) le_rfl (by
                        intro heq
                        exact hvx (hvnext.symm.trans heq))
                    have hs' := hs
                    simp [huv] at hs'
                    simp [hvnext, hvx, Ne.symm huv, hvK]
                    omega
                  · simp [hvnext, Ne.symm hvnext, hvx, Ne.symm huv]
                    have hs' := hs
                    simp [huv] at hs'
                    omega
    let D₀ : ℕ → List V := fun n => deletedList π ρ x x n
    have hgoodInv : ∀ n : ℕ, n ≤ t →
        (∀ v, v ≠ x → (run π K ξ (D₀ n)).ρ v = rot π ρ x n v) ∧
        (∀ e, e ∈ traversed π K ξ (D₀ n) → e.2 ∈ R₀) := by
      intro n
      induction n with
      | zero =>
          intro hn
          constructor
          · intro v hv
            rfl
          · intro e he
            simp [D₀, deletedList] at he
      | succ n ih =>
          intro hn
          have hnle : n ≤ t := Nat.le_of_succ_le hn
          obtain ⟨hrot, hedge⟩ := ih hnle
          by_cases hnx : X π ρ x n = x
          · have hD' : D₀ (n + 1) = D₀ n := by
              simpa [D₀, hnx] using deletedList_succ π ρ x x n
            constructor
            · intro v hv
              rw [hD', rot_succ,
                Function.update_of_ne (fun h => hv (h.trans hnx))]
              exact hrot v hv
            · intro e he
              apply hedge e
              simpa [hD'] using he
          · have hD' : D₀ (n + 1) = D₀ n ++ [X π ρ x n] := by
              simpa [D₀, hnx] using deletedList_succ π ρ x x n
            constructor
            · intro v hv
              rw [hD', run_append]
              change (actuate π K (run π K ξ (D₀ n)) (X π ρ x n)).ρ v =
                rot π ρ x (n + 1) v
              by_cases huv : v = X π ρ x n
              · subst v
                rw [actuate_ρ_self, hrot (X π ρ x n) hnx,
                  rot_succ, Function.update_self]
              · rw [actuate_ρ_of_ne π K (run π K ξ (D₀ n)) _ _ huv,
                  hrot v hv, rot_succ, Function.update_of_ne]
                exact huv
            · intro e he
              have he' : e ∈ traversed π K ξ (D₀ n) ∨
                  e ∈ traversed π K (run π K ξ (D₀ n)) [X π ρ x n] := by
                simpa [hD', traversed_append] using he
              rcases he' with he | he
              · exact hedge e he
              · have he' : e =
                    (X π ρ x n,
                      (π.next (X π ρ x n)
                        ((run π K ξ (D₀ n)).ρ (X π ρ x n))).1) := by
                    simpa [traversed_cons] using he
                subst e
                have hhead :
                    (π.next (X π ρ x n)
                      ((run π K ξ (D₀ n)).ρ (X π ρ x n))).1 =
                      X π ρ x (n + 1) := by
                  rw [hrot (X π ρ x n) hnx]
                  exact (X_succ π ρ x n).symm
                rw [hhead]
                exact X_mem_R π ρ x (n + 1) t hn
    have hgoodEdge := (hgoodInv t le_rfl).2
    have hhead_of_count : ∀ (l : List V) (ξ₁ : RState G) (u : V) (q : ℕ),
        (∀ e, e ∈ traversed π K ξ₁ l → e.2 ∈ R₀) →
        q < l.count u →
        (((π.next u) ^ (q + 1)) (ξ₁.ρ u)).1 ∈ R₀ := by
      intro l
      induction l with
      | nil =>
          intro ξ₁ u q he hq
          simp at hq
      | cons v l ih =>
          intro ξ₁ u q he hq
          by_cases hvu : v = u
          · subst v
            by_cases hq0 : q = 0
            · subst q
              have he0 :
                  (u, (π.next u (ξ₁.ρ u)).1) ∈ traversed π K ξ₁ (u :: l) := by
                simp
              exact he _ he0
            · have hq' : q - 1 < l.count u := by
                simp only [List.count_cons_self] at hq
                omega
              have hetail : ∀ e,
                  e ∈ traversed π K (actuate π K ξ₁ u) l → e.2 ∈ R₀ := by
                intro e he'
                apply he e
                simp only [traversed_cons, List.mem_cons]
                exact Or.inr he'
              have hh := ih (actuate π K ξ₁ u) u (q - 1) hetail hq'
              rw [actuate_ρ_self] at hh
              simpa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hq0),
                pow_succ, Equiv.Perm.mul_apply] using hh
          · have hq' : q < l.count u := by
              simpa [List.count_cons_of_ne hvu] using hq
            have hetail : ∀ e,
                e ∈ traversed π K (actuate π K ξ₁ v) l → e.2 ∈ R₀ := by
              intro e he'
              apply he e
              simp only [traversed_cons, List.mem_cons]
              exact Or.inr he'
            have hh := ih (actuate π K ξ₁ v) u q hetail hq'
            simpa [actuate_ρ_of_ne π K ξ₁ v u (Ne.symm hvu)] using hh
    have hgood : IsComplete π K ξ (D₀ t) := by
      simpa [K, B, R₀, ξ, D₀] using
        (isComplete_of_return π ρ x t ht)
    have hleast : ∀ (l : List V), IsLegal π K ξ l →
        l.length ≤ (D₀ t).length ∧
          ∀ v, l.count v ≤ (D₀ t).count v := by
      intro l hl
      exact ((abelian_holds G) π hV hG K (by simp [K]) ξ (D₀ t) l
        hgood.1 hl).1 hgood.2
    have hextend : ∀ (l : List V), IsLegal π K ξ l →
        ∃ r : List V, IsComplete π K ξ (l ++ r) := by
      have H : ∀ q : ℕ, ∀ l : List V,
          (D₀ t).length - l.length = q → IsLegal π K ξ l →
          ∃ r : List V, IsComplete π K ξ (l ++ r) := by
        intro q
        induction q using Nat.strong_induction_on with
        | h q ih =>
            intro l hq hl
            by_cases hs : Stable K (run π K ξ l)
            · exact ⟨[], by simpa, by simpa using hs⟩
            · unfold Stable at hs
              push Not at hs
              obtain ⟨v, hvK, hv⟩ := hs
              have hvpos : 0 < (run π K ξ l).σ v := Nat.pos_of_ne_zero hv
              have hl' : IsLegal π K ξ (l ++ [v]) := by
                rw [isLegal_append]
                refine ⟨hl, ?_⟩
                rw [isLegal_cons]
                exact ⟨hvK, hvpos, by simp⟩
              have hleast' := hleast (l ++ [v]) hl'
              have hq' : (D₀ t).length - (l ++ [v]).length < q := by
                simp only [List.length_append, List.length_singleton] at hleast' hq ⊢
                omega
              obtain ⟨r, hrleg, hrstable⟩ := ih _ hq' (l ++ [v]) rfl hl'
              refine ⟨v :: r, ?_, ?_⟩
              · simpa [List.append_assoc] using hrleg
              · simpa [List.append_assoc] using hrstable
      intro l hl
      exact H _ l rfl hl
    by_contra hnot
    push Not at hnot
    let N := (D₀ t).length + m
    have hnoAvoid : ¬ (∀ s ≤ N, X π ρ y s ≠ x → X π ρ y s ∉ K) := by
      intro havoid
      have hN := hroute N (Nat.le_of_lt (hnot N)) havoid
      have hNc : visitCount π ρ y x N < m :=
        hnot N
      have hElen : (E N).length +
          visitCount π ρ y x N = N := by
        simpa [E] using deletedList_length_add_visitCount π ρ y x N
      have hleastN := hleast (E N) hN.1
      have hlenN := hleastN.1
      dsimp [N] at hNc hlenN
      dsimp [N] at hElen
      omega
    have hBhit : ∃ s : ℕ, s ≤ N ∧ X π ρ y s ∈ B := by
      by_contra hno
      apply hnoAvoid
      intro s hs hsx hsmem
      have hmem : X π ρ y s = x ∨ X π ρ y s ∈ B := by
        simpa [K] using hsmem
      rcases hmem with hmem | hmem
      · exact False.elim (hsx hmem)
      · exact False.elim (hno ⟨s, hs, hmem⟩)
    let hexB : ∃ s : ℕ, s ≤ N ∧ X π ρ y s ∈ B := hBhit
    let s₀ := Nat.find hexB
    have hs₀ : s₀ ≤ N ∧ X π ρ y s₀ ∈ B := Nat.find_spec hexB
    have hs₀min : ∀ r < s₀, X π ρ y r ∉ B := by
      intro r hr hrB
      have hprop : r ≤ N ∧ X π ρ y r ∈ B := by
        exact ⟨by omega, hrB⟩
      have hmin := Nat.find_min' hexB hprop
      omega
    have hyB : y ∉ B := by
      apply hB (hsource_mem_R t hy)
    have hs₀pos : 0 < s₀ := by
      by_contra hzero
      have hs₀eq : s₀ = 0 := by omega
      rw [hs₀eq] at hs₀
      exact hyB (by simpa using hs₀.2)
    have hxB : x ∉ B := by
      apply hB
      simpa [R₀, ht] using X_mem_R π ρ x t t le_rfl
    by_cases hprevx : X π ρ y (s₀ - 1) = x
    · have hsourceB : X π ρ y s₀ ∈
          sourceList π ρ y x s₀ := by
        unfold sourceList
        apply List.mem_map.mpr
        refine ⟨s₀ - 1, ?_, ?_⟩
        · apply List.mem_filter.mpr
          refine ⟨List.mem_range.mpr (by omega), ?_⟩
          simp only [decide_eq_true_eq]
          exact hprevx
        · congr 1
          omega
      have hUpos : 0 < (U s₀).count (X π ρ y s₀) := by
        apply List.count_pos_iff.mpr
        simp [U, hsourceB]
      have hPnot : P.count (X π ρ y s₀) = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro hPmem
        exact (hB (hsource_mem_R t hPmem)) hs₀.2
      have hdomS := hdomP s₀ (Nat.le_of_lt (hnot s₀)) (X π ρ y s₀)
      omega
    · have havoidPrev : ∀ r ≤ s₀ - 1, X π ρ y r ≠ x →
          X π ρ y r ∉ K := by
        intro r hr hrx hrK
        have hrmem : X π ρ y r = x ∨ X π ρ y r ∈ B := by
          simpa [K] using hrK
        rcases hrmem with hrmem | hrmem
        · exact hrx hrmem
        · exact (hs₀min r (by omega)) hrmem
      have hprev := hroute (s₀ - 1)
        (Nat.le_of_lt (hnot (s₀ - 1))) havoidPrev
      let u := X π ρ y (s₀ - 1)
      have huK : u ∉ K := by
        intro hu
        have humem : u = x ∨ u ∈ B := by simpa [K] using hu
        rcases humem with humem | humem
        · exact hprevx humem
        · exact (hs₀min (s₀ - 1) (by omega)) humem
      have huσ : 0 < (run π K ξ (E (s₀ - 1))).σ u := by
        have hsigma := hprev.2.2 u
        have hdomu := hdomP (s₀ - 1)
          (Nat.le_of_lt (hnot (s₀ - 1))) u
        have hsigma' : (run π K ξ (E (s₀ - 1))).σ u +
            (U (s₀ - 1)).count u = P.count u + 1 := by
          simpa [u, hprevx, U] using hsigma
        omega
      have hE' : E s₀ = E (s₀ - 1) ++ [u] := by
        have hdel := deletedList_succ π ρ y x (s₀ - 1)
        rw [if_neg hprevx] at hdel
        have hsuc : s₀ - 1 + 1 = s₀ := by omega
        rw [hsuc] at hdel
        simpa [E, u] using hdel
      have hlegS : IsLegal π K ξ (E s₀) := by
        rw [hE', isLegal_append]
        refine ⟨hprev.1, ?_⟩
        rw [isLegal_cons]
        exact ⟨huK, huσ, by simp⟩
      have hleastS := hleast (E s₀) hlegS
      have hq_lt : (E (s₀ - 1)).count u < (D₀ t).count u := by
        have hcount := hleastS.2 u
        rw [hE', List.count_append] at hcount
        simp only [List.count_cons_self, List.count_nil, Nat.zero_add] at hcount
        omega
      have hhead := hhead_of_count (D₀ t) ξ u
        ((E (s₀ - 1)).count u) hgoodEdge hq_lt
      have hboundary :
          (((π.next u) ^ ((E (s₀ - 1)).count u + 1)) (ρ u)).1 =
            X π ρ y s₀ := by
        have hhead' :
            (π.next u ((run π K ξ (E (s₀ - 1))).ρ u)).1 =
              X π ρ y s₀ := by
          rw [hprev.2.1 u (by simpa [u] using hprevx)]
          have hsuc : s₀ - 1 + 1 = s₀ := by omega
          have hsucc := (X_succ π ρ y (s₀ - 1)).symm
          rw [hsuc] at hsucc
          simpa [u] using hsucc
        calc
          (((π.next u) ^ ((E (s₀ - 1)).count u + 1)) (ρ u)).1 =
              (π.next u ((π.next u ^ (E (s₀ - 1)).count u) (ρ u))).1 := by
                have hp := congrArg Subtype.val (show
                    (π.next u) ((π.next u ^ (E (s₀ - 1)).count u) (ρ u)) =
                      ((π.next u) ^ ((E (s₀ - 1)).count u + 1)) (ρ u) by
                    rw [← Equiv.Perm.mul_apply, pow_succ'])
                exact hp.symm
          _ = (π.next u ((run π K ξ (E (s₀ - 1))).ρ u)).1 := by
                rw [run_ρ]
                rfl
          _ = X π ρ y s₀ := hhead'
      have hRhead : X π ρ y s₀ ∈ R₀ := by
        rw [← hboundary]
        simpa [ξ, particleState] using hhead
      exact (hB hRhead) hs₀.2
  have hxinfty : Set.Infinite {t : ℕ | X π ρ y t = x} := by
    by_contra hfinite
    change ¬¬ Set.Finite {t : ℕ | X π ρ y t = x} at hfinite
    have hfin : Set.Finite {t : ℕ | X π ρ y t = x} := not_not.mp hfinite
    obtain ⟨M, hM⟩ := hfin.exists_le
    obtain ⟨n, hn⟩ := hvisit (M + 2)
    have hle : visitCount π ρ y x n ≤ M + 1 := by
      unfold visitCount
      have hsub : (Finset.range n).filter (fun s => X π ρ y s = x) ⊆
          Finset.range (M + 1) := by
        intro s hs
        have hs' := Finset.mem_filter.mp hs
        have hsM := hM s hs'.2
        exact Finset.mem_range.mpr (by omega : s < M + 1)
      have hcard := Finset.card_le_card hsub
      simpa using hcard
    omega
  let p' : Equiv.Perm (G.neighborSet x) := π.next x
  let d' := Fintype.card (G.neighborSet x)
  have hd' : 0 < d' := by
    dsimp [d']
    exact Fintype.card_pos_iff.mpr (π.nonempty x)
  have hperiod' : ∀ a : G.neighborSet x, (p' ^ d') a = a := by
    intro a
    exact pow_card_apply p' (π.cyclic x) a
  have hmul' : ∀ (a : G.neighborSet x) (q : ℕ),
      (p' ^ (d' * q)) a = a := by
    intro a q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hperiod', ih]
  have htimes' : ∀ n : ℕ, ∃ t : ℕ,
      X π ρ y t = x ∧ visitCount π ρ y x t = n :=
    exists_visitCount_eq_of_infinite π ρ y x hxinfty
  let τ' : ℕ → ℕ := fun n => (htimes' n).choose
  have hτ' : ∀ n : ℕ, X π ρ y (τ' n) = x ∧
      visitCount π ρ y x (τ' n) = n := by
    intro n
    exact (htimes' n).choose_spec
  have hτinj' : Function.Injective τ' := by
    intro a b hab
    have ha' := (hτ' a).2
    have hb' := (hτ' b).2
    rw [hab] at ha'
    omega
  obtain ⟨k', hk'⟩ := π.cyclic x (p' (ρ x)) ⟨y, hxy⟩
  let f' : ℕ → ℕ := fun q => τ' (k' + d' * q)
  have hf' : Function.Injective f' := by
    intro a b hab
    have hab' := hτinj' hab
    apply Nat.mul_left_cancel
    · exact hd'
    · exact Nat.add_left_cancel hab'
  let g' : ℕ → ℕ := fun q => f' q + 1
  have hg' : Function.Injective g' := by
    intro a b hab
    apply hf'
    dsimp [g'] at hab
    omega
  have hgrange' : (Set.range g').Infinite := Set.infinite_range_of_injective hg'
  have hsub' : Set.range g' ⊆ {t : ℕ | X π ρ y t = y} := by
    intro t ht
    obtain ⟨q, rfl⟩ := ht
    have hqt := hτ' (k' + d' * q)
    have hrot := rot_eq_pow_visitCount π ρ y x (τ' (k' + d' * q))
    have hdest :
        (p' ^ (k' + d' * q + 1)) (ρ x) = ⟨y, hxy⟩ := by
      calc
        (p' ^ (k' + d' * q + 1)) (ρ x) =
            (p' ^ (k' + 1)) ((p' ^ (d' * q)) (ρ x)) := by
              rw [show k' + d' * q + 1 = (k' + 1) + d' * q by omega,
                pow_add, Equiv.Perm.mul_apply]
        _ = (p' ^ (k' + 1)) (ρ x) := by rw [hmul']
        _ = (p' ^ k') (p' (ρ x)) := by
          rw [pow_succ, Equiv.Perm.mul_apply]
        _ = ⟨y, hxy⟩ := hk'
    have hX := X_succ π ρ y (τ' (k' + d' * q))
    rw [hqt.1, hrot, hqt.2] at hX
    have hpow :
        p' ((p' ^ (k' + d' * q)) (ρ x)) =
          (p' ^ (k' + d' * q + 1)) (ρ x) := by
      rw [← Equiv.Perm.mul_apply, pow_succ']
    change X π ρ y (f' q + 1) = y
    rw [hX, hpow, hdest]
  exact recurrent_of_infinite_visits π hV hG ρ y
    (hgrange'.mono hsub')

-- FROZEN-STATEMENT-BEGIN
/-- Angel–Holroyd Theorem 1 (`external input, Angel-Holroyd 2012 Theorem 1, cited in
the proof of prop:live-recurrence`), proved rather than assumed. -/
theorem recurrentOfRecurrent_holds : Rotor.External.RecurrentOfRecurrent G
-- FROZEN-STATEMENT-END
:= by
  intro π hV hG ρ o o' ho
  have hwalk : ∀ {u v : V} (p : G.Walk u v),
      Recurrent π ρ u → Recurrent π ρ v := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
        intro hu
        exact ih (recurrent_of_adjacent π hV hG ρ u v huv hu)
  exact hwalk (hG o o').some ho

end Rotor.Bridge
