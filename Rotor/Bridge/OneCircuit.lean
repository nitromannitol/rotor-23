import Rotor.External.OneCircuit
import Rotor.Support.WalkBasics

/-!
# FLP Lemmas 2.1 and 2.4: one circuit traverses every edge at most once

For every `n` with `T(n) < ⊤`, the rotor walk traverses no directed edge twice during the time
interval `[T(n), T(n+1))`, and if `T(n+1) < ⊤` it departs from every vertex reachable from the
origin in that interval exactly as many times as that vertex's degree. Proved unconditionally in
the `Aux` namespace by an injectivity argument on traversed edges together with incoming and
outgoing degree bounds at the circuit times `T(n)`.
-/

namespace Rotor.Bridge

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

namespace Aux

variable {G}

omit [G.LocallyFinite] in
/-- The rotor at `x` at time `b` is obtained from its value at time `a` by iterating the
mechanism's next map once for each departure from `x` in `[a, b)`. -/
theorem rot_eq_pow_departures (π : Mechanism G) (ρ : Config G) (o : V)
  (a b : ℕ) (x : V) (hab : a ≤ b) :
    rot π ρ o b x = ((π.next x) ^ departures π ρ o x a b) (rot π ρ o a x) := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp [departures]
  | succ b hab ih =>
      rw [rot_succ]
      by_cases hx : X π ρ o b = x
      · rw [hx, Function.update_self]
        rw [ih]
        have hI : Ico a (b + 1) = insert b (Ico a b) := by
          ext u
          simp only [mem_Ico, mem_insert]
          omega
        have hd : departures π ρ o x a (b + 1) =
            departures π ρ o x a b + 1 := by
          unfold departures
          rw [hI, filter_insert]
          simp [hx]
        rw [hd, pow_succ']
        rfl
      · rw [Function.update_of_ne (Ne.symm hx), ih]
        have hI : Ico a (b + 1) = insert b (Ico a b) := by
          ext u
          simp only [mem_Ico, mem_insert]
          omega
        have hd : departures π ρ o x a (b + 1) =
            departures π ρ o x a b := by
          unfold departures
          rw [hI, filter_insert]
          simp [hx]
        rw [hd]

omit [DecidableEq V] in
/-- If two iterates of the cyclic order at `v` agree on a neighbor, the gap between their
exponents is at least `G.degree v`, since that cyclic order has period `G.degree v`. -/
theorem degree_le_sub_of_pow_eq (π : Mechanism G) (v : V)
    (x : G.neighborSet v) (a b : ℕ) (hab : a < b)
    (h : ((π.next v) ^ a) x = ((π.next v) ^ b) x) : G.degree v ≤ b - a := by
  set f := π.next v with hf
  set p := b - a with hp
  have hp0 : 0 < p := by omega
  have hb : b = a + p := by omega
  have key : (f ^ p) x = x := by
    have : (f ^ a) ((f ^ p) x) = (f ^ a) x := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, ← hb, h]
    exact (f ^ a).injective this
  have hmul : ∀ q : ℕ, (f ^ (p * q)) x = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, key, ih]
  have hmod : ∀ k : ℕ, (f ^ k) x = (f ^ (k % p)) x := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k p, add_comm, pow_add, Equiv.Perm.mul_apply, hmul]
  have hsurj : Function.Surjective (fun i : Fin p => (f ^ (i : ℕ)) x) := by
    intro y
    obtain ⟨k, hk⟩ := π.cyclic v x y
    refine ⟨⟨k % p, Nat.mod_lt _ hp0⟩, ?_⟩
    simp only
    rw [← hmod, hk]
  have := Fintype.card_le_of_surjective _ hsurj
  rwa [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] at this

omit [G.LocallyFinite] in
/-- Between two visits to the origin, the number of departures from `x` on `[a, b)` equals the
number of arrivals at `x` on the same interval. -/
theorem departures_eq_card_arrivals (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ) (x : V) (hab : a ≤ b)
    (hXa : X π ρ o a = o) (hXb : X π ρ o b = o) :
    departures π ρ o x a b =
      ((Ico a b).filter (fun t => X π ρ o (t + 1) = x)).card := by
  classical
  let f : ℕ → ℤ := fun t => if X π ρ o t = x then 1 else 0
  have hs : (∑ t ∈ Ico a b, f t) =
      ∑ t ∈ Ico a b, f (t + 1) := by
    calc
      (∑ t ∈ Ico a b, f t) = (∑ t ∈ range b, f t) - ∑ t ∈ range a, f t :=
        sum_Ico_eq_sub f hab
      _ = (∑ t ∈ range (b + 1), f t) - ∑ t ∈ range (a + 1), f t := by
        rw [sum_range_succ, sum_range_succ]
        simp only [f]
        split <;> split <;> simp_all
      _ = ∑ t ∈ Ico (a + 1) (b + 1), f t :=
        (sum_Ico_eq_sub f (Nat.succ_le_succ hab)).symm
      _ = ∑ t ∈ Ico a b, f (t + 1) := (sum_Ico_add' f a b 1).symm
  unfold departures
  rw [card_filter, card_filter]
  have hs' : (∑ t ∈ Ico a b, (if X π ρ o t = x then (1 : ℤ) else 0)) =
      ∑ t ∈ Ico a b, (if X π ρ o (t + 1) = x then (1 : ℤ) else 0) := by
    simpa [f] using hs
  exact_mod_cast hs'

omit [G.LocallyFinite] in
/-- If the origin has been visited more than `q` times by time `a`, some earlier time is itself a
visit to the origin with at least `q` visits recorded there. -/
theorem exists_prior_return_of_lt_visits (π : Mechanism G) (ρ : Config G) (o : V)
    (q a : ℕ) (hq : q < visits π ρ o a) :
    ∃ t < a, X π ρ o t = o ∧ q ≤ visits π ρ o t := by
  classical
  let F : Finset ℕ := (range a).filter (fun t => X π ρ o t = o)
  have hF : F.card = visits π ρ o a := by
    rfl
  have hq1 : q + 1 ≤ F.card := by omega
  obtain ⟨S, hSF, hScard⟩ := exists_subset_card_eq hq1
  have hSne : S.Nonempty := by
    apply (card_pos.1 ?_)
    omega
  let t : ℕ := S.max' hSne
  have htS : t ∈ S := by
    exact Finset.max'_mem S hSne
  have htF : t ∈ F := hSF htS
  have hta : t < a := (mem_range.1 (mem_filter.1 htF).1)
  have hbelow : S.erase t ⊆ F.filter (fun u => u < t) := by
    intro u hu
    have hut : u ≠ t := (mem_erase.1 hu).1
    have huS : u ∈ S := (mem_erase.1 hu).2
    have hule : u ≤ t := by
      exact Finset.le_max' S u huS
    have hut' : u < t := lt_of_le_of_ne hule hut
    exact mem_filter.2 ⟨hSF huS, hut'⟩
  have hcardbelow : q ≤ (F.filter (fun u => u < t)).card := by
    have herase : (S.erase t).card = q := by
      rw [card_erase_of_mem htS, hScard]
      omega
    exact herase ▸ card_le_card hbelow
  have hFt : F.filter (fun u => u < t) =
      (range t).filter (fun u => X π ρ o u = o) := by
    ext u
    simp only [F, mem_filter, mem_range]
    constructor
    · rintro ⟨⟨hua, hxu⟩, hut⟩
      exact ⟨hut, hxu⟩
    · rintro ⟨hut, hxu⟩
      exact ⟨⟨by omega, hxu⟩, hut⟩
  refine ⟨t, hta, (mem_filter.1 htF).2, ?_⟩
  rw [hFt] at hcardbelow
  simpa [visits] using hcardbelow

omit [G.LocallyFinite] in
/-- Restates `mem_R`: a vertex lies in the range `R t` exactly when the walk visits it by time
`t`. -/
theorem mem_R_iff (π : Mechanism G) (ρ : Config G) (o : V) (t : ℕ) (x : V) :
    x ∈ R π ρ o t ↔ ∃ s ≤ t, X π ρ o s = x := by
  simp [R, Finset.mem_image]

omit [G.LocallyFinite] in
/-- Among the visits to `x` at times up to `a`, there is a last one, after which the walk does
not return to `x` before time `a`. -/
theorem exists_last_visit_le (π : Mechanism G) (ρ : Config G) (o : V)
    (a : ℕ) (x : V) (hx : x ∈ R π ρ o a) :
    ∃ t ≤ a, X π ρ o t = x ∧
      ∀ u, t < u → u ≤ a → X π ρ o u ≠ x := by
  classical
  obtain ⟨t₀, ht₀, hxt₀⟩ := (mem_R_iff π ρ o a x).1 hx
  let S : Finset ℕ := (range (a + 1)).filter (fun t => X π ρ o t = x)
  have hSt₀ : t₀ ∈ S := by
    rw [mem_filter]
    exact ⟨by simp [ht₀], hxt₀⟩
  have hSne : S.Nonempty := ⟨t₀, hSt₀⟩
  let t := S.max' hSne
  have htS : t ∈ S := Finset.max'_mem S hSne
  have hta : t ≤ a := by
    have := mem_range.1 (mem_filter.1 htS).1
    omega
  have hxt : X π ρ o t = x := (mem_filter.1 htS).2
  refine ⟨t, hta, hxt, ?_⟩
  intro u htu hua hux
  have huS : u ∈ S := by
    rw [mem_filter]
    exact ⟨by simp [hua], hux⟩
  have hut : u ≤ t := Finset.le_max' S u huS
  omega

/-- When `T n < ⊤`, the visit count to the origin at time `T n` is exactly `G.degree o * n`. -/
theorem visits_T_eq (π : Mechanism G) (ρ : Config G) (o : V) (n : ℕ)
    (h : T π ρ o n < ⊤) :
    visits π ρ o (T π ρ o n).toNat = G.degree o * n := by
  have hm := T_mem π ρ o n h
  have hle := hm.2
  by_contra hne
  have hlt : G.degree o * n < visits π ρ o (T π ρ o n).toNat := by omega
  obtain ⟨t, hta, hXt, hvt⟩ :=
    exists_prior_return_of_lt_visits π ρ o (G.degree o * n) _ hlt
  have hc : t ∈ circuitSet π ρ o n := ⟨hXt, hvt⟩
  have hmin := T_min π ρ o n hc
  omega

omit [G.LocallyFinite] in
/-- If no two distinct times in `[a, b)` traverse the same edge, the traversal map is injective
on that interval. -/
theorem traversal_injOn_of_forall_ne (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ)
    (h : ∀ s t : ℕ, s ∈ Ico a b → t ∈ Ico a b → s < t →
      traversal π ρ o s ≠ traversal π ρ o t) :
    Set.InjOn (traversal π ρ o) (Ico a b : Set ℕ) := by
  intro s hs t ht heq
  rcases lt_or_ge s t with hst | hst
  · exact False.elim (h s t hs ht hst heq)
  · rcases lt_or_ge t s with hts | hts
    · exact False.elim (h t s ht hs hts heq.symm)
    · exact le_antisymm hts hst

omit [G.LocallyFinite] in
/-- If `x` is never visited on `[a, b)`, the rotor at `x` is unchanged from time `a` to time `b`. -/
theorem rot_eq_of_no_departure (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ) (x : V) (hab : a ≤ b)
    (h : ∀ t ∈ Ico a b, X π ρ o t ≠ x) :
    rot π ρ o b x = rot π ρ o a x := by
  have hd : departures π ρ o x a b = 0 := by
    unfold departures
    rw [card_eq_zero]
    rw [filter_eq_empty_iff]
    intro t ht
    exact h t ht
  rw [rot_eq_pow_departures π ρ o a b x hab, hd]
  simp

omit [G.LocallyFinite] in
/-- If `t` is the last visit to `x` before time `a`, the rotor edge out of `x` at time `a` points
to the walk's position right after that visit. -/
theorem rotor_edge_of_last (π : Mechanism G) (ρ : Config G) (o : V)
    (t a : ℕ) (x : V) (hxt : X π ρ o t = x) (ht : t < a)
    (hlast : ∀ u, t < u → u < a → X π ρ o u ≠ x) :
    (rot π ρ o a x).1 = X π ρ o (t + 1) := by
  have hta : t + 1 ≤ a := by omega
  have hno : ∀ u ∈ Ico (t + 1) a, X π ρ o u ≠ x := by
    intro u hu
    rcases mem_Ico.1 hu with ⟨hu1, hu2⟩
    exact hlast u (by omega) hu2
  have hrot := rot_eq_of_no_departure π ρ o (t + 1) a x hta hno
  rw [hrot, rot_succ]
  rw [X_succ, hxt, Function.update_self]

omit [G.LocallyFinite] in
/-- Following the rotor edges at time `a`, starting from any position `x` visited by time `a` and
returning to `o`, traces a directed path back to the origin. -/
theorem rotor_path_of_mem (π : Mechanism G) (ρ : Config G) (o : V)
    (a : ℕ) (hXa : X π ρ o a = o) :
    ∀ t x, t ≤ a → X π ρ o t = x →
      (∀ u, t < u → u ≤ a → X π ρ o u ≠ x) →
      Relation.ReflTransGen (fun v w => (rot π ρ o a v).1 = w) x o := by
  have aux : ∀ d : ℕ, ∀ t x, a - t = d → t ≤ a → X π ρ o t = x →
      (∀ u, t < u → u ≤ a → X π ρ o u ≠ x) →
      Relation.ReflTransGen (fun v w => (rot π ρ o a v).1 = w) x o := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro t x hdt hta hxt hlast
        by_cases hd : d = 0
        · have hta' : t = a := by omega
          subst t
          have hxo : x = o := hxt.symm.trans hXa
          rw [hxo]
        · have hta' : t < a := by omega
          let y := X π ρ o (t + 1)
          have hxy : (rot π ρ o a x).1 = y := by
            apply rotor_edge_of_last π ρ o t a x hxt hta'
            intro u htu hua
            exact hlast u htu (by omega)
          by_cases hyo : y = o
          · exact Relation.ReflTransGen.single (by simpa [y, hyo] using hxy)
          · let S : Finset ℕ := (range (a + 1)).filter (fun u => X π ρ o u = y)
            have hSt : t + 1 ∈ S := by
              rw [mem_filter]
              refine ⟨?_, rfl⟩
              simp only [mem_range]
              omega
            have hSne : S.Nonempty := ⟨t + 1, hSt⟩
            let u : ℕ := S.max' hSne
            have huS : u ∈ S := Finset.max'_mem S hSne
            have huA : u ≤ a := by
              have := mem_range.1 (mem_filter.1 huS).1
              omega
            have htu : t < u := by
              have := Finset.le_max' S (t + 1) hSt
              omega
            have huy : X π ρ o u = y := (mem_filter.1 huS).2
            have hua : u < a := by
              by_contra hua
              have : u = a := by omega
              rw [this] at huy
              exact hyo (huy.symm.trans hXa)
            have hulast : ∀ v, u < v → v ≤ a → X π ρ o v ≠ y := by
              intro v huv hva hvy
              have hvS : v ∈ S := by
                rw [mem_filter]
                refine ⟨?_, hvy⟩
                simp only [mem_range]
                omega
              have hvle : v ≤ u := by
                exact Finset.le_max' S v hvS
              exact (Nat.not_lt_of_ge hvle) huv
            have hsmall : a - u < d := by omega
            have hpath := ih (a - u) hsmall u y rfl huA huy hulast
            have hfirst : Relation.ReflTransGen
                (fun v w => (rot π ρ o a v).1 = w) x y :=
              Relation.ReflTransGen.single hxy
            exact hfirst.trans hpath
  intro t x hta hxt hlast
  exact aux (a - t) t x rfl hta hxt hlast

omit [G.LocallyFinite] in
/-- The number of departures from `x` on `[a, b)` is monotone in `b`. -/
theorem departures_mono (π : Mechanism G) (ρ : Config G) (o : V) (x : V)
    {a b c : ℕ} (_hab : a ≤ b) (hbc : b ≤ c) :
    departures π ρ o x a b ≤ departures π ρ o x a c := by
  unfold departures
  apply Finset.card_le_card
  refine Finset.filter_subset_filter _ ?_
  intro t ht
  exact Finset.mem_Ico.2 ⟨Finset.mem_Ico.1 ht |>.1,
    lt_of_lt_of_le (Finset.mem_Ico.1 ht |>.2) hbc⟩

omit [G.LocallyFinite] in
/-- The number of departures from `x` on a subinterval `[s, t) ⊆ [a, b)` is at most the number of
departures on `[a, b)`. -/
theorem departures_subinterval (π : Mechanism G) (ρ : Config G) (o : V) (x : V)
    {a s t b : ℕ} (has : a ≤ s) (hbt : t ≤ b) (_hst : s ≤ t) :
    departures π ρ o x s t ≤ departures π ρ o x a b := by
  unfold departures
  apply Finset.card_le_card
  refine Finset.filter_subset_filter _ ?_
  intro u hu
  exact Finset.mem_Ico.2 ⟨has.trans (Finset.mem_Ico.1 hu |>.1),
    lt_of_lt_of_le (Finset.mem_Ico.1 hu |>.2) hbt⟩

omit [G.LocallyFinite] in
/-- Counting departures from `x` on `[a, b)` together with an indicator for the right endpoint
equals counting arrivals at `x` together with an indicator for the left endpoint. -/
theorem endpoint_count (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ) (x : V) (hab : a ≤ b) :
    departures π ρ o x a b + (if X π ρ o b = x then 1 else 0) =
      ((Ico a b).filter (fun t => X π ρ o (t + 1) = x)).card +
        (if X π ρ o a = x then 1 else 0) := by
  classical
  let f : ℕ → ℤ := fun t => if X π ρ o t = x then 1 else 0
  have hs : (∑ t ∈ Ico a b, f t) + (if X π ρ o b = x then 1 else 0) =
      (∑ t ∈ Ico a b, f (t + 1)) + (if X π ρ o a = x then 1 else 0) := by
    calc
      (∑ t ∈ Ico a b, f t) + (if X π ρ o b = x then 1 else 0) =
          ((∑ t ∈ range b, f t) - ∑ t ∈ range a, f t) +
            (if X π ρ o b = x then 1 else 0) := by rw [sum_Ico_eq_sub f hab]
      _ = ((∑ t ∈ range (b + 1), f t) - ∑ t ∈ range (a + 1), f t) +
            (if X π ρ o a = x then 1 else 0) := by
        rw [sum_range_succ, sum_range_succ]
        simp only [f]
        split <;> split <;> simp_all <;> ring
      _ = (∑ t ∈ Ico (a + 1) (b + 1), f t) +
            (if X π ρ o a = x then 1 else 0) := by
        rw [sum_Ico_eq_sub f (Nat.succ_le_succ hab)]
      _ = (∑ t ∈ Ico a b, f (t + 1)) +
            (if X π ρ o a = x then 1 else 0) := by
        rw [sum_Ico_add' f a b 1]
  unfold departures
  rw [card_filter, card_filter]
  have hs' :
      (∑ t ∈ Ico a b, (if X π ρ o t = x then (1 : ℤ) else 0)) +
          (if X π ρ o b = x then 1 else 0) =
        (∑ t ∈ Ico a b, (if X π ρ o (t + 1) = x then (1 : ℤ) else 0)) +
          (if X π ρ o a = x then 1 else 0) := by
    simpa [f] using hs
  exact_mod_cast hs'

/-- If the walk traverses the same edge at two times `s < t` with `s ≥ a`, the number of
departures from that edge's source on `[a, t)` is at least the vertex's degree. -/
theorem departures_lower_of_repeat (π : Mechanism G) (ρ : Config G) (o : V)
    (a s t : ℕ) (has : a ≤ s) (hst : s < t) (x : V) (hxs : X π ρ o s = x)
    (hrep : traversal π ρ o s = traversal π ρ o t) :
    G.degree x ≤ departures π ρ o x a t := by
  have hXs : X π ρ o s = x := hxs
  have hXt : X π ρ o t = x := by
    have := congrArg Prod.fst hrep
    simpa [traversal, hXs] using this.symm
  have hhead_eq : X π ρ o (s + 1) = X π ρ o (t + 1) := by
    simpa [traversal] using congrArg Prod.snd hrep
  have hnext_eq : π.next x (rot π ρ o s x) = π.next x (rot π ρ o t x) := by
    apply Subtype.ext
    rw [X_succ, hXs, X_succ, hXt] at hhead_eq
    exact hhead_eq
  have hrot_eq : rot π ρ o s x = rot π ρ o t x :=
    (π.next x).injective hnext_eq
  have hrot := rot_eq_pow_departures π ρ o s t x hst.le
  let d := departures π ρ o x s t
  have hrot' : rot π ρ o t x = ((π.next x) ^ d) (rot π ρ o s x) := by
    simpa [d] using hrot
  have hpow : ((π.next x) ^ d) (rot π ρ o s x) = rot π ρ o s x := by
    exact hrot'.symm.trans hrot_eq.symm
  have hdpos : 0 < d := by
    dsimp [d]
    unfold departures
    apply card_pos.2
    refine ⟨s, ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨le_rfl, hst⟩, hXs⟩
  have hdeg : G.degree x ≤ d := by
    have hc := degree_le_sub_of_pow_eq π x (rot π ρ o s x) 0 d hdpos
      (by simpa using hpow.symm)
    simpa using hc
  exact hdeg.trans (departures_subinterval π ρ o x has le_rfl hst.le)

/-- If the traversal map is injective on `[a, b)`, the number of arrivals at `x` on that interval
is at most `G.degree x`. -/
theorem incoming_card_le (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ) (htr : Set.InjOn (traversal π ρ o) (Ico a b : Set ℕ)) (x : V) :
    ((Ico a b).filter (fun t => X π ρ o (t + 1) = x)).card ≤ G.degree x := by
  classical
  let S : Finset ℕ := (Ico a b).filter (fun t => X π ρ o (t + 1) = x)
  let E : Finset V := S.image (fun t => X π ρ o t)
  have hSinj : Set.InjOn (X π ρ o) (S : Set ℕ) := by
    intro s hs t ht heq
    have hs' : s ∈ Ico a b := (Finset.mem_filter.1 hs).1
    have ht' : t ∈ Ico a b := (Finset.mem_filter.1 ht).1
    have hsy := (Finset.mem_filter.1 hs).2
    have hty := (Finset.mem_filter.1 ht).2
    apply htr hs' ht'
    simp [traversal, heq, hsy, hty]
  have hEcard : E.card = S.card := Finset.card_image_of_injOn hSinj
  have hEsub : E ⊆ G.neighborFinset x := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
    have htx := (Finset.mem_filter.1 ht).2
    rw [SimpleGraph.mem_neighborFinset]
    rw [← htx]
    exact G.adj_symm (adj_X_succ π ρ o t)
  have hcard : E.card ≤ G.degree x := by
    exact (Finset.card_le_card hEsub).trans_eq (SimpleGraph.card_neighborFinset_eq_degree G x)
  rw [hEcard] at hcard
  exact hcard

/-- If the traversal map is injective on `[a, b)`, the number of departures from `x` on that
interval is at most `G.degree x`. -/
theorem outgoing_card_le (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ) (htr : Set.InjOn (traversal π ρ o) (Ico a b : Set ℕ)) (x : V) :
    departures π ρ o x a b ≤ G.degree x := by
  classical
  let S : Finset ℕ := (Ico a b).filter (fun t => X π ρ o t = x)
  let E : Finset V := S.image (fun t => X π ρ o (t + 1))
  have hSinj : Set.InjOn (fun t => X π ρ o (t + 1)) (S : Set ℕ) := by
    intro s hs t ht heq
    have hs' : s ∈ Ico a b := (Finset.mem_filter.1 hs).1
    have ht' : t ∈ Ico a b := (Finset.mem_filter.1 ht).1
    have hxs : X π ρ o s = x := (Finset.mem_filter.1 hs).2
    have hxt : X π ρ o t = x := (Finset.mem_filter.1 ht).2
    apply htr hs' ht'
    simp [traversal, hxs, hxt, heq]
  have hEcard : E.card = S.card := Finset.card_image_of_injOn hSinj
  have hEsub : E ⊆ G.neighborFinset x := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
    have htx := (Finset.mem_filter.1 ht).2
    rw [SimpleGraph.mem_neighborFinset]
    rw [← htx]
    exact adj_X_succ π ρ o t
  have hcard : E.card ≤ G.degree x := by
    exact (Finset.card_le_card hEsub).trans_eq (SimpleGraph.card_neighborFinset_eq_degree G x)
  rw [hEcard] at hcard
  exact hcard

omit [G.LocallyFinite] in
/-- The visit count to the origin at time `b` is the visit count at an earlier time `a` plus the
number of departures from the origin on `[a, b)`. -/
theorem visits_add_departures (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ) (hab : a ≤ b) :
    visits π ρ o b = visits π ρ o a + departures π ρ o o a b := by
  classical
  let f : ℕ → ℤ := fun t => if X π ρ o t = o then 1 else 0
  have hs : (∑ t ∈ range b, f t) = (∑ t ∈ range a, f t) + ∑ t ∈ Ico a b, f t := by
    rw [sum_Ico_eq_sub f hab]
    ring
  unfold visits departures
  rw [card_filter, card_filter, card_filter]
  have hs' :
      (∑ t ∈ range b, (if X π ρ o t = o then (1 : ℤ) else 0)) =
        (∑ t ∈ range a, (if X π ρ o t = o then (1 : ℤ) else 0)) +
          ∑ t ∈ Ico a b, (if X π ρ o t = o then (1 : ℤ) else 0) := by
    simpa [f] using hs
  exact_mod_cast hs'

/-- Before the next circuit time `T (n + 1)`, no edge is traversed twice: the traversal map is
injective on `[a, b + 1)` whenever `a` records at least `G.degree o * n` visits to the origin
and `b` precedes `T (n + 1)`. -/
theorem no_repeat (π : Mechanism G) (ρ : Config G) (o : V) (n : ℕ)
    (a b : ℕ) (hab : a ≤ b) (hXa : X π ρ o a = o)
    (hvis : G.degree o * n ≤ visits π ρ o a)
    (hupper : (b : ℕ∞) < T π ρ o (n + 1)) :
    Set.InjOn (traversal π ρ o) (Ico a (b + 1) : Set ℕ) := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp
  | succ b hab ih =>
      have hprev : (b : ℕ∞) < T π ρ o (n + 1) := by
        exact lt_of_le_of_lt (by exact_mod_cast Nat.le_succ b) hupper
      have htr : Set.InjOn (traversal π ρ o) (Ico a (b + 1) : Set ℕ) := ih hprev
      have hab1 : a ≤ b + 1 := by omega
      have hnot : ∀ s ∈ Ico a (b + 1), traversal π ρ o s ≠ traversal π ρ o (b + 1) := by
        intro s hs hrep
        let x := X π ρ o (b + 1)
        have hxs : X π ρ o s = x := by
          have h := congrArg Prod.fst hrep
          simpa [traversal, x] using h
        have hdeg := departures_lower_of_repeat π ρ o a s (b + 1)
          (Finset.mem_Ico.1 hs).1 (Finset.mem_Ico.1 hs).2 x hxs hrep
        by_cases hxo : x = o
        · have hvb : visits π ρ o (b + 1) =
              visits π ρ o a + departures π ρ o o a (b + 1) :=
            visits_add_departures π ρ o a (b + 1) hab1
          have hdepo : G.degree o ≤ departures π ρ o o a (b + 1) := by
            rw [hxo] at hdeg
            exact hdeg
          have hq : G.degree o * (n + 1) ≤ visits π ρ o (b + 1) := by
            rw [hvb]
            rw [Nat.mul_succ]
            omega
          have hc : b + 1 ∈ circuitSet π ρ o (n + 1) := by
            refine ⟨?_, hq⟩
            simpa [x] using hxo
          have hle := T_le_of_mem π ρ o (n + 1) hc
          have : ((b + 1 : ℕ) : ℕ∞) < ((b + 1 : ℕ) : ℕ∞) :=
            lt_of_lt_of_le hupper hle
          exact (lt_irrefl _ this)
        · have hcnt := endpoint_count π ρ o a (b + 1) x hab1
          have hin := incoming_card_le π ρ o a (b + 1) htr x
          have hle : departures π ρ o x a (b + 1) + 1 ≤ G.degree x := by
            have hcnt' : departures π ρ o x a (b + 1) + 1 =
                ((Ico a (b + 1)).filter (fun t => X π ρ o (t + 1) = x)).card := by
              simpa [x, hXa, hxo, Ne.symm hxo] using hcnt
            rw [hcnt']
            exact hin
          omega
      intro s hs u hu heq
      have hs_upper : s < (b + 1) + 1 := by
        simpa using (Finset.mem_Ico.1 hs).2
      have hu_upper : u < (b + 1) + 1 := by
        simpa using (Finset.mem_Ico.1 hu).2
      by_cases hs_eq : s = b + 1
      · by_cases hu_eq : u = b + 1
        · omega
        · have hu_old : u < b + 1 := by omega
          exact False.elim (hnot u
            (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hu).1, hu_old⟩)
            (by simpa [hs_eq] using heq.symm))
      · have hs_old : s < b + 1 := by omega
        by_cases hu_eq : u = b + 1
        · exact False.elim (hnot s
            (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hs).1, hs_old⟩)
            (by simpa [hu_eq] using heq))
        · have hu_old : u < b + 1 := by omega
          exact htr (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hs).1, hs_old⟩)
            (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hu).1, hu_old⟩) heq

/-- On the interval between two consecutive circuit times `a` and `T (n + 1)`, the traversal map
is injective. -/
theorem interval_inj (π : Mechanism G) (ρ : Config G) (o : V) (n : ℕ)
    (a b : ℕ) (hab : a ≤ b) (hXa : X π ρ o a = o)
    (hvis : G.degree o * n ≤ visits π ρ o a)
    (hnext : (b : ℕ∞) = T π ρ o (n + 1))
    (_hb : T π ρ o (n + 1) < ⊤) :
    Set.InjOn (traversal π ρ o) (Ico a b : Set ℕ) := by
  by_cases hab' : a = b
  · subst b
    simp
  by_cases hb0 : b = 0
  · subst b
    omega
  have hablt : a < b := lt_of_le_of_ne hab (fun h => hab' h)
  have hap : a ≤ b - 1 := by omega
  have hprev : ((b - 1 : ℕ) : ℕ∞) < T π ρ o (n + 1) := by
    rw [← hnext]
    exact_mod_cast Nat.sub_lt (Nat.pos_of_ne_zero hb0) (by omega)
  have h := no_repeat π ρ o n a (b - 1) hap hXa hvis hprev
  have hsucc : b - 1 + 1 = b := by omega
  simpa [hsucc] using h

omit [G.LocallyFinite] in
/-- Extending the interval `[a, k)` to `[a, k + 1)` increases the departure count from `x` by one
exactly when time `k` is a visit to `x`. -/
theorem departures_succ (π : Mechanism G) (ρ : Config G) (o : V) (x : V)
    (a k : ℕ) (hak : a ≤ k) (hx : X π ρ o k = x) :
    departures π ρ o x a (k + 1) = departures π ρ o x a k + 1 := by
  unfold departures
  have hI : Ico a (k + 1) = insert k (Ico a k) := by
    ext u
    simp only [mem_Ico, mem_insert]
    omega
  rw [hI, filter_insert]
  simp [hx]

/-- If some traversed edge out of `x` at a time in `[a, b)` matches the rotor edge out of `x` at
time `a`, the number of departures from `x` on `[a, b)` is at least `G.degree x`. -/
theorem departures_lower_of_rotor_edge (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ) (_hab : a ≤ b) (x y : V) (hrot : (rot π ρ o a x).1 = y)
    (hused : ∃ k ∈ Ico a b, traversal π ρ o k = (x, y)) :
    G.degree x ≤ departures π ρ o x a b := by
  obtain ⟨k, hk, htr⟩ := hused
  have hka : a ≤ k := (mem_Ico.1 hk).1
  have hkb : k < b := (mem_Ico.1 hk).2
  have hkx : X π ρ o k = x := by
    simpa [traversal] using congrArg Prod.fst htr
  have hky : X π ρ o (k + 1) = y := by
    simpa [traversal] using congrArg Prod.snd htr
  have hrotk := rot_eq_pow_departures π ρ o a k x hka
  have hnext : π.next x (rot π ρ o k x) = rot π ρ o a x := by
    apply Subtype.ext
    rw [X_succ, hkx] at hky
    exact hky.trans hrot.symm
  let d := departures π ρ o x a k
  have hpow : ((π.next x) ^ (d + 1)) (rot π ρ o a x) = rot π ρ o a x := by
    calc
      ((π.next x) ^ (d + 1)) (rot π ρ o a x) =
          (π.next x) (((π.next x) ^ d) (rot π ρ o a x)) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
      _ = (π.next x) (rot π ρ o k x) := by rw [← hrotk]
      _ = rot π ρ o a x := hnext
  have hdeg : G.degree x ≤ d + 1 := by
    have hc := degree_le_sub_of_pow_eq π x (rot π ρ o a x) 0 (d + 1) (by omega)
      (by simpa using hpow.symm)
    simpa using hc
  have hds : d + 1 ≤ departures π ρ o x a (k + 1) := by
    rw [departures_succ π ρ o x a k hka hkx]
  have hka1 : a ≤ k + 1 := hka.trans (Nat.le_succ k)
  have hkb1 : k + 1 ≤ b := by omega
  exact hdeg.trans (hds.trans (departures_mono π ρ o x hka1 hkb1))

/-- If the traversal map is injective on `[a, b)` and `y` receives exactly `G.degree y` arrivals
there, every neighbor of `y` is the source of one of those arrivals. -/
theorem incoming_used (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ) (hab : a ≤ b) (x y : V) (hXa : X π ρ o a = o) (hXb : X π ρ o b = o)
    (htr : Set.InjOn (traversal π ρ o) (Ico a b : Set ℕ))
    (hy : departures π ρ o y a b = G.degree y) (hxy : G.Adj x y) :
    ∃ t ∈ Ico a b, traversal π ρ o t = (x, y) := by
  classical
  let S : Finset ℕ := (Ico a b).filter (fun t => X π ρ o (t + 1) = y)
  let E : Finset V := S.image (fun t => X π ρ o t)
  have hScard : S.card = G.degree y := by
    have hc := departures_eq_card_arrivals π ρ o a b y hab hXa hXb
    rw [← hc]
    exact hy
  have hSinj : Set.InjOn (X π ρ o) (S : Set ℕ) := by
    intro s hs t ht heq
    have hs' : s ∈ Ico a b := (mem_filter.1 hs).1
    have ht' : t ∈ Ico a b := (mem_filter.1 ht).1
    have hsy : X π ρ o (s + 1) = y := (mem_filter.1 hs).2
    have hty : X π ρ o (t + 1) = y := (mem_filter.1 ht).2
    apply htr hs' ht'
    simp [traversal, heq, hsy, hty]
  have hEcard : E.card = G.degree y := by
    rw [show E.card = S.card from card_image_of_injOn hSinj, hScard]
  have hEsub : E ⊆ G.neighborFinset y := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hz
    have hty := (mem_filter.1 ht).2
    rw [SimpleGraph.mem_neighborFinset]
    rw [← hty]
    exact G.adj_symm (adj_X_succ π ρ o t)
  have hEeq : E = G.neighborFinset y := by
    apply eq_of_subset_of_card_le hEsub
    rw [hEcard, SimpleGraph.card_neighborFinset_eq_degree]
  have hxE : x ∈ E := by
    rw [hEeq, SimpleGraph.mem_neighborFinset]
    exact G.adj_symm hxy
  obtain ⟨t, ht, hxt⟩ := mem_image.1 hxE
  refine ⟨t, (mem_filter.1 ht).1, ?_⟩
  have hty := (mem_filter.1 ht).2
  simp [traversal, hxt, hty]

/-- If the departure count from the origin on `[a, b)` equals its degree and the rotor edges at
time `a` trace a path from `x` back to the origin, the departure count from `x` on `[a, b)`
also equals its degree. -/
theorem departures_eq_of_rotor_path (π : Mechanism G) (ρ : Config G) (o : V)
    (a b : ℕ) (hab : a ≤ b) (hXa : X π ρ o a = o) (hXb : X π ρ o b = o)
    (htr : Set.InjOn (traversal π ρ o) (Ico a b : Set ℕ)) (x : V)
    (hpath : Relation.ReflTransGen (fun v w => (rot π ρ o a v).1 = w) x o)
    (hdo : departures π ρ o o a b = G.degree o) :
    departures π ρ o x a b = G.degree x := by
  have hout : ∀ z : V, departures π ρ o z a b ≤ G.degree z :=
    fun z => outgoing_card_le π ρ o a b htr z
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun z _ => departures π ρ o z a b = G.degree z) hpath ?_ ?_
  · exact hdo
  · intro z y hxy _hyo ih
    have hrot : (rot π ρ o a z).1 = y := hxy
    have hxy_adj : G.Adj z y := by
      rw [← hrot]
      exact (rot π ρ o a z).2
    have hy := ih
    have hused := incoming_used π ρ o a b hab z y hXa hXb htr hy hxy_adj
    have hlow := departures_lower_of_rotor_edge π ρ o a b hab z y hrot hused
    exact le_antisymm (hout z) hlow

end Aux

-- FROZEN-STATEMENT-BEGIN
/-- FLP Lemmas 2.1 and 2.4 (`lem:one-circuit`, `external input, FLP Lemmas 2.1 and 2.4,
the statement of lem:one-circuit`), proved rather than assumed. -/
theorem oneCircuit_holds : Rotor.External.OneCircuit G
-- FROZEN-STATEMENT-END
:= by
  intro π _hG ρ o n hn
  have hmem := T_mem π ρ o n hn
  let a : ℕ := (T π ρ o n).toNat
  have ha : X π ρ o a = o := by
    simpa [a] using hmem.1
  have hvis : G.degree o * n ≤ visits π ρ o a := by
    simpa [a] using hmem.2
  have hva : visits π ρ o a = G.degree o * n := by
    simpa [a] using Aux.visits_T_eq π ρ o n hn
  constructor
  · intro s t hst hlt ht
    have has : a ≤ s := by
      simpa [a] using ENat.toNat_le_of_le_coe hst
    have hat : a ≤ t := has.trans (Nat.le_of_lt hlt)
    have htr := Aux.no_repeat π ρ o n a t hat ha hvis ht
    have hs : s ∈ Ico a (t + 1) := Finset.mem_Ico.2 ⟨has, by omega⟩
    have ht' : t ∈ Ico a (t + 1) := Finset.mem_Ico.2 ⟨hat, by omega⟩
    intro heq
    have hst' := htr hs ht' heq
    omega
  · intro hn1 x hxA
    let b : ℕ := (T π ρ o (n + 1)).toNat
    have hb : X π ρ o b = o := by
      simpa [b] using X_T π ρ o (n + 1) hn1
    have hvb : visits π ρ o b = G.degree o * (n + 1) := by
      simpa [b] using Aux.visits_T_eq π ρ o (n + 1) hn1
    have hTmono := T_mono π ρ o n
    have hab : a ≤ b := by
      have hnat := ENat.toNat_le_toNat hTmono hn1.ne
      simpa [a, b] using hnat
    have hbT : (b : ℕ∞) = T π ρ o (n + 1) := by
      dsimp [b]
      exact ENat.coe_toNat hn1.ne
    have htr := Aux.interval_inj π ρ o n a b hab ha hvis hbT hn1
    have hdo : departures π ρ o o a b = G.degree o := by
      have hv := Aux.visits_add_departures π ρ o a b hab
      rw [hva, hvb] at hv
      rw [Nat.mul_succ] at hv
      omega
    have hxR : x ∈ R π ρ o a := by
      simpa [A, a] using hxA
    obtain ⟨t, hta, hxt, hlast⟩ :=
      Aux.exists_last_visit_le π ρ o a x hxR
    have hpath := Aux.rotor_path_of_mem π ρ o a ha t x hta hxt hlast
    exact Aux.departures_eq_of_rotor_path π ρ o a b hab ha hb htr x hpath hdo

end Rotor.Bridge
