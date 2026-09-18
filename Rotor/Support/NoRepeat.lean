/-
No legal boundary routing traverses a directed edge twice: the first
assertion of `lem:boundary-routing` (`rotor.tex:747-763`).

  "If `u → v` were the first repeated directed edge, then `u ∉ S` would have
   been actuated `deg(u) + 1` times.  Legality would therefore require at
   least `deg(u) + 1` incoming traversals at `u`, counting the initial edges
   from `S`.  One of the `deg(u)` incoming directed edges would then have
   repeated earlier, a contradiction."

The `k`-th actuation of `u` traverses `(next u)^k (ρ u)`, so `deg(u) + 1`
actuations of `u` repeat an out-edge (the cyclic order has `deg u` elements);
and each actuation of `u` needs a particle, which arrived along a distinct
in-edge of `u` or sat there initially, one per in-edge from `S`.
-/
import Rotor.Support.ParticleCount

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-- Along a legal routing, the actuations of `x ∉ S` are at most its initial
particles plus its arrivals. -/
theorem count_le_of_legal (S : Finset V) (ξ : RState G) (vs : List V) (x : V) (hx : x ∉ S)
    (hleg : IsLegal π S ξ vs) : vs.count x ≤ ξ.σ x + arrivals π S ξ vs x := by
  have h := run_σ_eq π S ξ vs x hx hleg
  have h0 : (0 : ℤ) ≤ ((run π S ξ vs).σ x : ℤ) := by positivity
  omega

/-- Splitting a routing at an actuation of `v`: that actuation traverses
`v → (next v)^(c+1) (ρ v)`, where `c` is the number of earlier actuations of `v`. -/
theorem traversed_split (S : Finset V) (ξ : RState G) (l : List V) (v : V) (rest : List V) :
    traversed π S ξ (l ++ v :: rest) =
      traversed π S ξ l ++
        (v, (((π.next v) ^ (l.count v + 1)) (ξ.ρ v)).1) ::
          traversed π S (actuate π S (run π S ξ l) v) rest := by
  rw [traversed_append, traversed_cons, run_ρ, pow_succ', Equiv.Perm.mul_apply]

omit [DecidableEq V] in
/-- A cyclic permutation of a finite type: if two powers agree at a point, the
size of the type is at most their difference. -/
theorem Mechanism.card_le_of_pow_eq [G.LocallyFinite] (v : V) (x : G.neighborSet v) (a b : ℕ)
    (hab : a < b) (h : ((π.next v) ^ a) x = ((π.next v) ^ b) x) :
    G.degree v ≤ b - a := by
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

open Classical in
/-- The in-edges of `u` from `S` and from outside `S` together number `deg u`. -/
theorem degree_eq_card_add [G.LocallyFinite] (S : Finset V) (u : V) :
    G.degree u = (S.filter (fun s => G.Adj s u)).card +
      ((G.neighborFinset u).filter (fun t => t ∉ S)).card := by
  have h1 : S.filter (fun s => G.Adj s u) = (G.neighborFinset u).filter (fun t => t ∈ S) := by
    ext t
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hS, hadj⟩; exact ⟨G.adj_symm hadj, hS⟩
    · rintro ⟨hadj, hS⟩; exact ⟨hS, G.adj_symm hadj⟩
  rw [h1, ← SimpleGraph.card_neighborFinset_eq_degree]
  exact (Finset.card_filter_add_card_filter_not _).symm

end Rotor

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-- Every actuated vertex of a legal routing lies outside `S`. -/
theorem IsLegal.not_mem_sink (S : Finset V) (ξ : RState G) (vs : List V)
    (h : IsLegal π S ξ vs) : ∀ v ∈ vs, v ∉ S := by
  induction vs generalizing ξ with
  | nil => simp
  | cons v vs ih =>
    rw [isLegal_cons] at h
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact h.1
    · exact ih _ h.2.2 w hw

/-- The tail of a traversed edge is an actuated vertex. -/
theorem fst_mem_of_mem_traversed (S : Finset V) (ξ : RState G) (vs : List V) (e : V × V)
    (he : e ∈ traversed π S ξ vs) : e.1 ∈ vs := by
  have := List.mem_map_of_mem (f := Prod.fst) he
  rwa [traversed_map_fst] at this

/-- A traversed edge joins adjacent vertices. -/
theorem adj_of_mem_traversed (S : Finset V) (ξ : RState G) (vs : List V) (e : V × V)
    (he : e ∈ traversed π S ξ vs) : G.Adj e.1 e.2 := by
  induction vs generalizing ξ with
  | nil => simp at he
  | cons v vs ih =>
    rw [traversed_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact (π.next v (ξ.ρ v)).2
    · exact ih _ he

/-- A traversed edge `e` arises at some actuation of its tail: splitting the
routing there, `e` is the tail together with the rotor advanced `c + 1` times,
`c` being the number of earlier actuations of the tail. -/
theorem exists_split_of_mem_traversed (S : Finset V) (ξ : RState G) (vs : List V) (e : V × V)
    (he : e ∈ traversed π S ξ vs) :
    ∃ l₁ l₂ : List V, vs = l₁ ++ e.1 :: l₂ ∧
      e.2 = (((π.next e.1) ^ (l₁.count e.1 + 1)) (ξ.ρ e.1)).1 := by
  induction vs generalizing ξ with
  | nil => simp at he
  | cons v vs ih =>
    rw [traversed_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨[], vs, by simp, by simp⟩
    · obtain ⟨l₁, l₂, h1, h2⟩ := ih _ he
      refine ⟨v :: l₁, l₂, by simp [h1], ?_⟩
      rw [h2]
      by_cases hv : v = e.1
      · subst hv
        rw [List.count_cons_self, actuate_ρ_self, ← Equiv.Perm.mul_apply, ← pow_succ]
      · rw [List.count_cons_of_ne hv, actuate_ρ_of_ne π S ξ v e.1 (Ne.symm hv)]

end Rotor

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

open Classical in
/-- The edges of a duplicate-free list of edges with head `u`, all of the form
`t → u` with `t ∉ S` adjacent to `u`, number at most the in-edges of `u` from
outside `S`. -/
theorem countP_head_le [G.LocallyFinite] (S : Finset V) (L : List (V × V)) (hL : L.Nodup)
    (u : V) (hadj : ∀ e ∈ L, G.Adj e.1 e.2) (hS : ∀ e ∈ L, e.1 ∉ S) :
    L.countP (fun e => e.2 = u) ≤ ((G.neighborFinset u).filter (fun t => t ∉ S)).card := by
  rw [List.countP_eq_length_filter]
  have hsub : ∀ t ∈ (L.filter (fun e => decide (e.2 = u))).map Prod.fst,
      t ∈ (G.neighborFinset u).filter (fun t => t ∉ S) := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    rw [List.mem_filter, decide_eq_true_eq] at he
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨G.adj_symm (he.2 ▸ hadj e he.1), hS e he.1⟩
  have hnd : ((L.filter (fun e => decide (e.2 = u))).map Prod.fst).Nodup := by
    refine List.Nodup.map_on ?_ (hL.filter _)
    intro e₁ he₁ e₂ he₂ h
    rw [List.mem_filter, decide_eq_true_eq] at he₁ he₂
    exact Prod.ext h (he₁.2.trans he₂.2.symm)
  calc (L.filter (fun e => decide (e.2 = u))).length
      = ((L.filter (fun e => decide (e.2 = u))).map Prod.fst).length := (List.length_map _).symm
    _ = ((L.filter (fun e => decide (e.2 = u))).map Prod.fst).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ _ := Finset.card_le_card (fun t ht => hsub t (List.mem_toFinset.1 ht))

/-- No legal boundary routing traverses a directed edge twice (the first
assertion of `lem:boundary-routing`, without the initial edges). -/
theorem traversed_nodup [G.LocallyFinite] (S : Finset V) (ρ : Config G) (vs : List V)
    (hleg : IsLegal π S (boundaryInit S ρ) vs) :
    (traversed π S (boundaryInit S ρ) vs).Nodup := by
  classical
  induction vs using List.reverseRecOn with
  | nil => simp
  | append_singleton l v ih =>
    have hl : IsLegal π S (boundaryInit S ρ) l := ((isLegal_append π S _ l [v]).1 hleg).1
    have ihl := ih hl
    rw [traversed_append, traversed_cons, traversed_nil, List.nodup_append]
    refine ⟨ihl, List.nodup_singleton _, ?_⟩
    intro e he b hb heq
    rw [List.mem_singleton] at hb
    rw [heq, hb] at he
    set ξ₀ := boundaryInit S ρ with hξ₀
    obtain ⟨l₁, l₂, hsplit, he2⟩ := exists_split_of_mem_traversed π S ξ₀ l _ he
    simp only at hsplit he2
    have hv_not : v ∉ S := IsLegal.not_mem_sink π S ξ₀ (l ++ [v]) hleg v (by simp)
    have hcount_l : l.count v = l₁.count v + 1 + l₂.count v := by
      rw [hsplit, List.count_append, List.count_cons_self]; omega
    have h1 : (π.next v ((run π S ξ₀ l).ρ v)).1 = (((π.next v) ^ (l.count v + 1)) (ξ₀.ρ v)).1 := by
      rw [run_ρ, ← Equiv.Perm.mul_apply, ← pow_succ']
    have hpow : ((π.next v) ^ (l₁.count v + 1)) (ξ₀.ρ v) = ((π.next v) ^ (l.count v + 1)) (ξ₀.ρ v) :=
      Subtype.ext (he2.symm.trans h1)
    have hdeg : G.degree v ≤ (l.count v + 1) - (l₁.count v + 1) :=
      Mechanism.card_le_of_pow_eq π v (ξ₀.ρ v) _ _ (by omega) hpow
    have hle := count_le_of_legal π S ξ₀ (l ++ [v]) v hv_not hleg
    have hlast : (traversed π S (run π S ξ₀ l) [v]).countP (fun e => decide (e.2 = v)) = 0 := by
      simp only [traversed_cons, traversed_nil, List.countP_cons, List.countP_nil, zero_add]
      simp [next_head_ne π (run π S ξ₀ l) v]
    have harr : arrivals π S ξ₀ (l ++ [v]) v ≤ ((G.neighborFinset v).filter (fun t => t ∉ S)).card := by
      unfold arrivals
      rw [traversed_append, List.countP_append, hlast, add_zero]
      exact countP_head_le S _ ihl v (adj_of_mem_traversed π S ξ₀ l)
        (fun e he => IsLegal.not_mem_sink π S ξ₀ l hl e.1 (fst_mem_of_mem_traversed π S ξ₀ l e he))
    have hinit : ξ₀.σ v = (S.filter (fun s => G.Adj s v)).card := by
      simp [hξ₀, boundaryInit, hv_not]
    have hdeg' := degree_eq_card_add (G := G) S v
    have hcount : (l ++ [v]).count v = l.count v + 1 := by simp [List.count_append]
    omega

/-- The first assertion of `lem:boundary-routing`: no legal boundary routing
traverses a directed edge twice, counting the initial edges from `S`. -/
theorem boundaryTraversed_nodup [G.LocallyFinite] (S : Finset V) (ρ : Config G)
    (es : List (V × V)) (vs : List V) (hes : IsBoundaryOrder G S es)
    (hleg : IsLegal π S (boundaryInit S ρ) vs) :
    (boundaryTraversed π S ρ es vs).Nodup := by
  unfold boundaryTraversed
  rw [List.nodup_append]
  refine ⟨hes.1, traversed_nodup π S ρ vs hleg, ?_⟩
  intro e he e' he' heq
  subst heq
  have h1 : e.1 ∈ S := ((hes.2 e).1 he).1
  have h2 : e.1 ∉ S :=
    IsLegal.not_mem_sink π S _ vs hleg e.1 (fst_mem_of_mem_traversed π S _ vs e he')
  exact h2 h1

end Rotor
