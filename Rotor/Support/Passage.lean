/-
The passage time, `prop:passage` (`rotor.tex:833-873`).

  "Every vertex of `∂S` initially carries a particle and is therefore actuated
   in a complete routing, so `S ∪ ∂S ⊆ Φ(S)`.  Iterating this inclusion along
   a shortest path from `x` to `y` proves `τ(x,y) ≤ d_G(x,y)`.  Set `m := τ(x,y)`
   and `k := τ(y,z)`.  Since `{y} ⊆ Φ^m({x})`, monotonicity gives
   `Φ^k({y}) ⊆ Φ^k(Φ^m({x})) = Φ^{m+k}({x})`.  The left-hand side contains `z`,
   proving the triangle inequality.  Finally, Proposition circuit-iterate gives
   `A_n = Φ^n({o})`, and the definition of `τ` gives the passage-ball identity."
-/
import Rotor.Support.CircuitIterate

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-! ### The boundary of `S` lies in `Φ(S)` -/

/-- A vertex outside `S` that carries a particle initially is actuated in
every complete boundary routing: otherwise its particles never leave. -/
theorem mem_of_complete_of_init_pos (S : Finset V) (ρ : Config G) (ws : List V)
    (hws : IsComplete π S (boundaryInit S ρ) ws) (y : V) (hy : y ∉ S)
    (hpos : 0 < (boundaryInit S ρ).σ y) : y ∈ ws := by
  by_contra hcon
  have hcount : ws.count y = 0 := List.count_eq_zero.2 hcon
  have hge := run_σ_add_count_ge π S (boundaryInit S ρ) ws y hy
  have hstab := hws.2 y hy
  omega

open Classical in
/-- `S ∪ ∂S ⊆ Φ(S)` when the boundary routing of `S` terminates. -/
theorem mem_Φ_of_adj (ρ : Config G) (S : Finset V) (hT : Terminates π S ρ) (s y : V)
    (hs : s ∈ S) (hadj : G.Adj s y) : y ∈ Φ π ρ S := by
  by_cases hy : y ∈ S
  · exact subset_Φ π ρ S hy
  rw [Φ_of_terminates π ρ S hT, Finset.mem_union, List.mem_toFinset]
  right
  refine mem_of_complete_of_init_pos π S ρ _ (Classical.choose_spec hT) y hy ?_
  simp only [boundaryInit, hy, if_false]
  exact Finset.card_pos.2 ⟨s, Finset.mem_filter.2 ⟨hs, hadj⟩⟩

/-! ### Iterates of `Φ` -/

theorem subset_Φ_iterate (ρ : Config G) (S : Finset V) (n : ℕ) : S ⊆ (Φ π ρ)^[n] S := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.trans (subset_Φ π ρ _)

theorem Φ_iterate_mono_index (ρ : Config G) (S : Finset V) {m n : ℕ} (h : m ≤ n) :
    (Φ π ρ)^[m] S ⊆ (Φ π ρ)^[n] S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, Function.iterate_add_apply]
  exact subset_Φ_iterate π ρ _ k

theorem nonempty_Φ_iterate (ρ : Config G) (S : Finset V) (hS : S.Nonempty) (n : ℕ) :
    ((Φ π ρ)^[n] S).Nonempty := hS.mono (subset_Φ_iterate π ρ S n)

/-- Under `AllTerminate`, the iterates of `Φ` are monotone in the set. -/
theorem Φ_iterate_mono (hAb : External.Abelian G) [Infinite V] [G.LocallyFinite]
    (hG : G.Connected) (ρ : Config G) (hall : AllTerminate π ρ) (S U : Finset V)
    (hS : S.Nonempty) (hSU : S ⊆ U) (k : ℕ) : (Φ π ρ)^[k] S ⊆ (Φ π ρ)^[k] U := by
  induction k with
  | zero => exact hSU
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Φ_mono π hAb hG ρ _ _ (nonempty_Φ_iterate π ρ S hS k) ih
      (hall _ (nonempty_Φ_iterate π ρ U (hS.mono hSU) k))

/-! ### The passage time -/

theorem τ_of_allTerminate (ρ : Config G) (h : AllTerminate π ρ) (x y : V) :
    τ π ρ x y = sInf {n : ℕ | y ∈ (Φ π ρ)^[n] {x}} := by
  simp [τ, h]

theorem τ_of_not_allTerminate (ρ : Config G) (h : ¬ AllTerminate π ρ) (x y : V) :
    τ π ρ x y = G.dist x y := by
  simp [τ, h]

/-- Along a shortest path, the `k`-th vertex lies in `Φ^k({x})`. -/
theorem getVert_mem_iterate (ρ : Config G) (hall : AllTerminate π ρ) {x y : V} (p : G.Walk x y)
    (k : ℕ) (hk : k ≤ p.length) : p.getVert k ∈ (Φ π ρ)^[k] {x} := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hk' : k < p.length := hk
    exact mem_Φ_of_adj π ρ _ (hall _ (nonempty_Φ_iterate π ρ {x} (by simp) k)) _ _
      (ih hk'.le) (p.adj_getVert_succ hk')

/-- `y ∈ Φ^{d(x,y)}({x})`, so the passage set is nonempty. -/
theorem mem_iterate_dist (hG : G.Connected) (ρ : Config G) (hall : AllTerminate π ρ) (x y : V) :
    y ∈ (Φ π ρ)^[G.dist x y] {x} := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
  have := getVert_mem_iterate π ρ hall p p.length le_rfl
  rwa [p.getVert_length, hp] at this

theorem τ_le_dist (hG : G.Connected) (ρ : Config G) (x y : V) : τ π ρ x y ≤ G.dist x y := by
  by_cases hall : AllTerminate π ρ
  · rw [τ_of_allTerminate π ρ hall]
    exact Nat.sInf_le (mem_iterate_dist π hG ρ hall x y)
  · rw [τ_of_not_allTerminate π ρ hall]

theorem mem_iterate_τ (hG : G.Connected) (ρ : Config G) (hall : AllTerminate π ρ) (x y : V) :
    y ∈ (Φ π ρ)^[τ π ρ x y] {x} := by
  rw [τ_of_allTerminate π ρ hall]
  exact Nat.sInf_mem (s := {n : ℕ | y ∈ (Φ π ρ)^[n] {x}})
    ⟨G.dist x y, mem_iterate_dist π hG ρ hall x y⟩

theorem τ_triangle (hAb : External.Abelian G) [Infinite V] [G.LocallyFinite] (hG : G.Connected)
    (ρ : Config G) (x y z : V) : τ π ρ x z ≤ τ π ρ x y + τ π ρ y z := by
  by_cases hall : AllTerminate π ρ
  · have hy := mem_iterate_τ π hG ρ hall x y
    have hz := mem_iterate_τ π hG ρ hall y z
    have hsub : (Φ π ρ)^[τ π ρ y z] {y} ⊆ (Φ π ρ)^[τ π ρ y z] ((Φ π ρ)^[τ π ρ x y] {x}) :=
      Φ_iterate_mono π hAb hG ρ hall _ _ (by simp) (by simpa using hy) _
    rw [← Function.iterate_add_apply, add_comm] at hsub
    rw [τ_of_allTerminate π ρ hall x z]
    exact Nat.sInf_le (hsub hz)
  · simp only [τ_of_not_allTerminate π ρ hall]
    exact hG.dist_triangle

/-! ### The passage balls -/

theorem T_zero' [G.LocallyFinite] (ρ : Config G) (o : V) : T π ρ o 0 = 0 := by
  refine le_antisymm ?_ (zero_le _)
  have h : (0 : ℕ) ∈ circuitSet π ρ o 0 := ⟨rfl, by simp⟩
  have := T_le_of_mem π ρ o 0 h
  simpa using this

theorem A_zero' [G.LocallyFinite] (ρ : Config G) (o : V) : A π ρ o 0 = {o} := by
  rw [A, T_zero']
  simp [R]

/-- Under `AllTerminate`, every circuit ends and `A_n = Φ^n({o})`. -/
theorem T_lt_and_A_eq [G.LocallyFinite] (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    [Infinite V] (hG : G.Connected) (ρ : Config G) (o : V) (hall : AllTerminate π ρ)
    (n : ℕ) : T π ρ o n < ⊤ ∧ A π ρ o n = (Φ π ρ)^[n] {o} := by
  induction n with
  | zero => exact ⟨by rw [T_zero']; exact WithTop.coe_lt_top _, A_zero' π ρ o⟩
  | succ n ih =>
    have hT : T π ρ o (n + 1) < ⊤ :=
      T_lt_of_terminates π ρ o hFLP hAb hG n ih.1 (hall _ ⟨o, o_mem_A π ρ o n⟩)
    refine ⟨hT, ?_⟩
    rw [A_succ_eq_Φ π ρ o hFLP hAb hG n ih.1 hT, ih.2, Function.iterate_succ_apply']

/-- `prop:passage`. -/
theorem passage_proof [G.LocallyFinite] (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    [Infinite V] (hG : G.Connected) (ρ : Config G) (o : V) :
    (∀ x y z : V, τ π ρ x z ≤ τ π ρ x y + τ π ρ y z) ∧
    (∀ x y : V, τ π ρ x y ≤ G.dist x y) ∧
    (AllTerminate π ρ → ∀ n : ℕ, T π ρ o n < ⊤ ∧ ∀ x : V, x ∈ A π ρ o n ↔ τ π ρ o x ≤ n) := by
  refine ⟨τ_triangle π hAb hG ρ, τ_le_dist π hG ρ, fun hall n => ?_⟩
  obtain ⟨hT, hA⟩ := T_lt_and_A_eq π hFLP hAb hG ρ o hall n
  refine ⟨hT, fun x => ?_⟩
  rw [hA]
  constructor
  · intro hx
    rw [τ_of_allTerminate π ρ hall]
    exact Nat.sInf_le hx
  · intro hle
    exact Φ_iterate_mono_index π ρ {o} hle (mem_iterate_τ π hG ρ hall o x)

end Rotor
