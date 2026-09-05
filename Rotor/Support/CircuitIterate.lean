/-
The bridge between the walk and the routings: `prop:circuit-iterate`
(`rotor.tex:774-799`).

  "Starting at time `T(n)`, delete the actuations in `A_n` and regard the
   traversals leaving `A_n` as initial boundary edges.  This gives a legal
   boundary routing.  If the boundary routing of `A_n` terminates, Lemma
   boundary-routing bounds the number of outside actuations.  Before time
   `T(n+1)` the walk departs from each vertex `x` at most `deg(x)` times by
   Lemma one-circuit, so the actuations inside the finite set `A_n` are
   finitely many as well.  Hence `T(n+1) < ∞`.  Conversely, if `T(n+1) < ∞`,
   the walk uses every directed edge leaving `A_n` once between `T(n)` and
   `T(n+1)`, so the routing is complete.  The abelian property gives
   `A_{n+1} = Φ(A_n)`."

The invariant: after the walk's outside actuations up to time `t`, the
routing state has the walk's rotors outside `A_n`, and its particles outside
`A_n` are the boundary edges not yet crossed plus the walker itself.
-/
import Rotor.Support.Monotone
import Rotor.Support.WalkBasics
import Rotor.External.OneCircuit

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G) (ρ : Config G) (o : V)

/-- The walk's positions outside `S` during `[t₀, t)`, in time order: the
outside actuations. -/
def outs (S : Finset V) (t₀ t : ℕ) : List V :=
  ((List.range' t₀ (t - t₀)).filter (fun s => decide (X π ρ o s ∉ S))).map (X π ρ o)

/-- The crossings from `S` into `x` during `[t₀, t)`. -/
def crossings (S : Finset V) (t₀ t : ℕ) (x : V) : ℕ :=
  ((Finset.Ico t₀ t).filter (fun s => X π ρ o s ∈ S ∧ X π ρ o (s + 1) = x)).card

variable (G) in
open Classical in
/-- The in-edges of `x` from `S`. -/
noncomputable def inEdges (S : Finset V) (x : V) : ℕ := (S.filter (fun s => G.Adj s x)).card

theorem outs_self (S : Finset V) (t₀ : ℕ) : outs π ρ o S t₀ t₀ = [] := by
  simp [outs]

theorem outs_succ (S : Finset V) (t₀ t : ℕ) (h : t₀ ≤ t) :
    outs π ρ o S t₀ (t + 1) =
      outs π ρ o S t₀ t ++ (if X π ρ o t ∈ S then [] else [X π ρ o t]) := by
  unfold outs
  rw [show t + 1 - t₀ = (t - t₀) + 1 by omega, List.range'_concat, List.filter_append, List.map_append]
  congr 1
  rw [show t₀ + 1 * (t - t₀) = t by omega]
  split_ifs with hS <;> simp [hS]

theorem crossings_succ (S : Finset V) (t₀ t : ℕ) (h : t₀ ≤ t) (x : V) :
    crossings π ρ o S t₀ (t + 1) x =
      crossings π ρ o S t₀ t x + (if X π ρ o t ∈ S ∧ X π ρ o (t + 1) = x then 1 else 0) := by
  unfold crossings
  have hI : Finset.Ico t₀ (t + 1) = insert t (Finset.Ico t₀ t) := by
    ext s; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [hI, Finset.filter_insert]
  split_ifs with hc
  · rw [Finset.card_insert_of_notMem]
    simp
  · rfl

/-- The invariant of the bridge at time `t`, for the sink set `S` and the
start time `t₀`: the routing of the outside actuations has the walk's rotors
outside `S`, its particles outside `S` are the uncrossed boundary edges plus
the walker, and it is legal. -/
structure WalkInv (S : Finset V) (t₀ t : ℕ) : Prop where
  rotor : ∀ x, x ∉ S → (run π S (boundaryInit S ρ) (outs π ρ o S t₀ t)).ρ x = rot π ρ o t x
  count : ∀ x, x ∉ S →
    (run π S (boundaryInit S ρ) (outs π ρ o S t₀ t)).σ x + crossings π ρ o S t₀ t x =
      inEdges G S x + (if X π ρ o t = x then 1 else 0)
  legal : IsLegal π S (boundaryInit S ρ) (outs π ρ o S t₀ t)

/-- The invariant holds at the start time when `S` is the range at that time
and the walker sits in `S`. -/
theorem walkInv_init (t₀ : ℕ) : WalkInv π ρ o (R π ρ o t₀) t₀ t₀ where
  rotor x hx := by
    rw [outs_self, run_nil, rot_eq_of_not_mem_R π ρ o t₀ x hx]; rfl
  count x hx := by
    classical
    have h0 : X π ρ o t₀ ≠ x := fun h => hx (h ▸ X_mem_R π ρ o t₀ t₀ le_rfl)
    simp [outs_self, crossings, boundaryInit, inEdges, hx, h0]
  legal := by rw [outs_self]; trivial

/-- One step of the walk preserves the invariant, provided the crossings into
the walker's vertex do not exceed its in-edges (which `lem:one-circuit`
guarantees before `T(n+1)`). -/
theorem walkInv_step (S : Finset V) (t₀ t : ℕ) (ht : t₀ ≤ t) (h : WalkInv π ρ o S t₀ t)
    (hb : X π ρ o t ∉ S → crossings π ρ o S t₀ t (X π ρ o t) ≤ inEdges G S (X π ρ o t)) :
    WalkInv π ρ o S t₀ (t + 1) := by
  obtain ⟨hrot, hcount, hleg⟩ := h
  by_cases hXt : X π ρ o t ∈ S
  · -- the walker is inside `S`: no actuation, possibly a crossing
    have ho : outs π ρ o S t₀ (t + 1) = outs π ρ o S t₀ t := by
      rw [outs_succ π ρ o S t₀ t ht]; simp [hXt]
    refine ⟨fun x hx => ?_, fun x hx => ?_, by rw [ho]; exact hleg⟩
    · rw [ho, hrot x hx, rot_succ, Function.update_of_ne (fun h => hx (by rw [h]; exact hXt))]
    · rw [ho, crossings_succ π ρ o S t₀ t ht]
      have h0 : X π ρ o t ≠ x := fun h => hx (h ▸ hXt)
      have := hcount x hx
      simp only [hXt, true_and, h0, if_false, add_zero] at this ⊢
      omega
  · -- the walker is outside `S`: it actuates its vertex
    have ho : outs π ρ o S t₀ (t + 1) = outs π ρ o S t₀ t ++ [X π ρ o t] := by
      rw [outs_succ π ρ o S t₀ t ht, if_neg hXt]
    set ξ := run π S (boundaryInit S ρ) (outs π ρ o S t₀ t) with hξ
    have hhead : (π.next (X π ρ o t) (ξ.ρ (X π ρ o t))).1 = X π ρ o (t + 1) := by
      rw [X_succ, hrot _ hXt]
    have hσv : 0 < ξ.σ (X π ρ o t) := by
      have := hcount _ hXt
      have hb' := hb hXt
      simp only [if_true] at this
      omega
    refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
    · rw [ho, run_append, run_cons, run_nil, ← hξ, rot_succ]
      by_cases hxv : x = X π ρ o t
      · rw [hxv, actuate_ρ_self, Function.update_self, hrot _ hXt]
      · rw [actuate_ρ_of_ne π S ξ _ x hxv, Function.update_of_ne hxv, hrot x hx]
    · rw [ho, run_append, run_cons, run_nil, ← hξ, actuate_σ, hhead,
        crossings_succ π ρ o S t₀ t ht]
      simp only [hXt, false_and, if_false, add_zero]
      have hc := hcount x hx
      by_cases hxv : x = X π ρ o t
      · rw [hxv] at hc ⊢
        simp only [if_true] at hc ⊢
        have hne : X π ρ o (t + 1) ≠ X π ρ o t := by
          rw [← hhead]; exact next_head_ne π ξ _
        simp only [hne, if_false, add_zero, hne.symm, false_and]
        omega
      · have hxv' : X π ρ o t ≠ x := Ne.symm hxv
        simp only [hxv, hxv', if_false, add_zero] at hc ⊢
        by_cases hh : X π ρ o (t + 1) = x
        · simp only [hh, hx, not_false_eq_true, and_self, if_true]
          omega
        · have hh' : ¬ (x = X π ρ o (t + 1) ∧ X π ρ o (t + 1) ∉ S) := fun h => hh h.1.symm
          simp only [hh, hh', if_false, add_zero]
          omega
    · rw [ho, isLegal_append]
      exact ⟨hleg, hXt, hσv, trivial⟩

/-! ### The crossing bound from `lem:one-circuit` -/

section
variable [G.LocallyFinite]

/-- `T n` as a natural number, when finite. -/
theorem coe_toNat_T (n : ℕ) (hn : T π ρ o n < ⊤) : ((T π ρ o n).toNat : ℕ∞) = T π ρ o n :=
  ENat.coe_toNat hn.ne

/-- Before `T(n+1)`, the crossings from `A_n` into `x` never exceed the in-edges
of `x` from `A_n`: distinct crossing times give distinct traversals
(`lem:one-circuit` (i)) with the same head, hence distinct tails. -/
theorem crossings_le (hFLP : External.OneCircuit G) (hG : G.Connected) (n : ℕ)
    (hn : T π ρ o n < ⊤) (t : ℕ) (ht : (t : ℕ∞) ≤ T π ρ o (n + 1)) (x : V) :
    crossings π ρ o (A π ρ o n) (T π ρ o n).toNat t x ≤ inEdges G (A π ρ o n) x := by
  classical
  unfold crossings inEdges
  refine Finset.card_le_card_of_injOn (fun s => X π ρ o s) ?_ ?_
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hs
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨hs.2.1, hs.2.2 ▸ adj_X_succ π ρ o s⟩
  · intro s hs s' hs' heq
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hs hs'
    by_contra hne
    have key : ∀ a b : ℕ, a < b → (T π ρ o n).toNat ≤ a → b < t →
        X π ρ o a = X π ρ o b → X π ρ o (a + 1) = x → X π ρ o (b + 1) = x → False := by
      intro a b hab ha hb hXab hXa hXb
      have h1 : T π ρ o n ≤ (a : ℕ∞) := by
        rw [← coe_toNat_T π ρ o n hn]; exact_mod_cast ha
      have h2 : (b : ℕ∞) < T π ρ o (n + 1) := lt_of_lt_of_le (by exact_mod_cast hb) ht
      exact (hFLP π hG ρ o n hn).1 a b h1 hab h2 (by simp [traversal, hXab, hXa, hXb])
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact key s s' hlt hs.1.1 hs'.1.2 heq hs.2.2 hs'.2.2
    · exact key s' s hlt hs'.1.1 hs.1.2 heq.symm hs'.2.2 hs.2.2

/-- The invariant holds at every time of `[T(n), T(n+1)]`. -/
theorem walkInv_all (hFLP : External.OneCircuit G) (hG : G.Connected) (n : ℕ)
    (hn : T π ρ o n < ⊤) (t : ℕ) (ht₀ : (T π ρ o n).toNat ≤ t)
    (ht : (t : ℕ∞) ≤ T π ρ o (n + 1)) :
    WalkInv π ρ o (A π ρ o n) (T π ρ o n).toNat t := by
  induction t, ht₀ using Nat.le_induction with
  | base => exact walkInv_init π ρ o _
  | succ t ht₀ ih =>
    have ht' : (t : ℕ∞) ≤ T π ρ o (n + 1) :=
      le_trans (by exact_mod_cast Nat.le_succ t) ht
    exact walkInv_step π ρ o _ _ t ht₀ (ih ht') (fun _ => crossings_le π ρ o hFLP hG n hn t ht' _)

/-! ### The forward direction: `T(n+1) < ∞` makes the routing complete -/

/-- When `T(n+1) < ∞`, every in-edge of `x ∉ A_n` from `A_n` is crossed during
the circuit: each `s₀ ∈ A_n` departs `deg s₀` times along distinct edges
(`lem:one-circuit`), hence along every edge out of `s₀`. -/
theorem inEdges_le_crossings (hFLP : External.OneCircuit G) (hG : G.Connected) (n : ℕ)
    (hn : T π ρ o n < ⊤) (hn1 : T π ρ o (n + 1) < ⊤) (x : V) :
    inEdges G (A π ρ o n) x ≤
      crossings π ρ o (A π ρ o n) (T π ρ o n).toNat (T π ρ o (n + 1)).toNat x := by
  classical
  unfold inEdges crossings
  refine Finset.card_le_card_of_surjOn (fun s => X π ρ o s) ?_
  intro s₀ hs₀
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs₀
  obtain ⟨hs₀S, hadj⟩ := hs₀
  have hdep := (hFLP π hG ρ o n hn).2 hn1 s₀ hs₀S
  unfold departures at hdep
  have hmaps : ∀ s ∈ (Finset.Ico (T π ρ o n).toNat (T π ρ o (n + 1)).toNat).filter
      (fun s => X π ρ o s = s₀), X π ρ o (s + 1) ∈ G.neighborFinset s₀ := by
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [SimpleGraph.mem_neighborFinset, ← hs.2]
    exact adj_X_succ π ρ o s
  have key : ∀ a b : ℕ, a < b → (T π ρ o n).toNat ≤ a → b < (T π ρ o (n + 1)).toNat →
      X π ρ o a = s₀ → X π ρ o b = s₀ → X π ρ o (a + 1) = X π ρ o (b + 1) → False := by
    intro a b hab ha hb hXa hXb hX
    have h1 : T π ρ o n ≤ (a : ℕ∞) := by
      rw [← coe_toNat_T π ρ o n hn]; exact_mod_cast ha
    have h2 : (b : ℕ∞) < T π ρ o (n + 1) := by
      rw [← coe_toNat_T π ρ o (n + 1) hn1]; exact_mod_cast hb
    exact (hFLP π hG ρ o n hn).1 a b h1 hab h2 (by simp [traversal, hXa, hXb, hX])
  have hinj : ∀ a ∈ (Finset.Ico (T π ρ o n).toNat (T π ρ o (n + 1)).toNat).filter
      (fun s => X π ρ o s = s₀), ∀ b ∈ (Finset.Ico (T π ρ o n).toNat (T π ρ o (n + 1)).toNat).filter
      (fun s => X π ρ o s = s₀), X π ρ o (a + 1) = X π ρ o (b + 1) → a = b := by
    intro a ha b hb hab
    rw [Finset.mem_filter, Finset.mem_Ico] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key a b h ha.1.1 hb.1.2 ha.2 hb.2 hab
    · exact key b a h hb.1.1 ha.1.2 hb.2 ha.2 hab.symm
  have hcard : (G.neighborFinset s₀).card ≤
      ((Finset.Ico (T π ρ o n).toNat (T π ρ o (n + 1)).toNat).filter
        (fun s => X π ρ o s = s₀)).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdep]
  obtain ⟨s, hs, hsx⟩ := Finset.surj_on_of_inj_on_of_card_le (fun s _ => X π ρ o (s + 1)) hmaps
    (fun a b ha hb h => hinj a ha b hb h) hcard x
    (by rw [SimpleGraph.mem_neighborFinset]; exact hadj)
  rw [Finset.mem_filter] at hs
  refine ⟨s, ?_, hs.2⟩
  simp only [Finset.coe_filter, Set.mem_setOf_eq]
  exact ⟨hs.1, hs.2 ▸ hs₀S, hsx.symm⟩

theorem toNat_T_le (n : ℕ) (hn1 : T π ρ o (n + 1) < ⊤) :
    (T π ρ o n).toNat ≤ (T π ρ o (n + 1)).toNat :=
  ENat.toNat_le_toNat (T_mono π ρ o n) hn1.ne

theorem o_mem_A (n : ℕ) : o ∈ A π ρ o n := X_mem_R π ρ o 0 _ (Nat.zero_le _)

/-- When `T(n+1) < ∞`, the outside actuations of the circuit form a complete
boundary routing of `A_n`. -/
theorem complete_of_T_lt (hFLP : External.OneCircuit G) (hG : G.Connected) (n : ℕ)
    (hn : T π ρ o n < ⊤) (hn1 : T π ρ o (n + 1) < ⊤) :
    IsComplete π (A π ρ o n) (boundaryInit (A π ρ o n) ρ)
      (outs π ρ o (A π ρ o n) (T π ρ o n).toNat (T π ρ o (n + 1)).toNat) := by
  have ht₀ := toNat_T_le π ρ o n hn1
  have ht₁ : (((T π ρ o (n + 1)).toNat : ℕ) : ℕ∞) ≤ T π ρ o (n + 1) := by
    rw [coe_toNat_T π ρ o (n + 1) hn1]
  have hinv := walkInv_all π ρ o hFLP hG n hn _ ht₀ ht₁
  refine ⟨hinv.legal, fun x hx => ?_⟩
  have hc := hinv.count x hx
  have hle := crossings_le π ρ o hFLP hG n hn _ ht₁ x
  have hge := inEdges_le_crossings π ρ o hFLP hG n hn hn1 x
  have hne : X π ρ o (T π ρ o (n + 1)).toNat ≠ x := by
    rw [X_T π ρ o (n + 1) hn1]; exact fun h => hx (h ▸ o_mem_A π ρ o n)
  simp only [hne, if_false, add_zero] at hc
  omega

theorem terminates_of_T_lt (hFLP : External.OneCircuit G) (hG : G.Connected) (n : ℕ)
    (hn : T π ρ o n < ⊤) (hn1 : T π ρ o (n + 1) < ⊤) : Terminates π (A π ρ o n) ρ :=
  ⟨_, complete_of_T_lt π ρ o hFLP hG n hn hn1⟩

/-! ### The range after the circuit -/

omit [G.LocallyFinite] in
theorem R_eq_union_outs (t₀ t : ℕ) (ht : t₀ ≤ t) :
    R π ρ o t = R π ρ o t₀ ∪ (outs π ρ o (R π ρ o t₀) t₀ t).toFinset ∪ {X π ρ o t} := by
  induction t, ht using Nat.le_induction with
  | base =>
    rw [outs_self]
    have : X π ρ o t₀ ∈ R π ρ o t₀ := X_mem_R π ρ o t₀ t₀ le_rfl
    ext y; simp only [Finset.mem_union, List.toFinset_nil, Finset.notMem_empty, or_false,
      Finset.mem_singleton]
    constructor
    · exact Or.inl
    · rintro (h | rfl) <;> [exact h; exact this]
  | succ t ht ih =>
    rw [R_succ, ih, outs_succ π ρ o _ t₀ t ht]
    ext y
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, List.toFinset_append,
      List.mem_toFinset]
    by_cases hXt : X π ρ o t ∈ R π ρ o t₀
    · simp only [hXt, if_true, List.not_mem_nil]
      constructor
      · rintro (rfl | (h | h) | rfl)
        · exact Or.inr rfl
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inl hXt)
      · rintro ((h | (h | h)) | rfl)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl (Or.inr h))
        · exact h.elim
        · exact Or.inl rfl
    · simp only [hXt, if_false, List.mem_singleton]
      constructor
      · rintro (rfl | (h | h) | rfl)
        · exact Or.inr rfl
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr rfl))
      · rintro ((h | (h | rfl)) | rfl)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl (Or.inr h))
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl

/-- `A_{n+1} = Φ(A_n)` when `T(n+1) < ∞`: the range at `T(n+1)` is `A_n` plus
the outside actuations, and those are the actuations of every complete
boundary routing of `A_n` (abelian property). -/
theorem A_succ_eq_Φ (hFLP : External.OneCircuit G) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (n : ℕ) (hn : T π ρ o n < ⊤) (hn1 : T π ρ o (n + 1) < ⊤) :
    A π ρ o (n + 1) = Φ π ρ (A π ρ o n) := by
  have hcomp := complete_of_T_lt π ρ o hFLP hG n hn hn1
  have hT : Terminates π (A π ρ o n) ρ := ⟨_, hcomp⟩
  have hS : (A π ρ o n).Nonempty := ⟨o, o_mem_A π ρ o n⟩
  have hR : R π ρ o (T π ρ o (n + 1)).toNat = A π ρ o n ∪
      (outs π ρ o (A π ρ o n) (T π ρ o n).toNat (T π ρ o (n + 1)).toNat).toFinset ∪
      {X π ρ o (T π ρ o (n + 1)).toNat} :=
    R_eq_union_outs π ρ o (T π ρ o n).toNat (T π ρ o (n + 1)).toNat (toNat_T_le π ρ o n hn1)
  rw [X_T π ρ o (n + 1) hn1] at hR
  ext x
  show x ∈ R π ρ o (T π ρ o (n + 1)).toNat ↔ x ∈ Φ π ρ (A π ρ o n)
  rw [hR, Φ_of_terminates π ρ _ hT]
  simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset]
  have hc := Classical.choose_spec hT
  have hcnt := ((hAb π inferInstance hG _ hS _ (Classical.choose hT) _ hc.1 hcomp.1).2 hc.2
    hcomp.2).2.2 x
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · right; rw [← List.count_pos_iff] at h ⊢; omega
    · exact Or.inl (by rw [h]; exact o_mem_A π ρ o n)
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · left; right; rw [← List.count_pos_iff] at h ⊢; omega

/-! ### The backward direction: termination makes `T(n+1)` finite -/

omit [G.LocallyFinite] in
/-- The number of outside actuations during `[t₀, t)`. -/
theorem length_outs (S : Finset V) (t₀ t : ℕ) (ht : t₀ ≤ t) :
    (outs π ρ o S t₀ t).length = ((Finset.Ico t₀ t).filter (fun s => X π ρ o s ∉ S)).card := by
  induction t, ht using Nat.le_induction with
  | base => simp [outs_self]
  | succ t ht ih =>
    rw [outs_succ π ρ o S t₀ t ht, List.length_append, ih]
    have hI : Finset.Ico t₀ (t + 1) = insert t (Finset.Ico t₀ t) := by
      ext s; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hI, Finset.filter_insert]
    by_cases h : X π ρ o t ∈ S
    · simp [h]
    · rw [if_neg h, if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp

/-- Before `T(n+1)`, the departures from `A_n` during `[T(n), t)` are at most
the number of directed edges out of `A_n`: distinct times give distinct
traversals. -/
theorem inside_le (hFLP : External.OneCircuit G) (hG : G.Connected) (n : ℕ)
    (hn : T π ρ o n < ⊤) (t : ℕ) (ht : (t : ℕ∞) ≤ T π ρ o (n + 1)) :
    ((Finset.Ico (T π ρ o n).toNat t).filter (fun s => X π ρ o s ∈ A π ρ o n)).card ≤
      ∑ v ∈ A π ρ o n, G.degree v := by
  classical
  calc ((Finset.Ico (T π ρ o n).toNat t).filter (fun s => X π ρ o s ∈ A π ρ o n)).card
      ≤ ((A π ρ o n).biUnion (fun v => (G.neighborFinset v).image (fun w => (v, w)))).card := by
        refine Finset.card_le_card_of_injOn (fun s => traversal π ρ o s) ?_ ?_
        · intro s hs
          simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hs
          simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image,
            SimpleGraph.mem_neighborFinset, exists_prop]
          exact ⟨X π ρ o s, hs.2, X π ρ o (s + 1), adj_X_succ π ρ o s, rfl⟩
        · intro s hs s' hs' heq
          simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hs hs'
          by_contra hne
          have key : ∀ a b : ℕ, a < b → (T π ρ o n).toNat ≤ a → b < t →
              traversal π ρ o a = traversal π ρ o b → False := by
            intro a b hab ha hb hX
            have h1 : T π ρ o n ≤ (a : ℕ∞) := by
              rw [← coe_toNat_T π ρ o n hn]; exact_mod_cast ha
            have h2 : (b : ℕ∞) < T π ρ o (n + 1) := lt_of_lt_of_le (by exact_mod_cast hb) ht
            exact (hFLP π hG ρ o n hn).1 a b h1 hab h2 hX
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · exact key s s' h hs.1.1 hs'.1.2 heq
          · exact key s' s h hs'.1.1 hs.1.2 heq.symm
    _ ≤ ∑ v ∈ A π ρ o n, ((G.neighborFinset v).image (fun w => (v, w))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ v ∈ A π ρ o n, G.degree v := by
        refine Finset.sum_le_sum (fun v _ => ?_)
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_image_le

/-- If the boundary routing of `A_n` terminates, then `T(n+1) < ∞`: otherwise
the walk would make only finitely many steps after `T(n)`. -/
theorem T_lt_of_terminates (hFLP : External.OneCircuit G) (hAb : External.Abelian G) [Infinite V]
    (hG : G.Connected) (n : ℕ) (hn : T π ρ o n < ⊤) (hT : Terminates π (A π ρ o n) ρ) :
    T π ρ o (n + 1) < ⊤ := by
  by_contra htop
  have htop' : T π ρ o (n + 1) = ⊤ := by
    rcases lt_or_eq_of_le (le_top (a := T π ρ o (n + 1))) with h | h
    · exact absurd h htop
    · exact h
  obtain ⟨ws, hws⟩ := hT
  have hS : (A π ρ o n).Nonempty := ⟨o, o_mem_A π ρ o n⟩
  have hbound : ∀ t, (T π ρ o n).toNat ≤ t →
      t - (T π ρ o n).toNat ≤ ws.length + ∑ v ∈ A π ρ o n, G.degree v := by
    intro t ht
    have ht' : (t : ℕ∞) ≤ T π ρ o (n + 1) := by rw [htop']; exact le_top
    have hinv := walkInv_all π ρ o hFLP hG n hn t ht ht'
    have h1 := ((hAb π inferInstance hG _ hS _ ws _ hws.1 hinv.legal).1 hws.2).1
    have h2 := inside_le π ρ o hFLP hG n hn t ht'
    have h3 := length_outs π ρ o (A π ρ o n) _ t ht
    have h4 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.Ico (T π ρ o n).toNat t) (fun s => X π ρ o s ∈ A π ρ o n)
    rw [Nat.card_Ico] at h4
    omega
  have := hbound ((T π ρ o n).toNat + ws.length + ∑ v ∈ A π ρ o n, G.degree v + 1) (by omega)
  omega

/-- `prop:circuit-iterate`. -/
theorem circuit_iterate_proof (hFLP : External.OneCircuit G) (hAb : External.Abelian G)
    [Infinite V] (hG : G.Connected) (n : ℕ) (hn : T π ρ o n < ⊤) :
    (T π ρ o (n + 1) < ⊤ ↔ Terminates π (A π ρ o n) ρ) ∧
    (T π ρ o (n + 1) < ⊤ → A π ρ o (n + 1) = Φ π ρ (A π ρ o n)) :=
  ⟨⟨terminates_of_T_lt π ρ o hFLP hG n hn, T_lt_of_terminates π ρ o hFLP hAb hG n hn⟩,
    A_succ_eq_Φ π ρ o hFLP hAb hG n hn⟩

end

end Rotor