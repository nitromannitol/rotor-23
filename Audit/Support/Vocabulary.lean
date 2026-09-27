import Mathlib

/-!
# Mathlib-only statement vocabulary for the comparator solutions

A verbatim copy of the vocabulary block (between `VOCABULARY-BEGIN` and
`VOCABULARY-END`) shared by every `Audit/*/Challenge.lean`.  It imports only
Mathlib, so the definitions it declares elaborate exactly as they do in the
challenges; `Audit/check_standalone.sh --vocabulary` checks that the blocks are
byte-identical.  This file plays the role of the per-challenge
`SolutionBasic.lean` of the comparator pattern.
-/

-- VOCABULARY-BEGIN
namespace RotorAudit

open MeasureTheory ProbabilityTheory

/-! ## 1. The rotor walk on a locally finite graph (`rotor.tex:179-225`) -/

section Model

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- A rotor mechanism on `G`: at each vertex `v`, a cyclic permutation `next v`
of the neighbors of `v`. -/
structure Mechanism where
  /-- `π_v`: the next directed edge out of `v` after a given one. -/
  next : ∀ v : V, Equiv.Perm (G.neighborSet v)
  /-- `π_v` is a cyclic permutation. -/
  cyclic : ∀ (v : V) (a b : G.neighborSet v), ∃ k : ℕ, ((next v) ^ k) a = b
  /-- every vertex has an outgoing directed edge. -/
  nonempty : ∀ v : V, Nonempty (G.neighborSet v)

/-- A rotor configuration: one outgoing directed edge at every vertex. -/
abbrev Config := ∀ v : V, G.neighborSet v

variable {G}

/-- The state of the rotor walk: the walker's position and the rotors. -/
structure State (G : SimpleGraph V) where
  /-- The walker's position `X_t`. -/
  pos : V
  /-- The rotor configuration `ρ_t`. -/
  rotor : Config G

variable (π : Mechanism G)

/-- One step of the walk: turn the rotor at the walker's site, then step along it. -/
def step (s : State G) : State G :=
  let a := π.next s.pos (s.rotor s.pos)
  { pos := a.1, rotor := Function.update s.rotor s.pos a }

/-- The walk started at `o` with initial rotors `ρ`, after `t` steps. -/
def walk (ρ : Config G) (o : V) (t : ℕ) : State G := (step π)^[t] ⟨o, ρ⟩

/-- The position `X_t`. -/
def X (ρ : Config G) (o : V) (t : ℕ) : V := (walk π ρ o t).pos

/-- The range `R_t = {X_0, …, X_t}`. -/
def R (ρ : Config G) (o : V) (t : ℕ) : Finset V :=
  (Finset.range (t + 1)).image (X π ρ o)

/-- The number of visits to `o` strictly before time `t`. -/
def visits (ρ : Config G) (o : V) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun s => X π ρ o s = o)).card

/-- `T(n)`, the completion time of the first `n` circuits, with value `⊤` when
no such time exists. -/
noncomputable def T (ρ : Config G) (o : V) (n : ℕ) : ℕ∞ :=
  ⨅ t ∈ {t : ℕ | X π ρ o t = o ∧ G.degree o * n ≤ visits π ρ o t}, (t : ℕ∞)

/-- `A_n = R_{T(n)}`, the range after `n` circuits; meaningful only when
`T n < ⊤`. -/
noncomputable def A (ρ : Config G) (o : V) (n : ℕ) : Finset V :=
  R π ρ o (T π ρ o n).toNat

/-- The walk is recurrent if it visits every vertex infinitely often. -/
def Recurrent (ρ : Config G) (o : V) : Prop :=
  ∀ x : V, Set.Infinite {t : ℕ | X π ρ o t = x}

/-- A particle-and-rotor state `ξ = (σ, ρ)`. -/
structure RState (G : SimpleGraph V) where
  /-- The particle configuration `σ`. -/
  σ : V → ℕ
  /-- The rotor configuration `ρ`. -/
  ρ : Config G

/-- Actuate the vertex `v`: advance its rotor and move one particle along the
new rotor edge, removing the particle if that edge enters the sink set `S`. -/
def actuate (S : Finset V) (ξ : RState G) (v : V) : RState G :=
  let a := π.next v (ξ.ρ v)
  { σ := fun x => (if x = v then ξ.σ x - 1 else ξ.σ x) + (if x = a.1 ∧ a.1 ∉ S then 1 else 0),
    ρ := Function.update ξ.ρ v a }

/-- The state reached from `ξ` by actuating the vertices of `vs` in order. -/
def run (S : Finset V) : RState G → List V → RState G
  | ξ, [] => ξ
  | ξ, v :: vs => run S (actuate π S ξ v) vs

/-- A state is stable when no particles remain outside `S`. -/
def Stable (S : Finset V) (ξ : RState G) : Prop := ∀ v, v ∉ S → ξ.σ v = 0

/-- The list `vs` is a legal routing from `ξ`: each actuated vertex is outside
`S` and occupied at its turn. -/
def IsLegal (S : Finset V) : RState G → List V → Prop
  | _, [] => True
  | ξ, v :: vs => v ∉ S ∧ 0 < ξ.σ v ∧ IsLegal S (actuate π S ξ v) vs

/-- The directed edge traversed by the walk at step `t`: `X_t → X_{t+1}`. -/
def traversal (ρ : Config G) (o : V) (t : ℕ) : V × V := (X π ρ o t, X π ρ o (t + 1))

/-- The number of departures from `x` during the time interval `[a, b)`. -/
def departures (ρ : Config G) (o : V) (x : V) (a b : ℕ) : ℕ :=
  ((Finset.Ico a b).filter (fun t => X π ρ o t = x)).card

end Model

/-! ## 2. The law of the initial rotors (`rotor.tex:228-233`, `1215-1217`) -/

section Law

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The discrete σ-algebra on the finite set of directed edges out of `v`. -/
instance (priority := high) neighborSet.measurableSpace (v : V) :
    MeasurableSpace (G.neighborSet v) := ⊤

/-- The product law of independent initial rotors with one-vertex laws `ν v`. -/
noncomputable def productLaw (ν : ∀ v : V, Measure (G.neighborSet v))
    [∀ v, IsProbabilityMeasure (ν v)] : Measure (Config G) :=
  Measure.infinitePi ν

/-- The uniform law on the directed edges out of `v`. -/
noncomputable def uniformAt (π : Mechanism G) (v : V) : Measure (G.neighborSet v) :=
  haveI := π.nonempty v
  (PMF.uniformOfFintype (G.neighborSet v)).toMeasure

instance (π : Mechanism G) (v : V) : IsProbabilityMeasure (uniformAt π v) := by
  haveI := π.nonempty v
  unfold uniformAt; infer_instance

/-- The law of independent uniform initial rotors. -/
noncomputable def uniformLaw (π : Mechanism G) : Measure (Config G) :=
  productLaw (uniformAt π)

/-- Total variation distance between two laws on a finite type. -/
noncomputable def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ s : Set α, |(μ s).toReal - (ν s).toReal|

end Law

/-! ## 3. Doubly periodic graphs in the plane -/

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

section Periodic

variable {V : Type*} (G : SimpleGraph V)

/-- A doubly periodic graph in the plane. -/
structure DoublyPeriodic where
  /-- The vertex set drawn in the plane: `V ⊂ ℝ²`. -/
  emb : V → Plane
  emb_injective : Function.Injective emb
  /-- The action of the lattice `Λ ≅ ℤ²` by translation. -/
  shift : ℤ × ℤ → V → V
  shift_zero : ∀ v, shift 0 v = v
  shift_add : ∀ z w v, shift (z + w) v = shift z (shift w v)
  /-- A basis of the lattice `Λ`. -/
  b : Fin 2 → Plane
  b_indep : LinearIndependent ℝ b
  emb_shift : ∀ z v, emb (shift z v) = emb v + (z.1 : ℝ) • b 0 + (z.2 : ℝ) • b 1
  /-- Translations are automorphisms. -/
  adj_shift : ∀ z u v, G.Adj (shift z u) (shift z v) ↔ G.Adj u v
  /-- Orbit representatives and coordinates. -/
  rep : V → V
  coord : V → ℤ × ℤ
  shift_coord_rep : ∀ v, shift (coord v) (rep v) = v
  rep_shift : ∀ z v, rep (shift z v) = rep v
  /-- Finitely many orbits. -/
  finite_orbits : (Set.range rep).Finite

namespace DoublyPeriodic

variable {G} (P : DoublyPeriodic G)

/-- A neighbor of `v`, shifted by `z`, is a neighbor of `shift z v`. -/
def shiftNbr (z : ℤ × ℤ) {v : V} (a : G.neighborSet v) : G.neighborSet (P.shift z v) :=
  ⟨P.shift z a.1, (P.adj_shift z v a.1).2 a.2⟩

/-- The mechanism `π` is doubly periodic. -/
def Periodic (π : Mechanism G) : Prop :=
  ∀ (z : ℤ × ℤ) (v : V) (a : G.neighborSet v),
    π.next (P.shift z v) (P.shiftNbr z a) = P.shiftNbr z (π.next v a)

/-- The one-vertex laws `ν` are invariant under the lattice. -/
def InvariantMarginals (ν : ∀ v : V, Measure (G.neighborSet v)) : Prop :=
  ∀ (z : ℤ × ℤ) (v : V), Measure.map (P.shiftNbr z) (ν v) = ν (P.shift z v)

end DoublyPeriodic

end Periodic

/-! ## 4. The square lattice with the clockwise mechanism (`rotor.tex:202-203`) -/

section Square

open Fin.NatCast

/-- A site of the square lattice `ℤ²`. -/
abbrev Site := ℤ × ℤ

/-- A direction out of a site, numbered `0 = N`, `1 = E`, `2 = S`, `3 = W`. -/
abbrev Dir := Fin 4

/-- The unit step `N, E, S, W` in direction `a`. -/
def dirVec (a : Dir) : Site := ![((0 : ℤ), (1 : ℤ)), (1, 0), (0, -1), (-1, 0)] a

/-- The square lattice as a simple graph on `ℤ × ℤ`. -/
def squareGraph : SimpleGraph Site where
  Adj := fun x y : Site => |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨fun x y h => by
    show |y.1 - x.1| + |y.2 - x.2| = 1
    rw [abs_sub_comm y.1, abs_sub_comm y.2]; exact h⟩
  loopless := ⟨fun x h => by simp at h⟩

theorem squareGraph_adj (x y : Site) : squareGraph.Adj x y ↔ |x.1 - y.1| + |x.2 - y.2| = 1 :=
  Iff.rfl

theorem adj_add_dirVec (v : Site) (a : Dir) : squareGraph.Adj v (v + dirVec a) := by
  rw [squareGraph_adj]
  fin_cases a <;> simp [dirVec]

/-- The direction of a unit step `d`. -/
def dirOf (d : Site) : Dir :=
  if d = (0, 1) then 0 else if d = (1, 0) then 1 else if d = (0, -1) then 2 else 3

theorem dirOf_dirVec (a : Dir) : dirOf (dirVec a) = a := by
  fin_cases a <;> simp [dirOf, dirVec]

theorem dirVec_dirOf_of_adj {v w : Site} (h : squareGraph.Adj v w) :
    v + dirVec (dirOf (w - v)) = w := by
  rw [squareGraph_adj] at h
  obtain ⟨a, b⟩ := v
  obtain ⟨c, d⟩ := w
  simp only [Prod.mk_sub_mk, dirOf, dirVec, Prod.mk.injEq] at h ⊢
  rcases abs_cases (a - c) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases abs_cases (b - d) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
  · split_ifs <;> simp_all <;> omega

/-- The four neighbors of a lattice site, indexed by direction. -/
def nbr (v : Site) : Dir ≃ squareGraph.neighborSet v where
  toFun a := ⟨v + dirVec a, adj_add_dirVec v a⟩
  invFun w := dirOf (w.1 - v)
  left_inv a := by simp [dirOf_dirVec]
  right_inv w := Subtype.ext (dirVec_dirOf_of_adj w.2)

instance : squareGraph.LocallyFinite := fun v => Fintype.ofEquiv Dir (nbr v)

/-- Turning by one direction, transported to the neighbors of `v`. -/
def turnAt (v : Site) : Equiv.Perm (squareGraph.neighborSet v) :=
  (nbr v).symm.trans ((Equiv.addRight (1 : Dir)).trans (nbr v))

theorem turnAt_nbr (v : Site) (a : Dir) : turnAt v (nbr v a) = nbr v (a + 1) := by
  simp [turnAt]

theorem turnAt_pow_nbr (v : Site) (k : ℕ) (a : Dir) :
    ((turnAt v) ^ k) (nbr v a) = nbr v (a + (k : Dir)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, turnAt_nbr]
    congr 1
    rw [Nat.cast_succ, add_assoc]

/-- The clockwise rotor mechanism on the square lattice: turn by one direction. -/
def clockwise : Mechanism squareGraph where
  next v := turnAt v
  cyclic v a b := by
    obtain ⟨i, rfl⟩ := (nbr v).surjective a
    obtain ⟨j, rfl⟩ := (nbr v).surjective b
    refine ⟨(j - i).val, ?_⟩
    rw [turnAt_pow_nbr, Fin.cast_val_eq_self]
    congr 1
    exact add_sub_cancel i j
  nonempty v := ⟨nbr v 0⟩

/-- The standard embedding of `ℤ²` in the plane. -/
def squareEmb (v : Site) : Plane := WithLp.toLp 2 ![(v.1 : ℝ), (v.2 : ℝ)]

theorem squareEmb_injective : Function.Injective squareEmb := by
  intro v w h
  have h' : (![(v.1 : ℝ), (v.2 : ℝ)] : Fin 2 → ℝ) = ![(w.1 : ℝ), (w.2 : ℝ)] := by
    have := congrArg WithLp.ofLp h
    simpa [squareEmb] using this
  have h0 := congrFun h' 0
  have h1 := congrFun h' 1
  simp at h0 h1
  exact Prod.ext h0 h1

/-- The square lattice as a doubly periodic graph: `ℤ²` acting on itself by
translation, with the standard basis. -/
noncomputable def squarePeriodic : DoublyPeriodic squareGraph where
  emb := squareEmb
  emb_injective := squareEmb_injective
  shift z v := v + z
  shift_zero v := by simp
  shift_add z w v := by simp [add_comm, add_left_comm]
  b := fun i => WithLp.toLp 2 (Pi.single i 1)
  b_indep := by
    have hb : (fun i => WithLp.toLp 2 (Pi.single i 1) : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
        ⇑(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis := by
      funext i
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      rfl
    rw [hb]
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.linearIndependent
  emb_shift z v := by
    ext i
    fin_cases i <;> simp [squareEmb]
  adj_shift z u v := by
    simp [squareGraph_adj]
  rep _ := 0
  coord v := v
  shift_coord_rep v := by simp
  rep_shift _ _ := rfl
  finite_orbits := by rw [Set.range_const]; exact Set.finite_singleton _

end Square

/-! ## 5. The graph `G_M` of Proposition 1.3 (`rotor.tex:293-314`) -/

section Pendant

open Fin.NatCast

/-- The vertices of `G_M`: lattice sites and `M` leaves at each site. -/
abbrev PVertex (M : ℕ) := Site ⊕ (Site × Fin M)

/-- Adjacency in `G_M`: lattice edges, and each leaf to its lattice vertex. -/
def pendantAdj (M : ℕ) : PVertex M → PVertex M → Prop
  | .inl u, .inl v => squareGraph.Adj u v
  | .inl u, .inr w => u = w.1
  | .inr w, .inl v => w.1 = v
  | .inr _, .inr _ => False

/-- The graph `G_M`. -/
def pendantGraph (M : ℕ) : SimpleGraph (PVertex M) where
  Adj := pendantAdj M
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only [pendantAdj] at h ⊢
    · exact h.symm
    · exact h.symm
    · exact h.symm⟩
  loopless := ⟨fun x h => by
    cases x <;> simp only [pendantAdj] at h
    exact squareGraph.irrefl h⟩

/-- The neighbors of a lattice vertex of `G_M`, in the clockwise order
`N, E, S, W, L_1, …, L_M`. -/
def pendantNbrLattice (M : ℕ) (v : Site) : Fin (M + 4) ≃ (pendantGraph M).neighborSet (.inl v) where
  toFun k := if h : (k : ℕ) < 4 then ⟨.inl (v + dirVec ⟨k, h⟩), adj_add_dirVec v ⟨k, h⟩⟩
    else ⟨.inr (v, ⟨k - 4, by omega⟩), rfl⟩
  invFun w :=
    match w with
    | ⟨.inl u, h⟩ => ⟨(dirOf (u - v) : ℕ), by have := (dirOf (u - v)).2; omega⟩
    | ⟨.inr (_, i), _⟩ => ⟨4 + i, by omega⟩
  left_inv k := by
    by_cases h : (k : ℕ) < 4
    · simp only [h, dite_true]
      ext
      simp [dirOf_dirVec]
    · simp only [h, dite_false]
      ext
      simp
      omega
  right_inv w := by
    rcases w with ⟨u | ⟨u, i⟩, h⟩
    · have hd : (dirOf (u - v) : ℕ) < 4 := (dirOf (u - v)).2
      simp only [hd, dite_true]
      ext
      simp only [Fin.eta]
      exact congrArg Sum.inl (dirVec_dirOf_of_adj h)
    · have h' : v = u := by simpa [pendantGraph, pendantAdj] using h
      subst h'
      have : ¬ (4 + (i : ℕ) < 4) := by omega
      simp only [this, dite_false]
      ext
      simp

/-- The single neighbor of a leaf. -/
def pendantNbrLeaf (M : ℕ) (w : Site × Fin M) : Unit ≃ (pendantGraph M).neighborSet (.inr w) where
  toFun _ := ⟨.inl w.1, rfl⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨u | u, h⟩
    · exact Subtype.ext (congrArg Sum.inl h)
    · exact h.elim

instance (M : ℕ) : (pendantGraph M).LocallyFinite := fun v =>
  match v with
  | .inl v => Fintype.ofEquiv _ (pendantNbrLattice M v)
  | .inr w => Fintype.ofEquiv _ (pendantNbrLeaf M w)

/-- Turning by one position in the clockwise order at a lattice vertex. -/
def pendantTurn (M : ℕ) (v : Site) : Equiv.Perm ((pendantGraph M).neighborSet (.inl v)) :=
  (pendantNbrLattice M v).symm.trans ((Equiv.addRight (1 : Fin (M + 4))).trans (pendantNbrLattice M v))

theorem pendantTurn_pow (M : ℕ) (v : Site) (k : ℕ) (a : Fin (M + 4)) :
    ((pendantTurn M v) ^ k) (pendantNbrLattice M v a) = pendantNbrLattice M v (a + (k : Fin (M + 4))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    simp only [pendantTurn, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.coe_addRight]
    congr 1
    rw [Nat.cast_succ, add_assoc]

/-- The clockwise rotor mechanism on `G_M`: order `N, E, S, W, L_1, …, L_M` at
lattice vertices, the identity at leaves. -/
def pendantMech (M : ℕ) : Mechanism (pendantGraph M) where
  next x := match x with
    | .inl v => pendantTurn M v
    | .inr _ => Equiv.refl _
  cyclic x a b := by
    match x with
    | .inl v =>
      obtain ⟨i, rfl⟩ := (pendantNbrLattice M v).surjective a
      obtain ⟨j, rfl⟩ := (pendantNbrLattice M v).surjective b
      refine ⟨(j - i).val, ?_⟩
      show ((pendantTurn M v) ^ (j - i).val) _ = _
      simp only [pendantTurn_pow, Fin.cast_val_eq_self, add_sub_cancel]
    | .inr w =>
      exact ⟨0, (pendantNbrLeaf M w).symm.injective rfl⟩
  nonempty x := match x with
    | .inl v => ⟨pendantNbrLattice M v (0 : Fin (M + 4))⟩
    | .inr w => ⟨pendantNbrLeaf M w ()⟩

end Pendant

/-! ## 6. The results the paper cites without proof

Each is a proposition, taken as an explicit hypothesis by the theorems that use
it; none is proved here. -/

namespace External

section Graph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- Florescu--Levine--Peres, Lemmas 2.1 and 2.4 (`lem:one-circuit`), assumed. -/
def OneCircuit : Prop :=
  ∀ (π : Mechanism G), G.Connected →
    ∀ (ρ : Config G) (o : V) (n : ℕ), T π ρ o n < ⊤ →
      (∀ s t : ℕ, T π ρ o n ≤ (s : ℕ∞) → s < t → (t : ℕ∞) < T π ρ o (n + 1) →
          traversal π ρ o s ≠ traversal π ρ o t) ∧
      (T π ρ o (n + 1) < ⊤ → ∀ x ∈ A π ρ o n,
          departures π ρ o x (T π ρ o n).toNat (T π ρ o (n + 1)).toNat = G.degree x)

/-- Holroyd--Levine--Mészáros--Peres--Propp--Wilson, Lemma 3.9 (`lem:least-action`), assumed. -/
def Abelian : Prop :=
  ∀ (π : Mechanism G), Infinite V → G.Connected →
    ∀ (S : Finset V), S.Nonempty → ∀ (ξ : RState G) (vs ws : List V),
      IsLegal π S ξ vs → IsLegal π S ξ ws →
      (Stable S (run π S ξ vs) → ws.length ≤ vs.length ∧ ∀ v, ws.count v ≤ vs.count v) ∧
      (Stable S (run π S ξ vs) → Stable S (run π S ξ ws) →
        ws.length = vs.length ∧ run π S ξ ws = run π S ξ vs ∧ ∀ v, ws.count v = vs.count v)

/-- Holroyd--Propp, Lemma 6, assumed. -/
def VisitsAllOfVisitsOne : Prop :=
  ∀ (π : Mechanism G), Infinite V → G.Connected →
    ∀ (ρ : Config G) (o x : V), Set.Infinite {t : ℕ | X π ρ o t = x} → Recurrent π ρ o

/-- Angel--Holroyd, Theorem 1, assumed. -/
def RecurrentOfRecurrent : Prop :=
  ∀ (π : Mechanism G), Infinite V → G.Connected →
    ∀ (ρ : Config G) (o o' : V), Recurrent π ρ o → Recurrent π ρ o'

end Graph

set_option linter.deprecated false in
/-- The Bernoulli law on `Bool` with success probability `p`. -/
noncomputable def bernoulli (p : NNReal) (hp : p ≤ 1) : Measure Bool := (PMF.bernoulli p hp).toMeasure

instance (p : NNReal) (hp : p ≤ 1) : IsProbabilityMeasure (bernoulli p hp) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- Independent Bernoulli(`p`) variables indexed by `ℤ²`. -/
noncomputable def bernoulliField (p : NNReal) (hp : p ≤ 1) : Measure (ℤ × ℤ → Bool) :=
  Measure.infinitePi (fun _ : ℤ × ℤ => bernoulli p hp)

/-- A set of `{0,1}`-fields is increasing. -/
def IsIncreasing (A : Set (ℤ × ℤ → Bool)) : Prop :=
  ∀ ω ω' : ℤ × ℤ → Bool, ω ∈ A → (∀ z, ω z = true → ω' z = true) → ω' ∈ A

/-- The field with law `μ` is `k`-dependent. -/
def KDependent (k : ℕ) (μ : Measure (ℤ × ℤ → Bool)) : Prop :=
  ∀ I J : Finset (ℤ × ℤ), (∀ i ∈ I, ∀ j ∈ J, (k : ℤ) < max |i.1 - j.1| |i.2 - j.2|) →
    IndepFun (fun ω : ℤ × ℤ → Bool => (fun i : I => ω i)) (fun ω => (fun j : J => ω j)) μ

theorem eighth_le_one : (1 / 8 : NNReal) ≤ 1 := by
  rw [div_le_one (by norm_num)]; norm_num

/-- Liggett--Schonmann--Stacey, Theorem 0.0(ii), in the instance used, assumed. -/
def LSS : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ μ : Measure (ℤ × ℤ → Bool), IsProbabilityMeasure μ →
    KDependent 2 μ → (∀ z, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
    ∀ A : Set (ℤ × ℤ → Bool), MeasurableSet A → IsIncreasing A →
      μ A ≤ bernoulliField (1 / 8) eighth_le_one A

end External

end RotorAudit
-- VOCABULARY-END
