import Rotor.Pendant
import Rotor.Support.SquareBasics

/-!
# Basic facts on the pendant graph `G_M`

Basic facts on `G_M` (`rotor.tex:291-299` and Section 6): connectivity, degrees, the
doubly periodic structure under lattice translations, and the periodicity of the clockwise
mechanism.
-/

open Fin.NatCast

namespace Rotor

variable (M : ℕ)

/-- The inclusion of the lattice is a graph homomorphism. -/
def pendantInl : squareGraph →g pendantGraph M where
  toFun := Sum.inl
  map_rel' h := h

/-- Each lattice site `v` is adjacent, in `G_M`, to each of its `M` pendant leaves `(v, i)`. -/
theorem pendantGraph_adj_inl_inr (v : Site) (i : Fin M) :
    (pendantGraph M).Adj (.inl v) (.inr (v, i)) := rfl

/-- `G_M` is connected: every vertex reaches some lattice vertex `.inl v` in at most one step,
and lattice vertices are joined through the connectivity of the square lattice `squareGraph`. -/
theorem pendantGraph_reachable (x y : PVertex M) : (pendantGraph M).Reachable x y := by
  have key : ∀ x : PVertex M, ∃ v : Site, (pendantGraph M).Reachable x (.inl v) := by
    rintro (v | ⟨v, i⟩)
    · exact ⟨v, SimpleGraph.Reachable.refl _⟩
    · exact ⟨v, (pendantGraph_adj_inl_inr M v i).symm.reachable⟩
  obtain ⟨u, hu⟩ := key x
  obtain ⟨v, hv⟩ := key y
  refine hu.trans (SimpleGraph.Reachable.trans ?_ hv.symm)
  exact (squareGraph_reachable u v).map (pendantInl M)

/-- `G_M` is connected, from `pendantGraph_reachable`. -/
theorem pendantGraph_connected : (pendantGraph M).Connected :=
  ⟨fun x y => pendantGraph_reachable M x y⟩

/-- A lattice vertex `.inl v` has degree `M + 4` in `G_M`: its four lattice neighbors plus its
`M` pendant leaves, via the neighbor-set equivalence `pendantNbrLattice`. -/
theorem pendantGraph_degree_inl (v : Site) : (pendantGraph M).degree (.inl v) = M + 4 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr (pendantNbrLattice M v).symm]
  simp

/-- A pendant leaf `.inr w` has degree `1` in `G_M`, via the neighbor-set equivalence
`pendantNbrLeaf`. -/
theorem pendantGraph_degree_inr (w : Site × Fin M) : (pendantGraph M).degree (.inr w) = 1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr (pendantNbrLeaf M w).symm]
  simp

/-- Every vertex of `G_M` has degree at most `M + 4`: lattice vertices by
`pendantGraph_degree_inl`, leaves by `pendantGraph_degree_inr`. -/
theorem pendantGraph_degree_le (x : PVertex M) : (pendantGraph M).degree x ≤ M + 4 := by
  rcases x with v | w
  · exact (pendantGraph_degree_inl M v).le
  · rw [pendantGraph_degree_inr]; omega

/-- `PVertex M` is infinite, inherited from its infinite lattice summand `Site`. -/
instance : Infinite (PVertex M) := inferInstance

/-- Shifting by the zero vector fixes every vertex of `G_M`. -/
theorem pendantShift_zero (x : PVertex M) : pendantShift M 0 x = x := by
  rcases x with v | ⟨v, i⟩ <;> simp [pendantShift]

/-- Shifting by `z + w` factors as shifting by `w` and then by `z`, so `pendantShift M` gives an
additive action of `Site` on `G_M`. -/
theorem pendantShift_add (z w : Site) (x : PVertex M) :
    pendantShift M (z + w) x = pendantShift M z (pendantShift M w x) := by
  rcases x with v | ⟨v, i⟩ <;> simp [pendantShift, add_comm, add_left_comm]

/-- Translating both endpoints of an edge by the same `z` preserves adjacency in `G_M`, so
`pendantShift M` acts by graph automorphisms. -/
theorem pendantGraph_adj_shift (z : Site) (x y : PVertex M) :
    (pendantGraph M).Adj (pendantShift M z x) (pendantShift M z y) ↔ (pendantGraph M).Adj x y := by
  rcases x with u | ⟨u, i⟩ <;> rcases y with v | ⟨v, j⟩ <;>
    simp [pendantGraph, pendantAdj, pendantShift, squareGraph_adj]

/-- The orbit representative: translate the lattice site to the origin. -/
def pendantRep : PVertex M → PVertex M
  | .inl _ => .inl 0
  | .inr (_, i) => .inr (0, i)

/-- The lattice coordinate of a vertex. -/
def pendantCoord : PVertex M → Site
  | .inl v => v
  | .inr (v, _) => v

/-- `G_M` as a doubly periodic graph. -/
noncomputable def pendantPeriodic : DoublyPeriodic (pendantGraph M) where
  emb := pendantEmb M
  emb_injective := pendantEmb_injective M
  shift := pendantShift M
  shift_zero := pendantShift_zero M
  shift_add := pendantShift_add M
  b := fun i => WithLp.toLp 2 (Pi.single i 1)
  b_indep := by
    have hb : (fun i => WithLp.toLp 2 (Pi.single i 1) : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
        ⇑(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis := by
      funext i
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      rfl
    rw [hb]
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.linearIndependent
  emb_shift z x := by
    rcases x with v | ⟨v, i⟩
    · ext k
      fin_cases k <;> simp [pendantEmb, pendantShift, squareEmb]
    · ext k
      fin_cases k <;> simp [pendantEmb, pendantShift, squareEmb] <;> ring
  adj_shift := pendantGraph_adj_shift M
  rep := pendantRep M
  coord := pendantCoord M
  shift_coord_rep x := by
    rcases x with v | ⟨v, i⟩ <;> simp [pendantShift, pendantRep, pendantCoord]
  rep_shift z x := by
    rcases x with v | ⟨v, i⟩ <;> rfl
  finite_orbits := by
    have hsub : Set.range (pendantRep M) ⊆
        {Sum.inl 0} ∪ Set.range (fun i : Fin M => (Sum.inr (0, i) : PVertex M)) := by
      rintro _ ⟨x, rfl⟩
      rcases x with v | ⟨v, i⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨i, rfl⟩
    exact Set.Finite.subset ((Set.finite_singleton _).union (Set.finite_range _)) hsub

/-- Translating a lattice vertex's `k`-th neighbor (via `pendantNbrLattice`) by `z` agrees with
taking the `k`-th neighbor of the translated site `v + z`. -/
theorem pendantNbrLattice_shift (z : Site) (v : Site) (k : Fin (M + 4)) :
    (pendantPeriodic M).shiftNbr z (pendantNbrLattice M v k) = pendantNbrLattice M (v + z) k := by
  apply Subtype.ext
  simp only [pendantNbrLattice, Equiv.coe_fn_mk]
  split_ifs with h
  · show Sum.inl (v + dirVec ⟨k, h⟩ + z) = Sum.inl (v + z + dirVec ⟨k, h⟩)
    rw [add_right_comm]
  · rfl

/-- The clockwise mechanism on `G_M` is invariant under translations. -/
theorem pendantPeriodic_periodic : (pendantPeriodic M).Periodic (pendantMech M) := by
  intro z x a
  rcases x with v | w
  · obtain ⟨k, rfl⟩ := (pendantNbrLattice M v).surjective a
    show pendantTurn M (v + z) _ = (pendantPeriodic M).shiftNbr z (pendantTurn M v _)
    rw [pendantNbrLattice_shift]
    have h1 : pendantTurn M (v + z) (pendantNbrLattice M (v + z) k) =
        pendantNbrLattice M (v + z) (k + 1) := by
      simpa using pendantTurn_pow M (v + z) 1 k
    have h2 : pendantTurn M v (pendantNbrLattice M v k) = pendantNbrLattice M v (k + 1) := by
      simpa using pendantTurn_pow M v 1 k
    rw [h1, h2, pendantNbrLattice_shift]
  · rfl

end Rotor
