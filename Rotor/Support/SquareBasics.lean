import Rotor.Square
import Rotor.Support.ProductErgodic

/-!
Basic facts on the square lattice with the clockwise mechanism (`rotor.tex:1486-1496`):
connectivity, degree four, and periodicity of the mechanism under translations.
-/

open Finset

namespace Rotor

theorem squareGraph_adj_add_east (x : Site) : squareGraph.Adj x (x + (1, 0)) := by
  rw [squareGraph_adj]; simp
theorem squareGraph_adj_add_west (x : Site) : squareGraph.Adj x (x + (-1, 0)) := by
  rw [squareGraph_adj]; simp
theorem squareGraph_adj_add_north (x : Site) : squareGraph.Adj x (x + (0, 1)) := by
  rw [squareGraph_adj]; simp
theorem squareGraph_adj_add_south (x : Site) : squareGraph.Adj x (x + (0, -1)) := by
  rw [squareGraph_adj]; simp

theorem squareGraph_reachable (x y : Site) : squareGraph.Reachable x y := by
  have key : ∀ n : ℕ, ∀ x y : Site, (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = n →
      squareGraph.Reachable x y := by
    intro n
    induction n with
    | zero =>
      intro x y h
      have hx : x = y := by
        obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
        simp only [Prod.mk.injEq]; omega
      rw [hx]
    | succ n ih =>
      intro x y h
      rcases lt_trichotomy x.1 y.1 with h1 | h1 | h1
      · exact (squareGraph_adj_add_east x).reachable.trans (ih (x + (1, 0)) y (by
          simp only [Prod.fst_add, Prod.snd_add]; omega))
      · rcases lt_or_gt_of_ne (show x.2 ≠ y.2 by intro h2; omega) with h2 | h2
        · exact (squareGraph_adj_add_north x).reachable.trans (ih (x + (0, 1)) y (by
            simp only [Prod.fst_add, Prod.snd_add]; omega))
        · exact (squareGraph_adj_add_south x).reachable.trans (ih (x + (0, -1)) y (by
            simp only [Prod.fst_add, Prod.snd_add]; omega))
      · exact (squareGraph_adj_add_west x).reachable.trans (ih (x + (-1, 0)) y (by
          simp only [Prod.fst_add, Prod.snd_add]; omega))
  exact key _ x y rfl

theorem squareGraph_connected : squareGraph.Connected :=
  ⟨fun x y => squareGraph_reachable x y⟩

theorem squareGraph_degree (v : Site) : squareGraph.degree v = 4 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr (nbr v).symm]
  rfl

/-- The clockwise mechanism is invariant under translations. -/
theorem squarePeriodic_periodic : squarePeriodic.Periodic clockwise := by
  intro z v a
  obtain ⟨a₀, rfl⟩ := (nbr v).surjective a
  have h1 : squarePeriodic.shiftNbr z (nbr v a₀) = nbr (squarePeriodic.shift z v) a₀ := by
    apply Subtype.ext
    show v + dirVec a₀ + z = v + z + dirVec a₀
    ring
  have h2 : squarePeriodic.shiftNbr z (nbr v (a₀ + 1)) =
      nbr (squarePeriodic.shift z v) (a₀ + 1) := by
    apply Subtype.ext
    show v + dirVec (a₀ + 1) + z = v + z + dirVec (a₀ + 1)
    ring
  show turnAt _ _ = _
  rw [h1, turnAt_nbr]
  show _ = squarePeriodic.shiftNbr z (turnAt v (nbr v a₀))
  rw [turnAt_nbr, h2]

instance : Infinite Site := inferInstance

end Rotor
