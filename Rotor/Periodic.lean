/-
Doubly periodic graphs and mechanisms, and laws invariant under the lattice.

`rotor.tex:217-227`: "A doubly periodic graph in `ℝ²` is a connected, locally
finite graph `G = (V, E)` with vertex set `V ⊂ ℝ²`, on which a rank-two lattice
`Λ ⊂ ℝ²` acts by translation.  We assume these translations are automorphisms
of `G` with finitely many orbits in `V`.  A rotor mechanism on `G` is doubly
periodic if its cyclic orders are invariant under `Λ`."

`rotor.tex:1036-1040` (prop:path-reduction (iii)): "the rotor law is invariant
and ergodic under the translation lattice".

`rotor.tex:1212-1226` (Section 3.2): "identify its translation lattice with
`ℤ²`, so that the vertex set splits into finite sets indexed by `ℤ²`.  For an
integer `L ≥ 1` and `z ∈ ℤ²`, let the block `Q_z` be the union of the sets
indexed by `Lz + {0, …, L-1}²`, and let `Q_z⁺ := ⋃_{|w-z|_∞ ≤ 1} Q_w`."

Rulings:

  M-014  A doubly periodic graph is the data `P : DoublyPeriodic G`: an
         injective embedding `emb : V → ℝ²`, a `ℤ²`-action `shift` by graph
         automorphisms, two `ℝ`-independent vectors `b 0, b 1` spanning the
         lattice `Λ` with `emb (shift z v) = emb v + z₁ b₀ + z₂ b₁`, and a
         choice of orbit representatives `rep` with coordinates `coord`, so
         that `v = shift (coord v) (rep v)`; "finitely many orbits" is
         `(Set.range rep).Finite`.  The representatives are a choice, not a
         restriction: every graph the paper calls doubly periodic admits one.
         `coord` is the paper's identification of `V` with finite sets indexed
         by `ℤ²`.
  M-015  A law `μ` on `Config G` is invariant when every lattice shift is
         measure preserving, and ergodic when every measurable shift-invariant
         set is null or conull.  Connectedness and infinitude of `V` are
         hypotheses of the statements, as in the paper, not fields.
  M-016  The total variation distance between two laws on a finite set is
         `sup_s |μ s - ν s|` over all subsets, as a real number.
-/
import Rotor.Law

open MeasureTheory Finset

namespace Rotor

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

/-- A doubly periodic graph in the plane (ruling M-014). -/
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

/-- The mechanism `π` is doubly periodic: its cyclic orders are invariant under
the lattice. -/
def Periodic (π : Mechanism G) : Prop :=
  ∀ (z : ℤ × ℤ) (v : V) (a : G.neighborSet v),
    π.next (P.shift z v) (P.shiftNbr z a) = P.shiftNbr z (π.next v a)

omit [DecidableEq V] [G.LocallyFinite] in
theorem shift_neg_shift (z : ℤ × ℤ) (v : V) : P.shift z (P.shift (-z) v) = v := by
  rw [← P.shift_add, add_neg_cancel, P.shift_zero]

omit [DecidableEq V] [G.LocallyFinite] in
theorem shift_shift_neg (z : ℤ × ℤ) (v : V) : P.shift (-z) (P.shift z v) = v := by
  rw [← P.shift_add, neg_add_cancel, P.shift_zero]

/-- The lattice acting on rotor configurations: `(z • ρ) (shift z v) = shift z (ρ v)`;
at `v` the rotor points to the shift of where the rotor at `shift (-z) v` points. -/
def shiftConfig (z : ℤ × ℤ) (ρ : Config G) : Config G := fun v =>
  ⟨P.shift z (ρ (P.shift (-z) v)).1, by
    have := (P.adj_shift z _ _).2 (ρ (P.shift (-z) v)).2
    rwa [P.shift_neg_shift] at this⟩

/-- The law `μ` is invariant under the lattice (ruling M-015). -/
def Invariant (μ : Measure (Config G)) : Prop :=
  ∀ z : ℤ × ℤ, MeasurePreserving (P.shiftConfig z) μ μ

/-- The one-vertex laws `ν` are invariant under the lattice: the law at
`shift z v` is the image of the law at `v` (`rotor.tex:270-272`). -/
def InvariantMarginals (ν : ∀ v : V, Measure (G.neighborSet v)) : Prop :=
  ∀ (z : ℤ × ℤ) (v : V), Measure.map (P.shiftNbr z) (ν v) = ν (P.shift z v)

/-- The law `μ` is ergodic under the lattice (ruling M-015). -/
def Ergodic (μ : Measure (Config G)) : Prop :=
  ∀ s : Set (Config G), MeasurableSet s → (∀ z, P.shiftConfig z ⁻¹' s = s) → μ s = 0 ∨ μ s = 1

/-- The block `Q_z` of side `L`: the vertices whose coordinates lie in
`Lz + {0, …, L-1}²` (`eq:block-definitions`). -/
def block (L : ℕ) (z : ℤ × ℤ) : Set V :=
  {v | (P.coord v).1 - L * z.1 ∈ Set.Ico 0 (L : ℤ) ∧ (P.coord v).2 - L * z.2 ∈ Set.Ico 0 (L : ℤ)}

/-- `Q_z⁺`, the union of the blocks at `ℓ^∞`-distance at most one from `z`. -/
def blockPlus (L : ℕ) (z : ℤ × ℤ) : Set V :=
  ⋃ w ∈ {w : ℤ × ℤ | max |w.1 - z.1| |w.2 - z.2| ≤ 1}, P.block L w

end DoublyPeriodic

/-- Total variation distance between two laws on a finite type (ruling M-016). -/
noncomputable def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ s : Set α, |(μ s).toReal - (ν s).toReal|

end Rotor
