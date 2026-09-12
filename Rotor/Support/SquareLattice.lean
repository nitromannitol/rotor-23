import Rotor.Support.SquareBasics
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
Finite-index translation sublattices of the square graph (`rotor.tex:231-235`).
An integer basis supplies the shifts and a finite quotient supplies the orbit representatives.
-/

open Module

namespace Rotor

theorem squareLattice_rank (Λ : AddSubgroup Site) [Λ.FiniteIndex] :
    Module.finrank ℤ Λ.toIntSubmodule = 2 := by
  simpa [Module.finrank_prod] using! AddSubgroup.finrank_eq_of_finiteIndex Λ

noncomputable def squareLatticeBasis (Λ : AddSubgroup Site) [Λ.FiniteIndex] :
    Basis (Fin 2) ℤ Λ.toIntSubmodule :=
  (Module.finBasis ℤ Λ.toIntSubmodule).reindex (finCongr (squareLattice_rank Λ))

theorem squarePair_det_ne_zero (a b : Site) (h : LinearIndependent ℤ ![a, b]) :
    a.1 * b.2 - a.2 * b.1 ≠ 0 := by
  intro hd
  have hc := LinearIndependent.pair_iff.mp h
  have hs : b.2 = 0 ∧ -a.2 = 0 := hc b.2 (-a.2) (by
    apply Prod.ext <;> change _ * _ + _ * _ = (0 : ℤ) <;> nlinarith)
  have hf : b.1 = 0 ∧ -a.1 = 0 := hc b.1 (-a.1) (by
    apply Prod.ext <;> change _ * _ + _ * _ = (0 : ℤ) <;> nlinarith)
  have ha : a = 0 := Prod.ext (by simpa using neg_eq_zero.mp hf.2) (by simpa using neg_eq_zero.mp hs.2)
  exact h.ne_zero 0 ha

theorem squareEmb_pair_independent (a b : Site) (h : a.1 * b.2 - a.2 * b.1 ≠ 0) :
    LinearIndependent ℝ ![squareEmb a, squareEmb b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrArg (fun x : Plane => x 0) hst
  have h1 := congrArg (fun x : Plane => x 1) hst
  simp [squareEmb] at h0 h1
  have hd : (a.1 : ℝ) * (b.2 : ℝ) - (a.2 : ℝ) * (b.1 : ℝ) ≠ 0 := by
    exact_mod_cast h
  have hs : s * ((a.1 : ℝ) * (b.2 : ℝ) - (a.2 : ℝ) * (b.1 : ℝ)) = 0 := by
    linear_combination (b.2 : ℝ) * h0 - (b.1 : ℝ) * h1
  have ht : t * ((a.1 : ℝ) * (b.2 : ℝ) - (a.2 : ℝ) * (b.1 : ℝ)) = 0 := by
    linear_combination (a.1 : ℝ) * h1 - (a.2 : ℝ) * h0
  exact ⟨(mul_eq_zero.mp hs).resolve_right hd, (mul_eq_zero.mp ht).resolve_right hd⟩

theorem squareEmb_add (v w : Site) : squareEmb (v + w) = squareEmb v + squareEmb w := by
  ext i
  fin_cases i <;> simp [squareEmb]

theorem squareEmb_zsmul (n : ℤ) (v : Site) : squareEmb (n • v) = (n : ℝ) • squareEmb v := by
  ext i
  fin_cases i <;> simp [squareEmb, smul_eq_mul]

noncomputable def squareLatticeVector (Λ : AddSubgroup Site) [Λ.FiniteIndex] (z : Site) :
    Λ.toIntSubmodule := (squareLatticeBasis Λ).equivFun.symm ![z.1, z.2]

theorem squareLatticeVector_formula (Λ : AddSubgroup Site) [Λ.FiniteIndex] (z : Site) :
    squareLatticeVector Λ z = z.1 • squareLatticeBasis Λ 0 + z.2 • squareLatticeBasis Λ 1 := by
  simp [squareLatticeVector, Basis.equivFun_symm_apply, Fin.sum_univ_two]

theorem squareLatticeVector_zero (Λ : AddSubgroup Site) [Λ.FiniteIndex] :
    squareLatticeVector Λ 0 = 0 := by
  simp [squareLatticeVector_formula]

theorem squareLatticeVector_add (Λ : AddSubgroup Site) [Λ.FiniteIndex] (z w : Site) :
    squareLatticeVector Λ (z + w) = squareLatticeVector Λ z + squareLatticeVector Λ w := by
  simp only [squareLatticeVector_formula, Prod.fst_add, Prod.snd_add, add_smul]
  abel

noncomputable def squareLatticeRep (Λ : AddSubgroup Site) (v : Site) : Site :=
  ((QuotientAddGroup.mk' Λ) v).out

theorem squareLatticeRep_sub_mem (Λ : AddSubgroup Site) (v : Site) :
    v - squareLatticeRep Λ v ∈ Λ := by
  apply QuotientAddGroup.eq_iff_sub_mem.mp
  exact (QuotientAddGroup.out_eq' ((QuotientAddGroup.mk' Λ) v)).symm

theorem squareLatticeRep_add (Λ : AddSubgroup Site) (v z : Site) (hz : z ∈ Λ) :
    squareLatticeRep Λ (v + z) = squareLatticeRep Λ v := by
  unfold squareLatticeRep
  congr 1
  rw [map_add]
  have hz0 : (QuotientAddGroup.mk' Λ) z = 0 := (QuotientAddGroup.eq_zero_iff z).mpr hz
  rw [hz0, add_zero]

theorem squareLatticeRep_finite (Λ : AddSubgroup Site) [Λ.FiniteIndex] :
    (Set.range (squareLatticeRep Λ)).Finite := by
  apply (Set.finite_range (fun q : Site ⧸ Λ => q.out)).subset
  rintro x ⟨v, rfl⟩
  exact ⟨_, rfl⟩

noncomputable def squareLatticeCoord (Λ : AddSubgroup Site) [Λ.FiniteIndex] (v : Site) : Site :=
  let f := (squareLatticeBasis Λ).equivFun ⟨v - squareLatticeRep Λ v, squareLatticeRep_sub_mem Λ v⟩
  (f 0, f 1)

theorem squareLatticeVector_coord (Λ : AddSubgroup Site) [Λ.FiniteIndex] (v : Site) :
    (squareLatticeVector Λ (squareLatticeCoord Λ v) : Site) = v - squareLatticeRep Λ v := by
  unfold squareLatticeVector squareLatticeCoord
  dsimp only
  have he : ∀ f : Fin 2 → ℤ, ![f 0, f 1] = f := by
    intro f
    ext i
    fin_cases i <;> rfl
  rw [he, LinearEquiv.symm_apply_apply]

theorem squareLatticeBasis_independent (Λ : AddSubgroup Site) [Λ.FiniteIndex] :
    LinearIndependent ℝ (fun i => squareEmb (squareLatticeBasis Λ i)) := by
  have h := (squareLatticeBasis Λ).linearIndependent.map'
    Λ.toIntSubmodule.subtype (Submodule.ker_subtype _)
  have he : (Λ.toIntSubmodule.subtype ∘ squareLatticeBasis Λ) =
      ![(squareLatticeBasis Λ 0 : Site), (squareLatticeBasis Λ 1 : Site)] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  have hr := squareEmb_pair_independent _ _ (squarePair_det_ne_zero _ _ h)
  convert hr using 1
  funext i
  fin_cases i <;> rfl

theorem squareLattice_emb_shift (Λ : AddSubgroup Site) [Λ.FiniteIndex] (z v : Site) :
    squareEmb (v + squareLatticeVector Λ z) = squareEmb v +
      (z.1 : ℝ) • squareEmb (squareLatticeBasis Λ 0) +
      (z.2 : ℝ) • squareEmb (squareLatticeBasis Λ 1) := by
  rw [squareLatticeVector_formula]
  change squareEmb (v + (z.1 • (squareLatticeBasis Λ 0 : Site) +
    z.2 • (squareLatticeBasis Λ 1 : Site))) = _
  rw [squareEmb_add, squareEmb_add, squareEmb_zsmul, squareEmb_zsmul, add_assoc]

/-- The square graph with the translation action of a finite-index sublattice. -/
noncomputable def squareLatticePeriodic (Λ : AddSubgroup Site) [Λ.FiniteIndex] :
    DoublyPeriodic squareGraph where
  emb := squareEmb
  emb_injective := squareEmb_injective
  shift z v := v + squareLatticeVector Λ z
  shift_zero v := by rw [squareLatticeVector_zero]; simp
  shift_add z w v := by rw [squareLatticeVector_add]; simp [add_comm, add_left_comm]
  b i := squareEmb (squareLatticeBasis Λ i)
  b_indep := squareLatticeBasis_independent Λ
  emb_shift := squareLattice_emb_shift Λ
  adj_shift z u v := squarePeriodic.adj_shift (squareLatticeVector Λ z) u v
  rep := squareLatticeRep Λ
  coord := squareLatticeCoord Λ
  shift_coord_rep v := by rw [squareLatticeVector_coord]; abel
  rep_shift z v := squareLatticeRep_add Λ v _ (squareLatticeVector Λ z).property
  finite_orbits := squareLatticeRep_finite Λ

/-- Clockwise cyclic orders commute with every translation in the sublattice. -/
theorem squareLatticePeriodic_periodic (Λ : AddSubgroup Site) [Λ.FiniteIndex] :
    (squareLatticePeriodic Λ).Periodic clockwise := by
  intro z v a
  exact squarePeriodic_periodic (squareLatticeVector Λ z) v a

/-- Invariant neighbor laws give invariant marginals for the chosen lattice basis. -/
theorem squareLatticePeriodic_invariantMarginals (Λ : AddSubgroup Site) [Λ.FiniteIndex]
    (ν : ∀ v : Site, MeasureTheory.Measure (squareGraph.neighborSet v))
    (hν : ∀ z ∈ Λ, ∀ v, MeasureTheory.Measure.map (squarePeriodic.shiftNbr z) (ν v) = ν (v + z)) :
    (squareLatticePeriodic Λ).InvariantMarginals ν := by
  intro z v
  exact hν (squareLatticeVector Λ z) (squareLatticeVector Λ z).property v

end Rotor
