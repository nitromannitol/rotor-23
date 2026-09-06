import Rotor.External.SubcriticalDecay
import Percolation.Literature.KestenTheoremProofs
import Percolation.Literature.SharpnessDCTProofs
import Percolation.Literature.BondPercolationSymmetry

/-!
Phase two: `External.SubcriticalDecay` proved from the percolation library
(`anthropics/formal-math`, subdirectory `percolation`, commit 795efb86): Kesten's
`p_c(ℤ²) = 1/2` (`kesten_criticalProb_Z2_holds`) and the sharpness of the phase transition
(`perc_sharpness_holds`).  The bridge identifies our bond field `Sym2 (ℤ × ℤ) → Bool` under
`bondLaw p` with the library's `bondPercolation (zdGraph 2) p` on `Set (Sym2 (Fin 2 → ℤ))`,
translates the box crossing to the origin, and reads a box crossing as the library's one-arm
event `siteToBoundary 2 r`.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open Percolation.Literature Percolation.Literature.LatticeModels

namespace Rotor.Bridge

/-! ### Sites and adjacency -/

/-- `ℤ × ℤ ≃ (Fin 2 → ℤ)`. -/
def siteEquiv : Site ≃ LatticeModels.Site 2 := (finTwoArrowEquiv ℤ).symm

theorem siteEquiv_apply (u : Site) : siteEquiv u = ![u.1, u.2] := rfl

theorem siteEquiv_sub_add (a x : Site) : siteEquiv (a - x) + siteEquiv x = siteEquiv a := by
  funext i
  fin_cases i <;> simp [siteEquiv_apply]

theorem siteEquiv_self_sub (x : Site) : siteEquiv (x - x) = 0 := by
  funext i
  fin_cases i <;> simp [siteEquiv_apply]

theorem siteEquiv_zero : siteEquiv 0 = 0 := by
  funext i
  fin_cases i <;> simp [siteEquiv_apply]

theorem square_adj_cases {v w : Site} (h : squareGraph.Adj v w) :
    (w.1 = v.1 + 1 ∧ w.2 = v.2) ∨ (w.1 = v.1 - 1 ∧ w.2 = v.2) ∨
    (w.1 = v.1 ∧ w.2 = v.2 + 1) ∨ (w.1 = v.1 ∧ w.2 = v.2 - 1) := by
  rw [squareGraph_adj] at h
  rcases abs_cases (v.1 - w.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (v.2 - w.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

theorem zd_adj_iff (u v : Site) :
    (zdGraph 2).Adj (siteEquiv u) (siteEquiv v) ↔ squareGraph.Adj u v := by
  rw [zdGraph_adj_iff]
  constructor
  · rintro ⟨i, h | h⟩
    · have h0 := congrFun h 0
      have h1 := congrFun h 1
      rw [squareGraph_adj]
      fin_cases i <;> simp [siteEquiv_apply] at h0 h1 <;> rw [h0, h1] <;> simp
    · have h0 := congrFun h 0
      have h1 := congrFun h 1
      rw [squareGraph_adj]
      fin_cases i <;> simp [siteEquiv_apply] at h0 h1 <;> rw [h0, h1] <;> simp
  · intro h
    rcases square_adj_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, Or.inl (by funext i; fin_cases i <;> simp [siteEquiv_apply, h1, h2])⟩
    · exact ⟨0, Or.inr (by funext i; fin_cases i <;> simp [siteEquiv_apply, h1, h2])⟩
    · exact ⟨1, Or.inl (by funext i; fin_cases i <;> simp [siteEquiv_apply, h1, h2])⟩
    · exact ⟨1, Or.inr (by funext i; fin_cases i <;> simp [siteEquiv_apply, h1, h2])⟩

/-! ### Bond configurations -/

/-- The bijection of unordered pairs. -/
def pairEquiv : Sym2 Site ≃ Sym2 (LatticeModels.Site 2) := sym2Equiv siteEquiv

/-- The edge indicators of our bond field, as a `Prop`-valued family on the library's pairs. -/
def toProp (ω : Rotor.BondConfig) : Sym2 (LatticeModels.Site 2) → Prop :=
  fun e => e ∈ (zdGraph 2).edgeSet ∧ ω (pairEquiv.symm e) = true

/-- Our bond field read as a bond configuration of the library: the open edges of `ℤ²`. -/
def toConfig (ω : Rotor.BondConfig) : Percolation.Literature.BondConfig (LatticeModels.Site 2) :=
  {e | toProp ω e}

theorem toConfig_eq :
    toConfig = (fun q : Sym2 (LatticeModels.Site 2) → Prop => {e | q e}) ∘ toProp := rfl

theorem pairEquiv_symm_pair (u v : Site) :
    pairEquiv.symm s(siteEquiv u, siteEquiv v) = s(u, v) := by
  simp [pairEquiv, sym2Equiv_symm, sym2Equiv_apply, Sym2.map_mk]

theorem mem_toConfig (ω : Rotor.BondConfig) (u v : Site) :
    s(siteEquiv u, siteEquiv v) ∈ toConfig ω ↔ squareGraph.Adj u v ∧ ω s(u, v) = true := by
  simp only [toConfig, toProp, Set.mem_setOf_eq, SimpleGraph.mem_edgeSet, zd_adj_iff,
    pairEquiv_symm_pair]

/-- A `Prop`-valued edge indicator is measurable. -/
theorem measurable_andEq {α : Type*} [MeasurableSpace α] (P : Prop) (f : α → Bool)
    (hf : Measurable f) : Measurable (fun a => P ∧ f a = true) := by
  apply measurable_to_prop
  by_cases hP : P
  · have h : (fun a => P ∧ f a = true) ⁻¹' {True} = f ⁻¹' {true} := by
      ext a; simp [hP]
    rw [h]; exact hf MeasurableSet.of_discrete
  · have h : (fun a => P ∧ f a = true) ⁻¹' {True} = ∅ := by
      ext a; simp [hP, eq_iff_iff]
    rw [h]; exact MeasurableSet.empty

theorem measurable_toProp : Measurable toProp := by
  exact measurable_pi_lambda _ (fun e => measurable_andEq _ _ (measurable_pi_apply _))

theorem measurable_toConfig : Measurable toConfig := by
  rw [toConfig_eq]; exact measurable_setOf.comp measurable_toProp

/-! ### The one-coordinate laws -/

-- `PMF.bernoulli_apply` is deprecated, but `External.bernoulli` is defined through
-- `PMF.bernoulli` (see `Rotor/External/LSS.lean`), so its evaluation lemma is the one to use.
set_option linter.deprecated false in
theorem bern_eq_smul (p : NNReal) (hp : p ≤ 1) :
    External.bernoulli p hp = p • Measure.dirac true + (1 - p) • Measure.dirac false := by
  rw [Measure.ext_iff_singleton]
  intro b
  have h1 : External.bernoulli p hp {b} = ((cond b p (1 - p) : NNReal) : ℝ≥0∞) := by
    unfold External.bernoulli
    rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete, PMF.bernoulli_apply]
  rw [h1, ENNReal.smul_def, ENNReal.smul_def]
  cases b <;> simp

theorem map_bern (p : NNReal) (hp : p ≤ 1) (P : Prop) :
    (External.bernoulli p hp).map (fun b : Bool => P ∧ b = true) =
      p • Measure.dirac P + (1 - p) • Measure.dirac False := by
  rw [bern_eq_smul, Measure.map_add _ _ Measurable.of_discrete, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac' Measurable.of_discrete,
    Measure.map_dirac' Measurable.of_discrete]
  simp

/-- The parameter as a point of the unit interval. -/
def toI (p : NNReal) (hp : p ≤ 1) : unitInterval := ⟨p, p.2, by exact_mod_cast hp⟩

theorem toNNReal_toI (p : NNReal) (hp : p ≤ 1) : unitInterval.toNNReal (toI p hp) = p := rfl

theorem toNNReal_symm_toI (p : NNReal) (hp : p ≤ 1) :
    unitInterval.toNNReal (unitInterval.symm (toI p hp)) = 1 - p := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sub hp]
  show ((unitInterval.symm (toI p hp) : unitInterval) : ℝ) = 1 - (p : ℝ)
  rw [unitInterval.coe_symm_eq]
  rfl

/-! ### The measure bridge -/

theorem map_toConfig (p : NNReal) (hp : p ≤ 1) :
    (bondLaw p hp).map toConfig = bondPercolation (zdGraph 2) (toI p hp) := by
  unfold bondPercolation
  rw [setBernoulli_eq_map, toConfig_eq, ← Measure.map_map measurable_setOf measurable_toProp]
  congr 1
  have hstep : toProp = (fun χ : Sym2 (LatticeModels.Site 2) → Bool =>
      fun e => (fun b : Bool => e ∈ (zdGraph 2).edgeSet ∧ b = true) (χ e)) ∘
      (fun ω : Sym2 Site → Bool => fun e => ω (pairEquiv.symm e)) := rfl
  have hm1 : Measurable (fun χ : Sym2 (LatticeModels.Site 2) → Bool =>
      fun e => (fun b : Bool => e ∈ (zdGraph 2).edgeSet ∧ b = true) (χ e)) :=
    measurable_pi_lambda _ (fun e => measurable_andEq _ _ (measurable_pi_apply e))
  have hm2 : Measurable (fun ω : Sym2 Site → Bool => fun e => ω (pairEquiv.symm e)) :=
    measurable_pi_lambda _ (fun e => measurable_pi_apply _)
  rw [hstep, ← Measure.map_map hm1 hm2]
  have hre : (fun ω : Sym2 Site → Bool => fun e => ω (pairEquiv.symm e)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : Sym2 (LatticeModels.Site 2) => Bool) pairEquiv) := by
    funext ω e
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  unfold bondLaw
  rw [hre, Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : Sym2 (LatticeModels.Site 2) => External.bernoulli p hp) pairEquiv]
  have hpi := Measure.infinitePi_map_pi
    (μ := fun _ : Sym2 (LatticeModels.Site 2) => External.bernoulli p hp)
    (f := fun (e : Sym2 (LatticeModels.Site 2)) (b : Bool) =>
      (e ∈ (zdGraph 2).edgeSet ∧ b = true : Prop))
    (fun _ => Measurable.of_discrete)
  rw [hpi]
  congr 1
  funext e
  rw [map_bern, toNNReal_toI, toNNReal_symm_toI]

/-! ### Translation and the one-arm event -/

/-- Translation of the library's sites by `-w`. -/
def transl (w : LatticeModels.Site 2) : LatticeModels.Site 2 ≃ LatticeModels.Site 2 :=
  Equiv.addRight (-w)

theorem transl_edge (w : LatticeModels.Site 2) (z : Sym2 (LatticeModels.Site 2)) :
    sym2Equiv (transl w) z ∈ (zdGraph 2).edgeSet ↔ z ∈ (zdGraph 2).edgeSet := by
  induction z using Sym2.ind with
  | h a b =>
    simp only [sym2Equiv_apply, Sym2.map_mk, SimpleGraph.mem_edgeSet, zdGraph_adj_iff, transl,
      Equiv.coe_addRight]
    refine exists_congr (fun i => or_congr ?_ ?_)
    · rw [add_right_comm a, add_left_inj]
    · rw [add_right_comm b, add_left_inj]

/-- The translated configuration. -/
def shifted (x : Site) (ω : Rotor.BondConfig) :
    Percolation.Literature.BondConfig (LatticeModels.Site 2) :=
  BondConfig.relabel (sym2Equiv (transl (siteEquiv x))) (toConfig ω)

theorem transl_symm_apply (x a : Site) :
    (transl (siteEquiv x)).symm (siteEquiv (a - x)) = siteEquiv a := by
  simp [transl, siteEquiv_sub_add]

theorem mem_shifted (x : Site) (ω : Rotor.BondConfig) (a b : Site) :
    s(siteEquiv (a - x), siteEquiv (b - x)) ∈ shifted x ω ↔
      squareGraph.Adj a b ∧ ω s(a, b) = true := by
  unfold shifted
  rw [BondConfig.mem_relabel_iff, sym2Equiv_symm, sym2Equiv_apply, Sym2.map_mk,
    transl_symm_apply, transl_symm_apply, mem_toConfig]

theorem openGraph_shifted_adj (x : Site) (ω : Rotor.BondConfig) {a b : Site}
    (h : squareGraph.Adj a b) (ho : ω s(a, b) = true) :
    (openGraph (shifted x ω)).Adj (siteEquiv (a - x)) (siteEquiv (b - x)) := by
  rw [openGraph_adj, mem_shifted]
  refine ⟨⟨h, ho⟩, fun heq => squareGraph.ne_of_adj h ?_⟩
  have := siteEquiv.injective heq
  exact sub_left_injective this

/-- A list path gives reachability in the induced open graph. -/
theorem reachable_of_chain {W : Type*} {G : SimpleGraph W} {S : Set W} {f : Site → W}
    {l : List Site} (hl : l.IsChain (fun a b => G.Adj (f a) (f b))) (hS : ∀ v ∈ l, f v ∈ S)
    {i : ℕ} (hi : i < l.length) (u v : ↥S) (hu : (u : W) = f (l[0]'(by omega)))
    (hv : (v : W) = f l[i]) : (G.induce S).Reachable u v := by
  have key : ∀ j (hj : j < l.length),
      (G.induce S).Reachable u ⟨f l[j], hS _ (List.getElem_mem hj)⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have : u = ⟨f l[0], hS _ (List.getElem_mem hj)⟩ := Subtype.ext hu
      rw [this]
    | succ j ih =>
      intro hj
      refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
      show (G.comap _).Adj _ _
      rw [SimpleGraph.comap_adj]
      exact (List.isChain_iff_getElem.1 hl) j hj
  have : v = ⟨f l[i], hS _ (List.getElem_mem hi)⟩ := Subtype.ext hv
  rw [this]
  exact key i hi

theorem mem_box_of_linf {x v : Site} {r : ℕ} (h : linfDist v x ≤ r) :
    siteEquiv (v - x) ∈ box 2 r := by
  rw [mem_box]
  unfold linfDist at h
  have h1 := abs_le.1 (le_trans (le_max_left _ _) h)
  have h2 := abs_le.1 (le_trans (le_max_right _ _) h)
  intro i
  fin_cases i <;> simp [siteEquiv_apply] <;> omega

theorem mem_innerBoundary_of_linf {x y : Site} {r : ℕ} (h : linfDist y x = r) :
    siteEquiv (y - x) ∈ innerBoundary (zdGraph 2) (box 2 r) := by
  rw [mem_innerBoundary_iff]
  refine ⟨mem_box_of_linf h.le, ?_⟩
  unfold linfDist at h
  rcases max_choice |y.1 - x.1| |y.2 - x.2| with hm | hm <;> rw [hm] at h
  · rcases (abs_eq (by positivity)).1 h with h' | h'
    · refine ⟨siteEquiv (y - x) + Pi.single 0 1, ?_, (zdGraph_adj_iff _ _).2 ⟨0, Or.inl rfl⟩⟩
      simp only [mem_box, not_forall]
      exact ⟨0, by simp [siteEquiv_apply]; omega⟩
    · refine ⟨siteEquiv (y - x) - Pi.single 0 1, ?_,
        (zdGraph_adj_iff _ _).2 ⟨0, Or.inr (by abel)⟩⟩
      simp only [mem_box, not_forall]
      exact ⟨0, by simp [siteEquiv_apply]; omega⟩
  · rcases (abs_eq (by positivity)).1 h with h' | h'
    · refine ⟨siteEquiv (y - x) + Pi.single 1 1, ?_, (zdGraph_adj_iff _ _).2 ⟨1, Or.inl rfl⟩⟩
      simp only [mem_box, not_forall]
      exact ⟨1, by simp [siteEquiv_apply]; omega⟩
    · refine ⟨siteEquiv (y - x) - Pi.single 1 1, ?_,
        (zdGraph_adj_iff _ _).2 ⟨1, Or.inr (by abel)⟩⟩
      simp only [mem_box, not_forall]
      exact ⟨1, by simp [siteEquiv_apply]; omega⟩

/-- A box crossing from `x` is, after translation, the library's one-arm event. -/
theorem boxCrossing_subset (x : Site) (r : ℕ) :
    boxCrossing x r ⊆ toConfig ⁻¹'
      (BondConfig.relabel (sym2Equiv (transl (siteEquiv x))) ⁻¹' siteToBoundary 2 r) := by
  rintro ω ⟨l, hl, hh, hin, y, hy, hyr⟩
  change shifted x ω ∈ siteToBoundary 2 r
  have hlen : 0 < l.length := by
    rcases l with _ | ⟨a, l⟩
    · simp at hh
    · simp
  have hl0 : l[0] = x := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at hh
    exact Option.some.inj hh
  have hylast : l[l.length - 1] = y := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hy
    exact Option.some.inj hy
  have hS : ∀ v ∈ l, siteEquiv (v - x) ∈ (↑(box 2 r) : Set (LatticeModels.Site 2)) :=
    fun v hv => Finset.mem_coe.2 (mem_box_of_linf (hin v hv))
  have hchain : l.IsChain (fun a b =>
      (openGraph (shifted x ω)).Adj (siteEquiv (a - x)) (siteEquiv (b - x))) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    exact openGraph_shifted_adj x ω ((List.isChain_iff_getElem.1 hl.1.2) i hi)
      ((List.isChain_iff_getElem.1 hl.2) i hi)
  refine ⟨siteEquiv (y - x), mem_innerBoundary_of_linf hyr, ?_⟩
  have h0 : (0 : LatticeModels.Site 2) ∈ (↑(box 2 r) : Set (LatticeModels.Site 2)) := by
    have := hS x (by rw [← hl0]; exact List.getElem_mem hlen)
    rwa [siteEquiv_self_sub] at this
  have hyS : siteEquiv (y - x) ∈ (↑(box 2 r) : Set (LatticeModels.Site 2)) :=
    hS y (by rw [← hylast]; exact List.getElem_mem (by omega))
  refine ⟨h0, hyS, ?_⟩
  exact reachable_of_chain hchain hS (by omega : l.length - 1 < l.length) ⟨0, h0⟩
    ⟨siteEquiv (y - x), hyS⟩ (by simp [hl0, siteEquiv_zero]) (by simp [hylast])

/-! ### The assembly -/

theorem sharpness_bound (p : NNReal) (hp : p ≤ 1) (hlt : p < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      bondPercolation (zdGraph 2) (toI p hp) (siteToBoundary 2 n) ≤ ENNReal.ofReal (Real.exp (-c * n)) := by
  have hk : criticalProb (zdGraph 2) 0 = 1 / 2 := kesten_criticalProb_Z2_holds
  have hpc : ((toI p hp : unitInterval) : ℝ) < criticalProb (zdGraph 2) 0 := by
    rw [hk]
    have : (p : ℝ) < ((1 / 2 : NNReal) : ℝ) := NNReal.coe_lt_coe.2 hlt
    simpa [toI] using this
  have hS : perc_sharpness := Percolation.Literature.DCT16.perc_sharpness_holds
  obtain ⟨c, hc, hbound⟩ := hS (d := 2) le_rfl (toI p hp) hpc
  refine ⟨c, hc, fun n => ?_⟩
  have := hbound n
  rw [measureReal_def] at this
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal this

/-- `External.SubcriticalDecay` holds. -/
theorem subcriticalDecay_holds : External.SubcriticalDecay := by
  intro p hp hlt
  obtain ⟨c, hc, hbound⟩ := sharpness_bound p hp hlt
  refine ⟨c, 1, hc, one_pos, fun x r _ => ?_⟩
  calc bondLaw p hp (boxCrossing x r)
      ≤ bondLaw p hp (toConfig ⁻¹'
          (BondConfig.relabel (sym2Equiv (transl (siteEquiv x))) ⁻¹' siteToBoundary 2 r)) :=
        measure_mono (boxCrossing_subset x r)
    _ ≤ ((bondLaw p hp).map toConfig)
          (BondConfig.relabel (sym2Equiv (transl (siteEquiv x))) ⁻¹' siteToBoundary 2 r) :=
        Measure.le_map_apply measurable_toConfig.aemeasurable _
    _ = bondPercolation (zdGraph 2) (toI p hp) (siteToBoundary 2 r) := by
        rw [map_toConfig]
        unfold bondPercolation
        rw [← MeasurableEquiv.map_apply, setBernoulli_map_relabel _ (transl_edge _)]
    _ ≤ ENNReal.ofReal (1 * Real.exp (-c * r)) := by rw [one_mul]; exact hbound r

end Rotor.Bridge
