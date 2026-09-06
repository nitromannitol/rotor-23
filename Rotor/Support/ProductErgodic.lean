import Rotor.Support.PassageArray
import Rotor.Support.ChainWeight
import Rotor.Support.BlockGeom

/-!
Invariance and ergodicity of product laws under the translation lattice,
`rotor.tex:1494-1496` ("the uniform product law is invariant and ergodic under the
translation lattice") and `rotor.tex:1506-1508` ("If the one-vertex laws are invariant under
the translation lattice, their product law is invariant and ergodic").
-/

open MeasureTheory ProbabilityTheory Finset
open scoped symmDiff

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (P : DoublyPeriodic G)

namespace DoublyPeriodic

/-- The translation by `z` as an equivalence of the vertex set. -/
def shiftVEquiv (z : ℤ × ℤ) : V ≃ V where
  toFun := P.shift z
  invFun := P.shift (-z)
  left_inv := P.shift_shift_neg z
  right_inv := P.shift_neg_shift z

omit [DecidableEq V] [G.LocallyFinite] in
theorem shiftVEquiv_apply (z : ℤ × ℤ) (v : V) : P.shiftVEquiv z v = P.shift z v := rfl

omit [DecidableEq V] [G.LocallyFinite] in
theorem shiftConfig_eq_piCongrLeft (z : ℤ × ℤ) (ρ : Config G) :
    P.shiftConfig z ρ = Equiv.piCongrLeft (fun v => G.neighborSet v) (P.shiftVEquiv z)
      (fun w => P.shiftNbr z (ρ w)) := by
  funext v
  obtain ⟨w, rfl⟩ := (P.shiftVEquiv z).surjective v
  rw [Equiv.piCongrLeft_apply_apply]
  apply Subtype.ext
  show P.shift z (ρ (P.shift (-z) (P.shift z w))).1 = P.shift z (ρ w).1
  congr 1
  exact congrArg (fun u => (ρ u).1) (P.shift_shift_neg z w)

omit [DecidableEq V] [G.LocallyFinite] in
theorem measurable_shiftNbr (z : ℤ × ℤ) (v : V) : Measurable (P.shiftNbr z (v := v)) :=
  measurable_from_top

omit [DecidableEq V] in
/-- A product law with invariant marginals is invariant. -/
theorem productLaw_invariant (ν : ∀ v : V, Measure (G.neighborSet v))
    [∀ v, IsProbabilityMeasure (ν v)] (hν : P.InvariantMarginals ν) :
    P.Invariant (productLaw ν) := by
  intro z
  refine ⟨P.measurable_shiftConfig z, ?_⟩
  have hfun : P.shiftConfig z =
      (MeasurableEquiv.piCongrLeft (fun v => G.neighborSet v) (P.shiftVEquiv z)) ∘
        (fun ρ w => P.shiftNbr z (ρ w)) := by
    funext ρ
    rw [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft]
    exact P.shiftConfig_eq_piCongrLeft z ρ
  have hf : Measurable (fun ρ : Config G => fun w => P.shiftNbr z (ρ w)) :=
    measurable_pi_lambda _ (fun w => (P.measurable_shiftNbr z w).comp (measurable_pi_apply w))
  unfold productLaw
  rw [hfun, ← Measure.map_map
    (g := ⇑(MeasurableEquiv.piCongrLeft (fun v => G.neighborSet v) (P.shiftVEquiv z)))
    (f := fun ρ : Config G => fun w => P.shiftNbr z (ρ w))
    (MeasurableEquiv.piCongrLeft (fun v => G.neighborSet v) (P.shiftVEquiv z)).measurable hf,
    Measure.infinitePi_map_pi (μ := ν) (f := fun w a => P.shiftNbr z a)
      (fun w => P.measurable_shiftNbr z w)]
  have : (fun w => (ν w).map (P.shiftNbr z)) = fun w => ν (P.shiftVEquiv z w) :=
    funext (fun w => hν z w)
  rw [this, Measure.infinitePi_map_piCongrLeft]

/-- The translation as an equivalence of neighbour sets. -/
def shiftNbrEquiv (z : ℤ × ℤ) (v : V) : G.neighborSet v ≃ G.neighborSet (P.shift z v) where
  toFun := P.shiftNbr z
  invFun a := ⟨P.shift (-z) a.1, by
    have := (P.adj_shift (-z) _ _).2 a.2
    rwa [P.shift_shift_neg] at this⟩
  left_inv a := by
    apply Subtype.ext
    show P.shift (-z) (P.shift z a.1) = a.1
    exact P.shift_shift_neg z a.1
  right_inv a := by
    apply Subtype.ext
    show P.shift z (P.shift (-z) a.1) = a.1
    exact P.shift_neg_shift z a.1

omit [DecidableEq V] in
/-- The uniform one-vertex laws are invariant. -/
theorem uniformAt_invariantMarginals (π : Mechanism G) : P.InvariantMarginals (uniformAt π) := by
  intro z v
  haveI := π.nonempty v
  haveI := π.nonempty (P.shift z v)
  refine Measure.ext_iff_singleton.2 (fun a => ?_)
  rw [Measure.map_apply (P.measurable_shiftNbr z v) (measurableSet_singleton a)]
  have hpre : P.shiftNbr z ⁻¹' {a} = {(P.shiftNbrEquiv z v).symm a} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h]; exact ((P.shiftNbrEquiv z v).symm_apply_apply b).symm
    · intro h; rw [h]; exact (P.shiftNbrEquiv z v).apply_symm_apply a
  rw [hpre]
  unfold uniformAt
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
    Fintype.card_congr (P.shiftNbrEquiv z v)]

end DoublyPeriodic

section Approx

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Events determined by disjoint finite sets of coordinates are independent. -/
theorem infinitePi_inter_of_disjoint (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, MeasurableSingletonClass (X i)] [∀ i, Finite (X i)]
    (S T : Finset ι) (hST : Disjoint S T) {A B : Set (∀ i, X i)} (hA : DeterminedBy (↑S) A)
    (hB : DeterminedBy (↑T) B) :
    Measure.infinitePi μ (A ∩ B) = Measure.infinitePi μ A * Measure.infinitePi μ B := by
  classical
  have hind := indepFun_of_disjoint μ S T hST id measurable_id id measurable_id
  have hSA : MeasurableSet (S.restrict '' A) := (Set.toFinite _).measurableSet
  have hTB : MeasurableSet (T.restrict '' B) := (Set.toFinite _).measurableSet
  have h1 := hind.measure_inter_preimage_eq_mul _ _ hSA hTB
  change Measure.infinitePi μ (S.restrict ⁻¹' (S.restrict '' A) ∩ T.restrict ⁻¹' (T.restrict '' B))
    = Measure.infinitePi μ (S.restrict ⁻¹' (S.restrict '' A)) *
      Measure.infinitePi μ (T.restrict ⁻¹' (T.restrict '' B)) at h1
  rwa [hA.preimage_image S, hB.preimage_image T] at h1

theorem biUnion_range_mem_measurableCylinders (c : ℕ → Set (∀ i, X i))
    (hc : ∀ i, c i ∈ measurableCylinders X) :
    ∀ n : ℕ, ⋃ i ∈ Finset.range n, c i ∈ measurableCylinders X
  | 0 => by simpa using empty_mem_measurableCylinders X
  | n + 1 => by
    rw [Finset.range_add_one, Finset.set_biUnion_insert]
    exact union_mem_measurableCylinders (hc n) (biUnion_range_mem_measurableCylinders c hc n)

/-- Every measurable set of a finite measure on a product is approximated in measure by
cylinders. -/
theorem exists_cylinder_approx (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ] :
    ∀ (s : Set (∀ i, X i)), MeasurableSet s → ∀ ε : ENNReal, 0 < ε →
      ∃ c ∈ measurableCylinders X, μ (s ∆ c) ≤ ε := by
  refine MeasurableSpace.induction_on_inter (C := fun s _ => ∀ ε : ENNReal, 0 < ε →
      ∃ c ∈ measurableCylinders X, μ (s ∆ c) ≤ ε)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_ ?_ ?_
  · intro ε _
    exact ⟨∅, empty_mem_measurableCylinders X, by simp⟩
  · intro t ht ε _
    exact ⟨t, ht, by simp⟩
  · intro t _ ih ε hε
    obtain ⟨c, hc, hle⟩ := ih ε hε
    exact ⟨cᶜ, compl_mem_measurableCylinders hc, by rwa [compl_symmDiff_compl]⟩
  · intro f hd hfm ih ε hε
    have hsum : ∑' i, μ (f i) ≠ ⊤ := by
      rw [← measure_iUnion hd hfm]; exact measure_ne_top _ _
    have htail := ENNReal.tendsto_sum_nat_add (fun i => μ (f i)) hsum
    have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    obtain ⟨n, hn⟩ := (htail.eventually (gt_mem_nhds hε2)).exists
    set δ : ENNReal := ε / 2 / (n + 1) with hδ
    have hδpos : 0 < δ := ENNReal.div_pos_iff.2 ⟨hε2.ne', by simp⟩
    choose c hc hcle using fun i => ih i δ hδpos
    refine ⟨⋃ i ∈ Finset.range n, c i, biUnion_range_mem_measurableCylinders c hc n, ?_⟩
    have hsub : (⋃ i, f i) ∆ (⋃ i ∈ Finset.range n, c i) ⊆
        (⋃ i, f (i + n)) ∪ ⋃ i ∈ Finset.range n, (f i ∆ c i) := by
      intro x hx
      rcases Set.mem_symmDiff.1 hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx1
        rcases Nat.lt_or_ge i n with hin | hin
        · refine Or.inr (Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hin, ?_⟩)
          exact Set.mem_symmDiff.2 (Or.inl ⟨hi, fun h => hx2 (Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hin, h⟩)⟩)
        · refine Or.inl (Set.mem_iUnion.2 ⟨i - n, ?_⟩)
          rw [Nat.sub_add_cancel hin]; exact hi
      · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx1
        refine Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, ?_⟩)
        exact Set.mem_symmDiff.2 (Or.inr ⟨hxi, fun h => hx2 (Set.mem_iUnion.2 ⟨i, h⟩)⟩)
    have hn1 : (n : ENNReal) + 1 ≠ 0 := by simp
    have hn2 : (n : ENNReal) + 1 ≠ ⊤ := by simp
    calc μ ((⋃ i, f i) ∆ ⋃ i ∈ Finset.range n, c i)
        ≤ μ ((⋃ i, f (i + n)) ∪ ⋃ i ∈ Finset.range n, (f i ∆ c i)) := measure_mono hsub
      _ ≤ μ (⋃ i, f (i + n)) + μ (⋃ i ∈ Finset.range n, (f i ∆ c i)) := measure_union_le _ _
      _ ≤ (∑' i, μ (f (i + n))) + ∑ i ∈ Finset.range n, μ (f i ∆ c i) :=
          add_le_add (measure_iUnion_le _) (measure_biUnion_finset_le _ _)
      _ ≤ ε / 2 + ∑ i ∈ Finset.range n, δ :=
          add_le_add hn.le (Finset.sum_le_sum (fun i _ => hcle i))
      _ ≤ ε / 2 + ((n : ENNReal) + 1) * δ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          gcongr
          exact le_self_add
      _ = ε := by
          rw [hδ, ENNReal.mul_div_cancel' (fun h => absurd h hn1) (fun h => absurd h hn2),
            ENNReal.add_halves]

end Approx

section Ergodic

namespace DoublyPeriodic

omit [G.LocallyFinite] in
/-- The preimage under a translation of an event determined by `F` is determined by the
translated coordinates. -/
theorem shiftConfig_preimage_determined (z : ℤ × ℤ) (F : Finset V) {A : Set (Config G)}
    (hA : DeterminedBy (↑F) A) :
    DeterminedBy (↑(F.image (P.shift (-z)))) (P.shiftConfig z ⁻¹' A) := by
  intro ρ ρ' h hρ
  refine hA (P.shiftConfig z ρ) (P.shiftConfig z ρ') (fun v hv => ?_) hρ
  have := h (P.shift (-z) v) (by rw [Finset.coe_image]; exact ⟨v, hv, rfl⟩)
  apply Subtype.ext
  show P.shift z (ρ (P.shift (-z) v)).1 = P.shift z (ρ' (P.shift (-z) v)).1
  rw [this]

omit [G.LocallyFinite] in
/-- A translation far enough moves a finite set of vertices off itself. -/
theorem exists_shift_disjoint (F : Finset V) :
    ∃ z : ℤ × ℤ, Disjoint F (F.image (P.shift (-z))) := by
  obtain ⟨K, hK⟩ := ((F ×ˢ F).image (fun p => |(P.coord p.1).1 - (P.coord p.2).1|)).bddAbove
  have hK' : ∀ u ∈ F, ∀ w ∈ F, |(P.coord u).1 - (P.coord w).1| ≤ K := fun u hu w hw =>
    hK (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(u, w), Finset.mem_product.2 ⟨hu, hw⟩, rfl⟩))
  refine ⟨(K + 1, 0), Finset.disjoint_left.2 (fun v hv hv' => ?_)⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv'
  have h0 : (0 : ℤ) ≤ K := (abs_nonneg _).trans (hK' u hu u hu)
  have := hK' u hu _ hv
  rw [P.coord_shift] at this
  simp only [Prod.fst_add, Prod.fst_neg] at this
  rw [show (P.coord u).1 - (-(K + 1) + (P.coord u).1) = K + 1 by ring,
    abs_of_nonneg (by omega)] at this
  omega

variable {ν : ∀ v : V, Measure (G.neighborSet v)} [∀ v, IsProbabilityMeasure (ν v)]

/-- Mixing on cylinders: a far translate of a cylinder is independent of it. -/
theorem exists_measure_inter_shift_eq_mul (hinv : P.Invariant (productLaw ν)) {c : Set (Config G)}
    (hc : c ∈ measurableCylinders (fun v => G.neighborSet v)) :
    ∃ z : ℤ × ℤ, productLaw ν (c ∩ P.shiftConfig z ⁻¹' c) = productLaw ν c * productLaw ν c := by
  obtain ⟨F, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hc
  have hdet : DeterminedBy (↑F) (cylinder (α := fun v => G.neighborSet v) F S) :=
    fun ρ ρ' h hρ => by
    show F.restrict ρ' ∈ S
    have : F.restrict ρ' = F.restrict ρ := funext (fun i => (h i i.2).symm)
    rw [this]; exact hρ
  obtain ⟨z, hz⟩ := P.exists_shift_disjoint F
  refine ⟨z, ?_⟩
  rw [productLaw, infinitePi_inter_of_disjoint ν F _ hz hdet
    (P.shiftConfig_preimage_determined z F hdet), ← productLaw,
    (hinv z).measure_preimage hS.cylinder.nullMeasurableSet]

/-- An invariant product law is ergodic. -/
theorem productLaw_ergodic (hinv : P.Invariant (productLaw ν)) : P.Ergodic (productLaw ν) := by
  intro s hs hsinv
  set μ := productLaw ν with hμ
  have ha1 : μ s ≤ 1 := prob_le_one
  -- for every small ε, |μ s - (μ s)²| ≤ 5 ε
  have key : ∀ ε : ENNReal, 0 < ε → ε ≤ 1 →
      μ s ≤ μ s * μ s + 5 * ε ∧ μ s * μ s ≤ μ s + 5 * ε := by
    intro ε hε hε1
    obtain ⟨c, hc, hd⟩ := exists_cylinder_approx μ s hs ε hε
    obtain ⟨z, hz⟩ := P.exists_measure_inter_shift_eq_mul hinv hc
    have hcm : MeasurableSet c := by
      obtain ⟨F, S, hS, hcF⟩ := (mem_measurableCylinders _).1 hc
      rw [hcF]; exact hS.cylinder
    set d := μ (s ∆ c) with hddef
    have hd1 : d ≤ 1 := hd.trans hε1
    have hb1 : μ c ≤ 1 := prob_le_one
    have hpre : μ (P.shiftConfig z ⁻¹' (s ∆ c)) = d :=
      (hinv z).measure_preimage (hs.symmDiff hcm).nullMeasurableSet
    -- (ii): μ s ≤ μ c * μ c + 2 d
    have h2 : μ s ≤ μ c * μ c + 2 * d := by
      have hsub : s ∩ P.shiftConfig z ⁻¹' s ⊆
          (c ∩ P.shiftConfig z ⁻¹' c) ∪ (s ∆ c) ∪ P.shiftConfig z ⁻¹' (s ∆ c) := by
        rintro x ⟨hxs, hxs'⟩
        by_cases hxc : x ∈ c
        · by_cases hxc' : P.shiftConfig z x ∈ c
          · exact Or.inl (Or.inl ⟨hxc, hxc'⟩)
          · exact Or.inr (Set.mem_symmDiff.2 (Or.inl ⟨hxs', hxc'⟩))
        · exact Or.inl (Or.inr (Set.mem_symmDiff.2 (Or.inl ⟨hxs, hxc⟩)))
      calc μ s = μ (s ∩ P.shiftConfig z ⁻¹' s) := by rw [hsinv z, Set.inter_self]
        _ ≤ μ ((c ∩ P.shiftConfig z ⁻¹' c) ∪ (s ∆ c) ∪ P.shiftConfig z ⁻¹' (s ∆ c)) :=
            measure_mono hsub
        _ ≤ μ ((c ∩ P.shiftConfig z ⁻¹' c) ∪ (s ∆ c)) + μ (P.shiftConfig z ⁻¹' (s ∆ c)) :=
            measure_union_le _ _
        _ ≤ μ (c ∩ P.shiftConfig z ⁻¹' c) + μ (s ∆ c) + μ (P.shiftConfig z ⁻¹' (s ∆ c)) :=
            add_le_add (measure_union_le _ _) le_rfl
        _ = μ c * μ c + 2 * d := by rw [hz, hpre, ← hddef]; ring
    -- (iii): μ c * μ c ≤ μ s + 2 d
    have h3 : μ c * μ c ≤ μ s + 2 * d := by
      have hsub : c ∩ P.shiftConfig z ⁻¹' c ⊆
          (s ∩ P.shiftConfig z ⁻¹' s) ∪ (s ∆ c) ∪ P.shiftConfig z ⁻¹' (s ∆ c) := by
        rintro x ⟨hxc, hxc'⟩
        by_cases hxs : x ∈ s
        · by_cases hxs' : P.shiftConfig z x ∈ s
          · exact Or.inl (Or.inl ⟨hxs, hxs'⟩)
          · exact Or.inr (Set.mem_symmDiff.2 (Or.inr ⟨hxc', hxs'⟩))
        · exact Or.inl (Or.inr (Set.mem_symmDiff.2 (Or.inr ⟨hxc, hxs⟩)))
      calc μ c * μ c = μ (c ∩ P.shiftConfig z ⁻¹' c) := hz.symm
        _ ≤ μ ((s ∩ P.shiftConfig z ⁻¹' s) ∪ (s ∆ c) ∪ P.shiftConfig z ⁻¹' (s ∆ c)) :=
            measure_mono hsub
        _ ≤ μ ((s ∩ P.shiftConfig z ⁻¹' s) ∪ (s ∆ c)) + μ (P.shiftConfig z ⁻¹' (s ∆ c)) :=
            measure_union_le _ _
        _ ≤ μ (s ∩ P.shiftConfig z ⁻¹' s) + μ (s ∆ c) + μ (P.shiftConfig z ⁻¹' (s ∆ c)) :=
            add_le_add (measure_union_le _ _) le_rfl
        _ = μ s + 2 * d := by rw [hsinv z, Set.inter_self, hpre, ← hddef]; ring
    -- (iv): |μ s - μ c| ≤ d
    have h4 : μ c ≤ μ s + d := by
      calc μ c ≤ μ (s ∪ (s ∆ c)) := measure_mono (fun x hx => by
            by_cases hxs : x ∈ s
            · exact Or.inl hxs
            · exact Or.inr (Set.mem_symmDiff.2 (Or.inr ⟨hx, hxs⟩)))
        _ ≤ μ s + d := measure_union_le _ _
    have h5 : μ s ≤ μ c + d := by
      calc μ s ≤ μ (c ∪ (s ∆ c)) := measure_mono (fun x hx => by
            by_cases hxc : x ∈ c
            · exact Or.inl hxc
            · exact Or.inr (Set.mem_symmDiff.2 (Or.inl ⟨hx, hxc⟩)))
        _ ≤ μ c + d := measure_union_le _ _
    have hsq : ∀ a b : ENNReal, a ≤ 1 → b ≤ 1 → (a + b) * (a + b) ≤ a * a + 3 * b := by
      intro a b ha hb
      calc (a + b) * (a + b) = a * a + a * b + b * a + b * b := by ring
        _ ≤ a * a + b + b + b := by
            gcongr
            · exact (mul_le_mul' ha le_rfl).trans (one_mul b).le
            · exact (mul_le_mul' le_rfl ha).trans (mul_one b).le
            · exact (mul_le_mul' hb le_rfl).trans (one_mul b).le
        _ = a * a + 3 * b := by ring
    refine ⟨?_, ?_⟩
    · calc μ s ≤ μ c * μ c + 2 * d := h2
        _ ≤ (μ s + d) * (μ s + d) + 2 * d := by gcongr
        _ ≤ μ s * μ s + 3 * d + 2 * d := by gcongr; exact hsq _ _ ha1 hd1
        _ = μ s * μ s + 5 * d := by ring
        _ ≤ μ s * μ s + 5 * ε := by gcongr
    · calc μ s * μ s ≤ (μ c + d) * (μ c + d) := by gcongr
        _ ≤ μ c * μ c + 3 * d := hsq _ _ hb1 hd1
        _ ≤ μ s + 2 * d + 3 * d := by gcongr
        _ = μ s + 5 * d := by ring
        _ ≤ μ s + 5 * ε := by gcongr
  have heq : μ s = μ s * μ s := by
    apply le_antisymm
    · refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
      have hε' : (0 : ENNReal) < min ((ε : ENNReal) / 5) 1 :=
        lt_min (ENNReal.div_pos_iff.2 ⟨by exact_mod_cast hε.ne', by norm_num⟩) one_pos
      calc μ s ≤ μ s * μ s + 5 * min ((ε : ENNReal) / 5) 1 := (key _ hε' (min_le_right _ _)).1
        _ ≤ μ s * μ s + 5 * ((ε : ENNReal) / 5) := by gcongr; exact min_le_left _ _
        _ = μ s * μ s + ε := by rw [ENNReal.mul_div_cancel' (by norm_num) (by norm_num)]
    · refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
      have hε' : (0 : ENNReal) < min ((ε : ENNReal) / 5) 1 :=
        lt_min (ENNReal.div_pos_iff.2 ⟨by exact_mod_cast hε.ne', by norm_num⟩) one_pos
      calc μ s * μ s ≤ μ s + 5 * min ((ε : ENNReal) / 5) 1 := (key _ hε' (min_le_right _ _)).2
        _ ≤ μ s + 5 * ((ε : ENNReal) / 5) := by gcongr; exact min_le_left _ _
        _ = μ s + ε := by rw [ENNReal.mul_div_cancel' (by norm_num) (by norm_num)]
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · exact Or.inl h0
  · right
    exact (ENNReal.mul_right_inj h0 (measure_ne_top _ _)).1 (heq.symm.trans (mul_one _).symm)

omit [DecidableEq V] in
/-- The uniform product law is invariant. -/
theorem uniformLaw_invariant (π : Mechanism G) : P.Invariant (uniformLaw π) :=
  P.productLaw_invariant (uniformAt π) (P.uniformAt_invariantMarginals π)

/-- The uniform product law is ergodic. -/
theorem uniformLaw_ergodic (π : Mechanism G) : P.Ergodic (uniformLaw π) :=
  P.productLaw_ergodic (P.uniformLaw_invariant π)

end DoublyPeriodic

end Ergodic



end Rotor
