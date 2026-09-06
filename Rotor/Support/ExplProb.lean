import Rotor.Support.ExplInv
import Rotor.Support.SideCount
import Rotor.Support.ChainWeight

/-!
Lemma 5.4 (iii) (`rotor.tex:1910-1913`): given the outcomes of all earlier tests, the current
edge `E` is open with probability `1`, `0` or `1/2` according as its opposite side `W` was
tested closed, tested open, or not tested.  The event that the first `n` outcomes are `h` is
the intersection over the tests of `replay f d h` of the events that the tested dual edge has
the recorded state (`history_event`); each such event depends on the rotor at one lattice
vertex, the primal tail of the edge, so the product law factorizes over vertices
(`infinitePi_eval_inter`), and at the vertex of `E` the computation is the finite check of
`SideCount.lean`.
-/

open Finset MeasureTheory ENNReal

namespace Rotor

/-- The current edge of a state (junk when the active list is empty). -/
def curEdge (s : ExplState) : Site × Site := s.active.headD ((0, 0), (0, 0))

theorem curEdge_eq {s : ExplState} {e : Site × Site} {rest : List (Site × Site)}
    (h : s.active = e :: rest) : curEdge s = e := by
  rw [curEdge, h, List.headD_cons]

open Classical in
/-- The outcome of the next test under `ρ` from the state after the outcomes `h`. -/
noncomputable def outcome (ρ : Config squareGraph) (f d : Site) (h : List Bool) : Bool :=
  decide (DualOpen ρ (curEdge (replay f d h)).1 (curEdge (replay f d h)).2)

theorem replay_active_ne_nil_of_append (f d : Site) (h : List Bool) (o : Bool)
    (hne : (replay f d (h ++ [o])).active ≠ []) : (replay f d h).active ≠ [] := by
  intro h0
  apply hne
  rw [replay_append, explStepWith_nil h0]
  exact h0

theorem replay_active_ne_nil_of_take (f d : Site) (h : List Bool) (hne : (replay f d h).active ≠ [])
    (i : ℕ) : (replay f d (h.take i)).active ≠ [] := by
  intro h0
  apply hne
  have : h = h.take i ++ h.drop i := (List.take_append_drop i h).symm
  rw [this]
  unfold replay
  rw [List.foldl_append]
  have hfix : ∀ (l : List Bool) (s : ExplState), s.active = [] → (l.foldl explStepWith s).active = [] := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons o l ih =>
      intro s hs
      rw [List.foldl_cons, explStepWith_nil hs]
      exact ih s hs
  exact hfix _ _ h0

open Classical in
/-- The next outcome extends the history. -/
theorem history_append_iff (ρ : Config squareGraph) (f d : Site) (h : List Bool) (o : Bool)
    (hne : (replay f d h).active ≠ []) :
    history ρ f d (h.length + 1) = h ++ [o] ↔
      history ρ f d h.length = h ∧ outcome ρ f d h = o := by
  constructor
  · intro heq
    rcases hact : (explore ρ f d h.length).active with _ | ⟨e, rest⟩
    · exfalso
      rw [history_succ_nil ρ f d _ hact] at heq
      have := history_length_le ρ f d h.length
      rw [heq, List.length_append, List.length_singleton] at this
      omega
    · rw [history_succ_cons ρ f d _ hact] at heq
      have h1 : history ρ f d h.length = h := List.append_inj_left' heq (by simp)
      have h2 : [decide (DualOpen ρ e.1 e.2)] = [o] := List.append_inj_right' heq (by simp)
      simp only [List.cons.injEq, and_true] at h2
      refine ⟨h1, ?_⟩
      have hcur : curEdge (replay f d h) = e := by
        rw [← h1, ← explore_eq_replay]
        exact curEdge_eq hact
      rw [outcome, hcur]
      exact h2
  · rintro ⟨h1, h2⟩
    rcases hh : (replay f d h).active with _ | ⟨e, rest⟩
    · exact absurd hh hne
    have hact : (explore ρ f d h.length).active = e :: rest := by
      rw [explore_eq_replay, h1, hh]
    rw [history_succ_cons ρ f d _ hact, h1, ← h2, outcome, curEdge_eq hh]

open Classical in
/-- The event that the tests in `C` had the recorded outcomes. -/
def testEvent (C : List (Site × Site × Bool)) : Set (Config squareGraph) :=
  {ρ | ∀ t ∈ C, decide (DualOpen ρ t.1 t.2.1) = t.2.2}

theorem testEvent_nil : testEvent [] = Set.univ := by
  ext ρ; simp [testEvent]

open Classical in
/-- The event that the first `h.length` outcomes are `h`. -/
theorem history_event (f d : Site) : ∀ (h : List Bool),
    (∀ i < h.length, (replay f d (h.take i)).active ≠ []) →
      {ρ | history ρ f d h.length = h} = testEvent (replay f d h).tested := by
  intro h
  induction h using List.reverseRecOn with
  | nil =>
    intro _
    ext ρ
    simp [testEvent, history, explore_zero, explInit, replay]
  | append_singleton h o ih =>
    intro hpre
    have hne : (replay f d h).active ≠ [] := by
      have := hpre h.length (by simp)
      rwa [List.take_left'] at this
      rfl
    have ih' := ih (fun i hi => by
      have := hpre i (by simp; omega)
      rwa [List.take_append_of_le_length hi.le] at this)
    ext ρ
    simp only [Set.mem_setOf_eq, List.length_append, List.length_singleton]
    rw [history_append_iff ρ f d h o hne]
    have hmem : ρ ∈ {ρ | history ρ f d h.length = h} ↔ ρ ∈ testEvent (replay f d h).tested := by
      rw [ih']
    simp only [Set.mem_setOf_eq] at hmem
    rw [hmem, replay_append]
    rcases hh : (replay f d h).active with _ | ⟨e, rest⟩
    · exact absurd hh hne
    rw [explStepWith_cons hh]
    have hout : outcome ρ f d h = decide (DualOpen ρ e.1 e.2) := by rw [outcome, curEdge_eq hh]
    rw [hout]
    simp only [testEvent, Set.mem_setOf_eq, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩ t ht
      rcases ht with ht | rfl
      · exact h1 t ht
      · exact h2
    · intro h1
      exact ⟨fun t ht => h1 t (Or.inl ht), h1 (e.1, e.2, o) (Or.inr rfl)⟩

/-! ### Factorization over vertices -/

/-- The primal tail of a test. -/
def tailOf (t : Site × Site × Bool) : Site := primalTail t.1 t.2.1

theorem testEvent_split (C : List (Site × Site × Bool)) (v : Site) :
    testEvent C = testEvent (C.filter (fun t => tailOf t = v)) ∩
      testEvent (C.filter (fun t => tailOf t ≠ v)) := by
  ext ρ
  simp only [testEvent, Set.mem_setOf_eq, Set.mem_inter_iff, List.mem_filter, decide_eq_true_eq,
    and_imp]
  constructor
  · intro h
    exact ⟨fun t ht _ => h t ht, fun t ht _ => h t ht⟩
  · rintro ⟨h1, h2⟩ t ht
    by_cases hv : tailOf t = v
    · exact h1 t ht hv
    · exact h2 t ht hv

theorem dualOpen_iff_openAt' (ρ : Config squareGraph) {t : Site × Site × Bool}
    (hadj : squareGraph.Adj t.1 t.2.1) :
    DualOpen ρ t.1 t.2.1 ↔ openAt (primalDir t.1 t.2.1) (dir0 ρ (tailOf t)) = true := by
  have := dualOpen_iff_openAt ρ (tailOf t) (primalDir t.1 t.2.1)
  rw [tailOf, dualEdge_primal hadj] at this
  rw [this]
  rfl

open Classical in
theorem testEvent_at (C : List (Site × Site × Bool)) (v : Site)
    (hC : ∀ t ∈ C, tailOf t = v) (hadj : ∀ t ∈ C, squareGraph.Adj t.1 t.2.1) :
    testEvent C = (fun ρ : Config squareGraph => ρ v) ⁻¹'
      {x | ∀ t ∈ C, openAt (primalDir t.1 t.2.1) ((nbr v).symm x) = t.2.2} := by
  ext ρ
  simp only [testEvent, Set.mem_setOf_eq, Set.mem_preimage]
  refine forall₂_congr (fun t ht => ?_)
  have h1 := dualOpen_iff_openAt' ρ (hadj t ht)
  rw [hC t ht] at h1
  rw [dir0] at h1
  have h2 : decide (DualOpen ρ t.1 t.2.1) =
      decide (openAt (primalDir t.1 t.2.1) ((nbr v).symm (ρ v)) = true) := decide_eq_decide.2 h1
  rw [h2, Bool.decide_eq_true]

open Classical in
theorem testEvent_determined (C : List (Site × Site × Bool))
    (hadj : ∀ t ∈ C, squareGraph.Adj t.1 t.2.1) :
    DeterminedBy ↑((C.map tailOf).toFinset) (testEvent C) := by
  intro ρ ρ' hρ hmem t ht
  have hv : tailOf t ∈ ((C.map tailOf).toFinset : Set Site) := by
    rw [mem_coe, List.mem_toFinset]
    exact List.mem_map.2 ⟨t, ht, rfl⟩
  have h1 := dualOpen_iff_openAt' ρ (hadj t ht)
  have h2 := dualOpen_iff_openAt' ρ' (hadj t ht)
  have hd : dir0 ρ (tailOf t) = dir0 ρ' (tailOf t) := by
    rw [dir0, dir0, hρ _ hv]
  rw [← hmem t ht]
  apply decide_eq_decide.2
  rw [h1, h2, hd]

/-- The uniform law at `v` of a set described by the initial rotor direction. -/
theorem uniformAt_dir (v : Site) (Q : Dir → Prop) [DecidablePred Q] :
    uniformAt clockwise v {x | Q ((nbr v).symm x)} = ((univ.filter Q).card : ℝ≥0∞) / 4 := by
  have hset : {x : squareGraph.neighborSet v | Q ((nbr v).symm x)} =
      ↑(univ.filter (fun x : squareGraph.neighborSet v => Q ((nbr v).symm x))) := by
    ext x; simp
  unfold uniformAt
  rw [hset, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, sum_const, nsmul_eq_mul,
    SimpleGraph.card_neighborSet_eq_degree, squareGraph_degree]
  rw [Finset.card_equiv (nbr v).symm (t := univ.filter Q) (fun x => by simp)]
  rw [div_eq_mul_inv]
  push_cast
  rfl

/-- The probability that the current edge is open given the earlier tests: the three cases. -/
theorem testEvent_inter_open (C : List (Site × Site × Bool))
    (hadj : ∀ t ∈ C, squareGraph.Adj t.1 t.2.1)
    (e : Site × Site) (he : squareGraph.Adj e.1 e.2)
    (hnot : ∀ t ∈ C, bond e ≠ bond (t.1, t.2.1)) :
    let v := primalTail e.1 e.2
    let a := primalDir e.1 e.2
    (((dualEdge v (a + 2)).1, (dualEdge v (a + 2)).2, false) ∈ C →
      uniformLaw clockwise (testEvent C ∩ {ρ | DualOpen ρ e.1 e.2}) =
        uniformLaw clockwise (testEvent C)) ∧
    (((dualEdge v (a + 2)).1, (dualEdge v (a + 2)).2, true) ∈ C →
      uniformLaw clockwise (testEvent C ∩ {ρ | DualOpen ρ e.1 e.2}) = 0) ∧
    (((dualEdge v (a + 2)).1, (dualEdge v (a + 2)).2, false) ∉ C →
      ((dualEdge v (a + 2)).1, (dualEdge v (a + 2)).2, true) ∉ C →
      uniformLaw clockwise (testEvent C ∩ {ρ | DualOpen ρ e.1 e.2}) =
        2⁻¹ * uniformLaw clockwise (testEvent C)) := by
  classical
  intro v a
  have hev : e = dualEdge v a := (dualEdge_primal he).symm
  set Cv := C.filter (fun t => tailOf t = v) with hCv
  set Cr := C.filter (fun t => tailOf t ≠ v) with hCr
  have hCv_tail : ∀ t ∈ Cv, tailOf t = v := fun t ht => by
    rw [hCv, List.mem_filter] at ht; simpa using ht.2
  have hCv_adj : ∀ t ∈ Cv, squareGraph.Adj t.1 t.2.1 := fun t ht =>
    hadj t (List.mem_of_mem_filter ht)
  have hCr_adj : ∀ t ∈ Cr, squareGraph.Adj t.1 t.2.1 := fun t ht =>
    hadj t (List.mem_of_mem_filter ht)
  have hvT : v ∉ (Cr.map tailOf).toFinset := by
    rw [List.mem_toFinset, List.mem_map]
    rintro ⟨t, ht, htv⟩
    rw [hCr, List.mem_filter] at ht
    simp only [decide_eq_true_eq] at ht
    exact ht.2 htv
  -- the set at `v`
  set Q : Dir → Prop := fun dd => ∀ t ∈ Cv, openAt (primalDir t.1 t.2.1) dd = t.2.2 with hQ
  have hopen : {ρ : Config squareGraph | DualOpen ρ e.1 e.2} =
      (fun ρ : Config squareGraph => ρ v) ⁻¹' {x | openAt a ((nbr v).symm x) = true} := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [hev, dualOpen_iff_openAt]
    rfl
  have hsplit : testEvent C = (fun ρ : Config squareGraph => ρ v) ⁻¹' {x | Q ((nbr v).symm x)} ∩
      testEvent Cr := by
    rw [testEvent_split C v, ← hCv, ← hCr, testEvent_at Cv v hCv_tail hCv_adj]
  have hdet := testEvent_determined Cr hCr_adj
  have key1 : uniformLaw clockwise (testEvent C ∩ {ρ | DualOpen ρ e.1 e.2}) =
      uniformAt clockwise v {x | Q ((nbr v).symm x) ∧ openAt a ((nbr v).symm x) = true} *
        uniformLaw clockwise (testEvent Cr) := by
    rw [hsplit, hopen]
    have : (fun ρ : Config squareGraph => ρ v) ⁻¹' {x | Q ((nbr v).symm x)} ∩ testEvent Cr ∩
        (fun ρ : Config squareGraph => ρ v) ⁻¹' {x | openAt a ((nbr v).symm x) = true} =
        (fun ρ : Config squareGraph => ρ v) ⁻¹'
          {x | Q ((nbr v).symm x) ∧ openAt a ((nbr v).symm x) = true} ∩ testEvent Cr := by
      ext ρ; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]; tauto
    rw [this]
    exact infinitePi_eval_inter (μ := uniformAt clockwise) v _ _ hvT hdet
  have key2 : uniformLaw clockwise (testEvent C) =
      uniformAt clockwise v {x | Q ((nbr v).symm x)} * uniformLaw clockwise (testEvent Cr) := by
    rw [hsplit]
    exact infinitePi_eval_inter (μ := uniformAt clockwise) v _ _ hvT hdet
  have hW : ∀ o : Bool, ((dualEdge v (a + 2)).1, (dualEdge v (a + 2)).2, o) ∈ C →
      ((dualEdge v (a + 2)).1, (dualEdge v (a + 2)).2, o) ∈ Cv := by
    intro o ho
    rw [hCv, List.mem_filter]
    refine ⟨ho, ?_⟩
    simp only [tailOf, dualEdge, primalTail_dual, decide_true]
  refine ⟨?_, ?_, ?_⟩
  · -- `W` tested closed: `E` is open
    intro hWc
    rw [key1, key2]
    congr 1
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hx
    have := hx _ (hW false hWc)
    simp only [dualEdge, primalDir_dual] at this
    rw [openAt_opp] at this
    simpa using this
  · -- `W` tested open: `E` is closed
    intro hWo
    rw [key1]
    have : {x : squareGraph.neighborSet v |
        Q ((nbr v).symm x) ∧ openAt a ((nbr v).symm x) = true} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx
      have := hx _ (hW true hWo)
      simp only [dualEdge, primalDir_dual] at this
      rw [openAt_opp] at this
      simpa using this
    rw [this, measure_empty, zero_mul]
  · -- `W` untested: probability one half
    intro hWc hWo
    rw [key1, key2, ← mul_assoc]
    congr 1
    -- the constraints at `v` are on the sides `N` and `S`
    set m₁t := decide (((dualEdge v (a - 1)).1, (dualEdge v (a - 1)).2, true) ∈ Cv) with hm₁t
    set m₁f := decide (((dualEdge v (a - 1)).1, (dualEdge v (a - 1)).2, false) ∈ Cv) with hm₁f
    set m₂t := decide (((dualEdge v (a + 1)).1, (dualEdge v (a + 1)).2, true) ∈ Cv) with hm₂t
    set m₂f := decide (((dualEdge v (a + 1)).1, (dualEdge v (a + 1)).2, false) ∈ Cv) with hm₂f
    have hQ' : ∀ dd : Dir, Q dd ↔
        sideOK m₁t m₁f (openAt (a - 1) dd) ∧ sideOK m₂t m₂f (openAt (a + 1) dd) := by
      intro dd
      constructor
      · intro hq
        refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
        · have := hq _ (of_decide_eq_true h)
          simpa [dualEdge, primalDir_dual] using this
        · have := hq _ (of_decide_eq_true h)
          simpa [dualEdge, primalDir_dual] using this
        · have := hq _ (of_decide_eq_true h)
          simpa [dualEdge, primalDir_dual] using this
        · have := hq _ (of_decide_eq_true h)
          simpa [dualEdge, primalDir_dual] using this
      · rintro ⟨⟨h1t, h1f⟩, ⟨h2t, h2f⟩⟩ t ht
        have htv := hCv_tail t ht
        have htadj := hCv_adj t ht
        set k := primalDir t.1 t.2.1 with hk
        have hte : (t.1, t.2.1) = dualEdge v k := by
          rw [hk, ← htv, tailOf, dualEdge_primal htadj]
        have hka : k ≠ a := by
          intro hka
          apply hnot t (List.mem_of_mem_filter ht)
          rw [hev, ← hka, ← hte]
        have hka2 : k ≠ a + 2 := by
          intro hka2
          have ht' : t = ((dualEdge v (a + 2)).1, (dualEdge v (a + 2)).2, t.2.2) := by
            rw [← hka2, ← hte]
          rcases hb : t.2.2 with _ | _
          · rw [hb] at ht'
            exact hWc (ht' ▸ List.mem_of_mem_filter ht)
          · rw [hb] at ht'
            exact hWo (ht' ▸ List.mem_of_mem_filter ht)
        have hteq : t = ((dualEdge v k).1, (dualEdge v k).2, t.2.2) := by rw [← hte]
        rcases side_cases a k hka hka2 with hk1 | hk1
        · rcases hb : t.2.2 with _ | _
          · have hmem : ((dualEdge v (a - 1)).1, (dualEdge v (a - 1)).2, false) ∈ Cv := by
              rw [← hk1, ← hb, ← hteq]; exact ht
            rw [hk1]
            exact h1f (by rw [hm₁f, decide_eq_true_iff]; exact hmem)
          · have hmem : ((dualEdge v (a - 1)).1, (dualEdge v (a - 1)).2, true) ∈ Cv := by
              rw [← hk1, ← hb, ← hteq]; exact ht
            rw [hk1]
            exact h1t (by rw [hm₁t, decide_eq_true_iff]; exact hmem)
        · rcases hb : t.2.2 with _ | _
          · have hmem : ((dualEdge v (a + 1)).1, (dualEdge v (a + 1)).2, false) ∈ Cv := by
              rw [← hk1, ← hb, ← hteq]; exact ht
            rw [hk1]
            exact h2f (by rw [hm₂f, decide_eq_true_iff]; exact hmem)
          · have hmem : ((dualEdge v (a + 1)).1, (dualEdge v (a + 1)).2, true) ∈ Cv := by
              rw [← hk1, ← hb, ← hteq]; exact ht
            rw [hk1]
            exact h2t (by rw [hm₂t, decide_eq_true_iff]; exact hmem)
    have hs1 : {x : squareGraph.neighborSet v | Q ((nbr v).symm x) ∧ openAt a ((nbr v).symm x) = true} =
        {x | (sideOK m₁t m₁f (openAt (a - 1) ((nbr v).symm x)) ∧
          sideOK m₂t m₂f (openAt (a + 1) ((nbr v).symm x))) ∧ openAt a ((nbr v).symm x) = true} := by
      ext x; simp only [Set.mem_setOf_eq, hQ']
    have hs2 : {x : squareGraph.neighborSet v | Q ((nbr v).symm x)} =
        {x | sideOK m₁t m₁f (openAt (a - 1) ((nbr v).symm x)) ∧
          sideOK m₂t m₂f (openAt (a + 1) ((nbr v).symm x))} := by
      ext x; simp only [Set.mem_setOf_eq, hQ']
    rw [hs1, hs2, uniformAt_dir v (fun dd => (sideOK m₁t m₁f (openAt (a - 1) dd) ∧
      sideOK m₂t m₂f (openAt (a + 1) dd)) ∧ openAt a dd = true),
      uniformAt_dir v (fun dd => sideOK m₁t m₁f (openAt (a - 1) dd) ∧
      sideOK m₂t m₂f (openAt (a + 1) dd))]
    have hc := half_count a m₁t m₁f m₂t m₂f
    rw [← hc]
    push_cast
    rw [mul_div_assoc, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top, one_mul]

end Rotor
