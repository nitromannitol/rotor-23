import Rotor.Support.FreshTime

/-!
Extinction of the exploration, `rotor.tex:1362-1376`: the retained tree is dominated by a
critical Galton–Watson tree, so it is finite almost surely.  Formally: the queue length at
the fresh steps is a supermartingale with respect to the atoms of the read histories, hence
it hits a level `N` with probability at most `1/N`; and while it stays below `N`, each block
of `N` fresh steps has probability at least `3^{-N}` of consisting of steps that add nothing,
which would empty the queue.  So almost surely only finitely many vertices are reached.
-/

open Finset MeasureTheory

namespace Rotor

open QueryProcess

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (o x : V)

section Partition

/-- The history read by `ρ` up to the `j`-th fresh step. -/
noncomputable def histOf (j : ℕ) (ρ : Config G) : History G :=
  (St π o x ρ (τf π o x j ρ)).hist.map (fun v => ⟨v, ρ v⟩)

variable {π o x}

theorem verts_histOf (j : ℕ) (ρ : Config G) :
    verts (histOf π o x j ρ) = (St π o x ρ (τf π o x j ρ)).hist := by
  simp only [histOf, verts, List.map_map]
  exact List.map_id' _

theorem length_histOf {j : ℕ} {ρ : Config G} (hj : Reach π o x j ρ) :
    (histOf π o x j ρ).length = j := by
  unfold histOf
  rw [List.length_map]
  exact hist_length_τf hj

theorem mem_atomE_histOf (j : ℕ) (ρ : Config G) :
    ρ ∈ atomE π o x (histOf π o x j ρ) := by
  refine ⟨⟨τf π o x j ρ, ?_⟩, fun y hy => ?_⟩
  · rw [hist_run_eq, verts_histOf]
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy
    rfl

theorem histOf_eq_of_mem_atomE {h : History G} {ρ : Config G} (hρ : ρ ∈ atomE π o x h) :
    histOf π o x h.length ρ = h := by
  have hr := reach_of_atomE hρ
  have hv : (St π o x ρ (τf π o x h.length ρ)).hist = verts h := by
    obtain ⟨⟨t₀, ht₀⟩, -⟩ := id hρ
    rw [hist_run_eq] at ht₀
    have hτ : τf π o x h.length ρ ≤ t₀ := τf_le hr (by rw [ht₀, verts, List.length_map])
    have hpre := (qProc π o x).hist_run_prefix ρ hτ
    rw [hist_run_eq, hist_run_eq, ht₀] at hpre
    exact hpre.eq_of_length (by rw [hist_length_τf hr, verts, List.length_map])
  rw [histOf, hv, verts, List.map_map]
  conv_rhs => rw [← List.map_id h]
  apply List.map_congr_left
  intro y hy
  simp only [Function.comp, id]
  have := hρ.2 y hy
  exact Sigma.ext rfl (heq_of_eq this)

theorem atomE_disjoint {h h' : History G} (hlen : h.length = h'.length) (hne : h ≠ h') :
    Disjoint (atomE π o x h) (atomE π o x h') := by
  rw [Set.disjoint_left]
  intro ρ hρ hρ'
  apply hne
  rw [← histOf_eq_of_mem_atomE hρ, ← histOf_eq_of_mem_atomE hρ', hlen]

theorem exists_max_reach (ρ : Config G) : ∀ j : ℕ, ∃ i ≤ j, Reach π o x i ρ ∧
    (i = j ∨ ¬ Reach π o x (i + 1) ρ)
  | 0 => ⟨0, le_rfl, reach_zero ρ, Or.inl rfl⟩
  | j + 1 => by
    by_cases hj : Reach π o x (j + 1) ρ
    · exact ⟨j + 1, le_rfl, hj, Or.inl rfl⟩
    · obtain ⟨i, hi, hr, hor⟩ := exists_max_reach ρ j
      refine ⟨i, by omega, hr, Or.inr ?_⟩
      rcases hor with rfl | h
      · exact hj
      · exact h

variable (π o x) in
/-- The pieces of the partition at level `j`: the atoms of level `j`, and the atoms of
lower level at which the exploration stops reaching new vertices. -/
noncomputable def piece (j : ℕ) (h : History G) : Set (Config G) :=
  if h.length = j then atomE π o x h else atomE π o x h ∩ {ρ | ¬ Reach π o x (h.length + 1) ρ}

theorem piece_subset_atomE (j : ℕ) (h : History G) : piece π o x j h ⊆ atomE π o x h := by
  unfold piece
  split_ifs
  · exact le_rfl
  · exact Set.inter_subset_left

theorem piece_of_length_eq {j : ℕ} {h : History G} (hh : h.length = j) :
    piece π o x j h = atomE π o x h := by
  unfold piece; rw [if_pos hh]

theorem piece_of_length_lt {j : ℕ} {h : History G} (hh : h.length < j) :
    piece π o x j h = atomE π o x h ∩ {ρ | ¬ Reach π o x (h.length + 1) ρ} := by
  unfold piece; rw [if_neg hh.ne]

theorem iUnion_piece (j : ℕ) :
    ⋃ h : {h : History G // h.length ≤ j}, piece π o x j h.1 = Set.univ := by
  ext ρ
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨i, hi, hr, hor⟩ := exists_max_reach ρ j
  refine ⟨⟨histOf π o x i ρ, by rw [length_histOf hr]; exact hi⟩, ?_⟩
  rcases hor with rfl | hnr
  · rw [piece_of_length_eq (length_histOf hr)]
    exact mem_atomE_histOf _ _
  · rcases lt_or_eq_of_le hi with hlt | rfl
    · rw [piece_of_length_lt (by rw [length_histOf hr]; exact hlt)]
      refine ⟨mem_atomE_histOf _ _, ?_⟩
      rw [length_histOf hr]; exact hnr
    · rw [piece_of_length_eq (length_histOf hr)]
      exact mem_atomE_histOf _ _

theorem piece_disjoint {j : ℕ} {h h' : History G} (hh : h.length ≤ j) (hh' : h'.length ≤ j)
    (hne : h ≠ h') : Disjoint (piece π o x j h) (piece π o x j h') := by
  rcases lt_trichotomy h.length h'.length with hlt | heq | hgt
  · rw [piece_of_length_lt (by omega)]
    rw [Set.disjoint_left]
    rintro ρ ⟨-, hnr⟩ hρ'
    exact hnr (reach_mono (by omega) (reach_of_atomE (piece_subset_atomE j h' hρ')))
  · exact (atomE_disjoint heq hne).mono (piece_subset_atomE j h) (piece_subset_atomE j h')
  · rw [piece_of_length_lt (j := j) (h := h') (by omega)]
    rw [Set.disjoint_left]
    rintro ρ hρ ⟨-, hnr⟩
    exact hnr (reach_mono (by omega) (reach_of_atomE (piece_subset_atomE j h hρ)))

theorem Y_const_on_piece {j : ℕ} {h : History G} (hh : h.length ≤ j) {k : ℕ} (hk : k ≤ j)
    {ρ ρ' : Config G} (hρ : ρ ∈ piece π o x j h) (hρ' : ρ' ∈ piece π o x j h) :
    Y π o x k ρ = Y π o x k ρ' := by
  rcases le_or_gt k h.length with hkh | hkh
  · exact Y_eq_of_atomE_le (piece_subset_atomE j h hρ) (piece_subset_atomE j h hρ') hkh
  · have hlt : h.length < j := by omega
    rw [piece_of_length_lt hlt] at hρ hρ'
    rw [Y_of_not_reach (fun hr => hρ.2 (reach_mono (by omega) hr)),
      Y_of_not_reach (fun hr => hρ'.2 (reach_mono (by omega) hr))]

theorem reach_const_on_piece {j : ℕ} {h : History G} (hh : h.length ≤ j) {k : ℕ} (hk : k ≤ j)
    {ρ ρ' : Config G} (hρ : ρ ∈ piece π o x j h) (hρ' : ρ' ∈ piece π o x j h) :
    Reach π o x k ρ ↔ Reach π o x k ρ' := by
  rcases le_or_gt k h.length with hkh | hkh
  · exact ⟨fun _ => reach_mono hkh (reach_of_atomE (piece_subset_atomE j h hρ')),
      fun _ => reach_mono hkh (reach_of_atomE (piece_subset_atomE j h hρ))⟩
  · have hlt : h.length < j := by omega
    rw [piece_of_length_lt hlt] at hρ hρ'
    exact ⟨fun hr => absurd (reach_mono (by omega) hr) hρ.2,
      fun hr => absurd (reach_mono (by omega) hr) hρ'.2⟩

variable [Countable V]

theorem measurableSet_reach (j : ℕ) : MeasurableSet {ρ : Config G | Reach π o x j ρ} := by
  have : {ρ : Config G | Reach π o x j ρ} = ⋃ h : {h : History G // h.length = j}, atomE π o x h.1 := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hr
      exact ⟨⟨histOf π o x j ρ, length_histOf hr⟩, mem_atomE_histOf _ _⟩
    · rintro ⟨h, hρ⟩
      have := reach_of_atomE hρ
      rwa [h.2] at this
  rw [this]
  exact MeasurableSet.iUnion (fun h => measurableSet_atomE h.1)

theorem measurableSet_piece (j : ℕ) (h : History G) : MeasurableSet (piece π o x j h) := by
  unfold piece
  split_ifs
  · exact measurableSet_atomE h
  · exact (measurableSet_atomE h).inter (measurableSet_reach _).compl

/-- A function constant on every piece of level `j` is measurable. -/
theorem measurable_of_const_on_pieces (j : ℕ) (F : Config G → ℕ)
    (hF : ∀ h : History G, h.length ≤ j → ∀ ρ ∈ piece π o x j h, ∀ ρ' ∈ piece π o x j h,
      F ρ = F ρ') : Measurable F := by
  classical
  refine measurable_to_countable' (fun n => ?_)
  have : F ⁻¹' {n} = ⋃ h : {h : History G // h.length ≤ j},
      if ∃ ρ ∈ piece π o x j h.1, F ρ = n then piece π o x j h.1 else ∅ := by
    ext ρ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
    constructor
    · intro hρ
      have hcov := iUnion_piece (π := π) (o := o) (x := x) j
      have : ρ ∈ ⋃ h : {h : History G // h.length ≤ j}, piece π o x j h.1 := by
        rw [hcov]; exact Set.mem_univ ρ
      obtain ⟨h, hh⟩ := Set.mem_iUnion.1 this
      refine ⟨h, ?_⟩
      rw [if_pos ⟨ρ, hh, hρ⟩]
      exact hh
    · rintro ⟨h, hh⟩
      split_ifs at hh with hex
      · obtain ⟨ρ', hρ', hF'⟩ := hex
        rw [hF h.1 h.2 ρ hh ρ' hρ', hF']
      · exact absurd hh (Set.notMem_empty ρ)
  rw [this]
  refine MeasurableSet.iUnion (fun h => ?_)
  split_ifs
  · exact measurableSet_piece j h.1
  · exact MeasurableSet.empty

theorem measurable_Y (j : ℕ) : Measurable (fun ρ : Config G => Y π o x j ρ) :=
  measurable_of_const_on_pieces j _ (fun _ hh _ hρ _ hρ' => Y_const_on_piece hh le_rfl hρ hρ')

end Partition

section Stopped

variable {π o x}

variable (π o x) in
open Classical in
/-- The queue length at fresh steps, stopped when it first reaches `N`. -/
noncomputable def Z (N j : ℕ) (ρ : Config G) : ℕ :=
  if h : ∃ i ≤ j, N ≤ Y π o x i ρ then Y π o x (Nat.find h) ρ else Y π o x j ρ

variable {N : ℕ}

theorem Z_zero (ρ : Config G) : Z π o x N 0 ρ = 1 := by
  unfold Z
  split_ifs with h
  · have := (Nat.find_spec h).1
    rw [Nat.le_zero.1 this, Y_zero]
  · exact Y_zero ρ

theorem Z_succ_of_stopped {j : ℕ} {ρ : Config G} (hs : ∃ i ≤ j, N ≤ Y π o x i ρ) :
    Z π o x N (j + 1) ρ = Z π o x N j ρ := by
  classical
  have hs' : ∃ i ≤ j + 1, N ≤ Y π o x i ρ := by
    obtain ⟨i, hi, h⟩ := hs; exact ⟨i, by omega, h⟩
  have hfind : Nat.find hs' = Nat.find hs := by
    rw [Nat.find_eq_iff]
    exact ⟨⟨(Nat.find_spec hs).1.trans (Nat.le_succ j), (Nat.find_spec hs).2⟩,
      fun n hn hn' => Nat.find_min hs hn ⟨(Nat.find_spec hs).1.trans' hn.le, hn'.2⟩⟩
  unfold Z
  rw [dif_pos hs, dif_pos hs', hfind]

theorem Z_succ_of_not_stopped {j : ℕ} {ρ : Config G} (hs : ¬ ∃ i ≤ j, N ≤ Y π o x i ρ) :
    Z π o x N (j + 1) ρ = Y π o x (j + 1) ρ ∧ Z π o x N j ρ = Y π o x j ρ := by
  classical
  refine ⟨?_, by unfold Z; rw [dif_neg hs]⟩
  unfold Z
  split_ifs with h
  · congr 1
    rw [Nat.find_eq_iff]
    refine ⟨⟨le_rfl, ?_⟩, fun n hn hn' => hs ⟨n, by omega, hn'.2⟩⟩
    obtain ⟨i, hi, hY⟩ := h
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact absurd ⟨i, by omega, hY⟩ hs
    · rwa [show i = j + 1 by omega] at hY
  · rfl

theorem Z_le_of_not_reach {j : ℕ} {ρ : Config G}
    (hj : ¬ Reach π o x (j + 1) ρ) : Z π o x N (j + 1) ρ ≤ Z π o x N j ρ := by
  by_cases hs : ∃ i ≤ j, N ≤ Y π o x i ρ
  · rw [Z_succ_of_stopped hs]
  · obtain ⟨h1, -⟩ := Z_succ_of_not_stopped hs
    rw [h1, Y_of_not_reach hj]
    exact Nat.zero_le _

theorem stopped_iff {j : ℕ} {ρ : Config G} : (∃ i ≤ j, N ≤ Y π o x i ρ) ↔ N ≤ Z π o x N j ρ := by
  classical
  constructor
  · intro hs
    unfold Z
    rw [dif_pos hs]
    exact (Nat.find_spec hs).2
  · intro hZ
    by_contra hs
    obtain ⟨-, h2⟩ := Z_succ_of_not_stopped hs
    rw [h2] at hZ
    exact hs ⟨j, le_rfl, hZ⟩

theorem Z_const_on_piece {j : ℕ} {h : History G} (hh : h.length ≤ j) {ρ ρ' : Config G}
    (hρ : ρ ∈ piece π o x j h) (hρ' : ρ' ∈ piece π o x j h) :
    Z π o x N j ρ = Z π o x N j ρ' := by
  classical
  have hY : ∀ i ≤ j, Y π o x i ρ = Y π o x i ρ' := fun i hi => Y_const_on_piece hh hi hρ hρ'
  have hiff : (∃ i ≤ j, N ≤ Y π o x i ρ) ↔ (∃ i ≤ j, N ≤ Y π o x i ρ') := by
    constructor
    · rintro ⟨i, hi, hY'⟩; exact ⟨i, hi, by rwa [← hY i hi]⟩
    · rintro ⟨i, hi, hY'⟩; exact ⟨i, hi, by rwa [hY i hi]⟩
  unfold Z
  by_cases hs : ∃ i ≤ j, N ≤ Y π o x i ρ
  · have hs' := hiff.1 hs
    rw [dif_pos hs, dif_pos hs']
    have hfind : Nat.find hs = Nat.find hs' := by
      rw [Nat.find_eq_iff]
      refine ⟨⟨(Nat.find_spec hs').1, by rw [hY _ (Nat.find_spec hs').1]; exact (Nat.find_spec hs').2⟩,
        fun n hn hn' => Nat.find_min hs' hn ⟨hn'.1, by rw [← hY n hn'.1]; exact hn'.2⟩⟩
    rw [hfind, hY _ (Nat.find_spec hs').1]
  · rw [dif_neg hs, dif_neg (fun h' => hs (hiff.2 h')), hY j le_rfl]

variable [Countable V]

theorem measurable_Z (j : ℕ) : Measurable (fun ρ : Config G => Z π o x N j ρ) :=
  measurable_of_const_on_pieces j _ (fun _ hh _ hρ _ hρ' => Z_const_on_piece hh hρ hρ')

/-- The supermartingale step on a full atom of level `j`. -/
theorem lintegral_Y_succ_le_atom (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3)
    {j : ℕ} {h : History G} (hj : h.length = j) :
    ∫⁻ ρ in atomE π o x h, (Y π o x (j + 1) ρ : ENNReal) ∂(uniformLaw π)
      ≤ ∫⁻ ρ in atomE π o x h, (Y π o x j ρ : ENNReal) ∂(uniformLaw π) := by
  subst hj
  set R := {ρ : Config G | Reach π o x (h.length + 1) ρ} with hR
  have hsplit : atomE π o x h = (atomE π o x h ∩ R) ∪ (atomE π o x h ∩ Rᶜ) :=
    (Set.inter_union_compl _ _).symm
  have hdisj : Disjoint (atomE π o x h ∩ R) (atomE π o x h ∩ Rᶜ) :=
    Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right disjoint_compl_right
  have hmR : MeasurableSet (atomE π o x h ∩ Rᶜ) :=
    (measurableSet_atomE h).inter (measurableSet_reach _).compl
  rw [hsplit, lintegral_union hmR hdisj, lintegral_union hmR hdisj]
  refine add_le_add ?_ ?_
  · rcases Set.eq_empty_or_nonempty (atomE π o x h ∩ R) with he | ⟨ρ₀, hρ₀⟩
    · rw [he]; simp
    obtain ⟨v₀, hv₀⟩ := (reach_succ_iff hρ₀.1).1 hρ₀.2
    have heq : atomE π o x h ∩ R = atomE π o x h ∩ nxtE π o x h v₀ := by
      ext ρ
      constructor
      · rintro ⟨hρ, hr⟩
        obtain ⟨v, hv⟩ := (reach_succ_iff hρ).1 hr
        rw [nxt_eq_of_atomE ⟨hρ₀.1, hv₀⟩ hρ hv]
        exact ⟨hρ, hv⟩
      · rintro ⟨hρ, hv⟩
        exact ⟨hρ, (reach_succ_iff hρ).2 ⟨v₀, hv⟩⟩
    rw [heq]
    exact lintegral_Y_succ_le hox h3 h v₀
  · refine setLIntegral_mono' hmR (fun ρ hρ => ?_)
    rw [Y_of_not_reach hρ.2, Nat.cast_zero]
    exact zero_le

theorem lintegral_Z_succ_le (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) (j : ℕ) :
    ∫⁻ ρ, (Z π o x N (j + 1) ρ : ENNReal) ∂(uniformLaw π)
      ≤ ∫⁻ ρ, (Z π o x N j ρ : ENNReal) ∂(uniformLaw π) := by
  have hcov := iUnion_piece (π := π) (o := o) (x := x) j
  have hd : Pairwise (Function.onFun Disjoint
      (fun h : {h : History G // h.length ≤ j} => piece π o x j h.1)) :=
    fun h h' hne => piece_disjoint h.2 h'.2 (fun e => hne (Subtype.ext e))
  rw [← Measure.restrict_univ (μ := uniformLaw π), ← hcov,
    lintegral_iUnion (s := fun h : {h : History G // h.length ≤ j} => piece π o x j h.1)
      (fun h => measurableSet_piece j h.1) hd,
    lintegral_iUnion (s := fun h : {h : History G // h.length ≤ j} => piece π o x j h.1)
      (fun h => measurableSet_piece j h.1) hd]
  refine ENNReal.tsum_le_tsum (fun h => ?_)
  rcases lt_or_eq_of_le h.2 with hlt | heq
  · refine setLIntegral_mono' (measurableSet_piece j h.1) (fun ρ hρ => ?_)
    rw [piece_of_length_lt hlt] at hρ
    exact_mod_cast Z_le_of_not_reach (fun hr => hρ.2 (reach_mono (by omega) hr))
  · rw [piece_of_length_eq heq]
    by_cases hs : ∃ ρ₀ ∈ atomE π o x h.1, ∃ i ≤ j, N ≤ Y π o x i ρ₀
    · obtain ⟨ρ₀, hρ₀, i, hi, hY⟩ := hs
      refine setLIntegral_mono' (measurableSet_atomE h.1) (fun ρ hρ => ?_)
      have hs' : ∃ i ≤ j, N ≤ Y π o x i ρ :=
        ⟨i, hi, by rwa [Y_eq_of_atomE_le hρ hρ₀ (by omega)]⟩
      exact_mod_cast (Z_succ_of_stopped hs').le
    · push Not at hs
      have hZ : ∀ ρ ∈ atomE π o x h.1,
          Z π o x N (j + 1) ρ = Y π o x (j + 1) ρ ∧ Z π o x N j ρ = Y π o x j ρ :=
        fun ρ hρ => Z_succ_of_not_stopped (fun ⟨i, hi, hY⟩ => absurd hY (not_le.2 (hs ρ hρ i hi)))
      calc ∫⁻ ρ in atomE π o x h.1, (Z π o x N (j + 1) ρ : ENNReal) ∂(uniformLaw π)
          = ∫⁻ ρ in atomE π o x h.1, (Y π o x (j + 1) ρ : ENNReal) ∂(uniformLaw π) :=
            setLIntegral_congr_fun (measurableSet_atomE _) (fun ρ hρ => by rw [(hZ ρ hρ).1])
        _ ≤ ∫⁻ ρ in atomE π o x h.1, (Y π o x j ρ : ENNReal) ∂(uniformLaw π) :=
            lintegral_Y_succ_le_atom hox h3 heq
        _ = ∫⁻ ρ in atomE π o x h.1, (Z π o x N j ρ : ENNReal) ∂(uniformLaw π) :=
            (setLIntegral_congr_fun (measurableSet_atomE _) (fun ρ hρ => by rw [(hZ ρ hρ).2])).symm

theorem lintegral_Z_le_one (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) :
    ∀ j : ℕ, ∫⁻ ρ, (Z π o x N j ρ : ENNReal) ∂(uniformLaw π) ≤ 1
  | 0 => by simp [Z_zero]
  | j + 1 => (lintegral_Z_succ_le hox h3 j).trans (lintegral_Z_le_one hox h3 j)

/-- Markov: the queue length at a fresh step reaches `N` with probability at most `1/N`. -/
theorem measure_stopped_le (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) (j : ℕ) : uniformLaw π {ρ | ∃ i ≤ j, N ≤ Y π o x i ρ} ≤ (N : ENNReal)⁻¹ := by
  have hE : {ρ : Config G | ∃ i ≤ j, N ≤ Y π o x i ρ} = {ρ | N ≤ Z π o x N j ρ} := by
    ext ρ; exact stopped_iff
  have hm : MeasurableSet {ρ : Config G | N ≤ Z π o x N j ρ} :=
    measurableSet_le measurable_const (measurable_Z j)
  rw [hE, ENNReal.le_inv_iff_mul_le, mul_comm]
  calc (N : ENNReal) * uniformLaw π {ρ | N ≤ Z π o x N j ρ}
      = ∫⁻ ρ in {ρ | N ≤ Z π o x N j ρ}, (N : ENNReal) ∂(uniformLaw π) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ ρ in {ρ | N ≤ Z π o x N j ρ}, (Z π o x N j ρ : ENNReal) ∂(uniformLaw π) :=
        setLIntegral_mono' hm (fun ρ hρ => by exact_mod_cast hρ)
    _ ≤ ∫⁻ ρ, (Z π o x N j ρ : ENNReal) ∂(uniformLaw π) := setLIntegral_le_lintegral _ _
    _ ≤ 1 := lintegral_Z_le_one hox h3 j

theorem measure_exists_stop_le (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) :
    uniformLaw π {ρ | ∃ i, N ≤ Y π o x i ρ} ≤ (N : ENNReal)⁻¹ := by
  have : {ρ : Config G | ∃ i, N ≤ Y π o x i ρ} = ⋃ i, {ρ | N ≤ Y π o x i ρ} := by
    ext ρ; simp
  rw [this, measure_iUnion_eq_iSup_accumulate]
  refine iSup_le (fun j => ?_)
  have : Set.accumulate (fun i => {ρ : Config G | N ≤ Y π o x i ρ}) j
      = {ρ | ∃ i ≤ j, N ≤ Y π o x i ρ} := by
    ext ρ; simp [Set.mem_accumulate]
  rw [this]
  exact measure_stopped_le hox h3 j

end Stopped

section Blocks

variable {π o x}

variable (π o x) in
/-- Either the `(j+1)`-th fresh step does not occur or it adds nothing. -/
def Drop (j : ℕ) : Set (Config G) :=
  {ρ | ¬ Reach π o x (j + 1) ρ ∨ Y π o x (j + 1) ρ + 1 ≤ Y π o x j ρ}

variable (π o x) in
/-- The sets that are unions of pieces of level `j`. -/
def LevelMeas (j : ℕ) (E : Set (Config G)) : Prop :=
  ∀ h : History G, h.length ≤ j → ∀ ρ ∈ piece π o x j h, ∀ ρ' ∈ piece π o x j h, ρ ∈ E → ρ' ∈ E

theorem levelMeas_succ {j : ℕ} {E : Set (Config G)} (hE : LevelMeas π o x j E) :
    LevelMeas π o x (j + 1) E := by
  intro h hh ρ hρ ρ' hρ' hE'
  rcases lt_or_eq_of_le hh with hlt | heq
  · have hsub : piece π o x (j + 1) h ⊆ piece π o x j h := by
      rw [piece_of_length_lt hlt]
      unfold piece
      split_ifs
      · exact Set.inter_subset_left
      · exact le_rfl
    exact hE h (by omega) ρ (hsub hρ) ρ' (hsub hρ') hE'
  · rw [piece_of_length_eq heq] at hρ hρ'
    have hlen : (h.take j).length = j := by rw [List.length_take]; omega
    have hsub : atomE π o x h ⊆ piece π o x j (h.take j) := by
      rw [piece_of_length_eq hlen]
      exact fun ρ hρ => (qProc π o x).atomF_prefix (List.take_prefix j h) hρ
    exact hE (h.take j) hlen.le ρ (hsub hρ) ρ' (hsub hρ') hE'

theorem levelMeas_of_le {j k : ℕ} (hjk : j ≤ k) {E : Set (Config G)}
    (hE : LevelMeas π o x j E) : LevelMeas π o x k E := by
  induction k with
  | zero => rw [Nat.le_zero.1 hjk] at hE; exact hE
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact levelMeas_succ (ih (by omega))
    · rw [Nat.le_antisymm hjk h] at hE; exact hE

theorem levelMeas_inter {j : ℕ} {E E' : Set (Config G)} (hE : LevelMeas π o x j E)
    (hE' : LevelMeas π o x j E') : LevelMeas π o x j (E ∩ E') :=
  fun h hh ρ hρ ρ' hρ' ⟨h1, h2⟩ => ⟨hE h hh ρ hρ ρ' hρ' h1, hE' h hh ρ hρ ρ' hρ' h2⟩

theorem levelMeas_compl {j : ℕ} {E : Set (Config G)} (hE : LevelMeas π o x j E) :
    LevelMeas π o x j Eᶜ :=
  fun h hh ρ hρ ρ' hρ' hnE hE' => hnE (hE h hh ρ' hρ' ρ hρ hE')

theorem levelMeas_drop (j : ℕ) : LevelMeas π o x (j + 1) (Drop π o x j) := by
  intro h hh ρ hρ ρ' hρ' hD
  simp only [Drop, Set.mem_setOf_eq] at hD ⊢
  rw [← reach_const_on_piece hh le_rfl hρ hρ', ← Y_const_on_piece hh le_rfl hρ hρ',
    ← Y_const_on_piece hh (Nat.le_succ j) hρ hρ']
  exact hD

theorem levelMeas_reach (j : ℕ) : LevelMeas π o x j {ρ | Reach π o x j ρ} :=
  fun _ hh _ hρ _ hρ' hr => (reach_const_on_piece hh le_rfl hρ hρ').1 hr

variable [Countable V]

theorem measurableSet_of_levelMeas {j : ℕ} {E : Set (Config G)} (hE : LevelMeas π o x j E) :
    MeasurableSet E := by
  classical
  have : E = ⋃ h : {h : History G // h.length ≤ j},
      if ∃ ρ ∈ piece π o x j h.1, ρ ∈ E then piece π o x j h.1 else ∅ := by
    ext ρ
    simp only [Set.mem_iUnion]
    constructor
    · intro hρ
      have hmem : ρ ∈ ⋃ h : {h : History G // h.length ≤ j}, piece π o x j h.1 := by
        rw [iUnion_piece]; exact Set.mem_univ ρ
      obtain ⟨h, hh⟩ := Set.mem_iUnion.1 hmem
      exact ⟨h, by rw [if_pos ⟨ρ, hh, hρ⟩]; exact hh⟩
    · rintro ⟨h, hh⟩
      split_ifs at hh with hex
      · obtain ⟨ρ', hρ', hE'⟩ := hex
        exact hE h.1 h.2 ρ' hρ' ρ hh hE'
      · exact absurd hh (Set.notMem_empty ρ)
  rw [this]
  refine MeasurableSet.iUnion (fun h => ?_)
  split_ifs
  · exact measurableSet_piece j h.1
  · exact MeasurableSet.empty

theorem measurableSet_drop (j : ℕ) : MeasurableSet (Drop π o x j) :=
  measurableSet_of_levelMeas (levelMeas_drop j)

/-- On an atom of level `j`, the next fresh step drops with probability at least `1/3`. -/
theorem measure_atomE_le_three_mul_drop (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3)
    {j : ℕ} {h : History G} (hj : h.length = j) :
    uniformLaw π (atomE π o x h) ≤ 3 * uniformLaw π (atomE π o x h ∩ Drop π o x j) := by
  subst hj
  set R := {ρ : Config G | Reach π o x (h.length + 1) ρ} with hR
  have hmR : MeasurableSet R := measurableSet_reach _
  have h1 : uniformLaw π (atomE π o x h) =
      uniformLaw π (atomE π o x h ∩ Rᶜ) + uniformLaw π (atomE π o x h ∩ R) := by
    rw [← measure_inter_add_sdiff (atomE π o x h) hmR, add_comm, Set.sdiff_eq]
  have h2 : uniformLaw π (atomE π o x h ∩ Drop π o x h.length) =
      uniformLaw π (atomE π o x h ∩ Drop π o x h.length ∩ Rᶜ) +
        uniformLaw π (atomE π o x h ∩ Drop π o x h.length ∩ R) := by
    rw [← measure_inter_add_sdiff (atomE π o x h ∩ Drop π o x h.length) hmR, add_comm, Set.sdiff_eq]
  rw [h1, h2, mul_add]
  refine add_le_add ?_ ?_
  · have hsub : atomE π o x h ∩ Rᶜ ⊆ atomE π o x h ∩ Drop π o x h.length ∩ Rᶜ :=
      fun ρ ⟨hρ, hr⟩ => ⟨⟨hρ, Or.inl hr⟩, hr⟩
    exact (measure_mono hsub).trans (le_mul_of_one_le_left (zero_le) (by norm_num))
  · rcases Set.eq_empty_or_nonempty (atomE π o x h ∩ R) with he | ⟨ρ₀, hρ₀⟩
    · rw [he]; simp
    obtain ⟨v₀, hv₀⟩ := (reach_succ_iff hρ₀.1).1 hρ₀.2
    have heq : atomE π o x h ∩ R = atomE π o x h ∩ nxtE π o x h v₀ := by
      ext ρ
      constructor
      · rintro ⟨hρ, hr⟩
        obtain ⟨v, hv⟩ := (reach_succ_iff hρ).1 hr
        rw [nxt_eq_of_atomE ⟨hρ₀.1, hv₀⟩ hρ hv]
        exact ⟨hρ, hv⟩
      · rintro ⟨hρ, hv⟩
        exact ⟨hρ, (reach_succ_iff hρ).2 ⟨v₀, hv⟩⟩
    rw [heq]
    refine (measure_drop_ge hox h3 h v₀).trans (mul_le_mul' le_rfl (measure_mono ?_))
    rintro ρ ⟨⟨hρ, hv⟩, hY⟩
    exact ⟨⟨hρ, Or.inr hY⟩, (reach_succ_iff hρ).2 ⟨v₀, hv⟩⟩

/-- Restricted to a set that is a union of pieces of level `j`, the next fresh step drops
with probability at least `1/3`. -/
theorem measure_le_three_mul_drop (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) {j : ℕ}
    {E : Set (Config G)} (hE : LevelMeas π o x j E) :
    uniformLaw π E ≤ 3 * uniformLaw π (E ∩ Drop π o x j) := by
  have hcov := iUnion_piece (π := π) (o := o) (x := x) j
  have hEm := measurableSet_of_levelMeas hE
  have hd : Pairwise (Function.onFun Disjoint
      (fun h : {h : History G // h.length ≤ j} => E ∩ piece π o x j h.1)) :=
    fun h h' hne => (piece_disjoint h.2 h'.2 (fun e => hne (Subtype.ext e))).mono
      Set.inter_subset_right Set.inter_subset_right
  have hd' : Pairwise (Function.onFun Disjoint
      (fun h : {h : History G // h.length ≤ j} => E ∩ Drop π o x j ∩ piece π o x j h.1)) :=
    fun h h' hne => (piece_disjoint h.2 h'.2 (fun e => hne (Subtype.ext e))).mono
      Set.inter_subset_right Set.inter_subset_right
  have hE1 : E = ⋃ h : {h : History G // h.length ≤ j}, E ∩ piece π o x j h.1 := by
    rw [← Set.inter_iUnion, hcov, Set.inter_univ]
  have hE2 : E ∩ Drop π o x j =
      ⋃ h : {h : History G // h.length ≤ j}, E ∩ Drop π o x j ∩ piece π o x j h.1 := by
    rw [← Set.inter_iUnion, hcov, Set.inter_univ]
  conv_rhs => rw [hE2]
  conv_lhs => rw [hE1]
  rw [measure_iUnion hd (fun h => hEm.inter (measurableSet_piece j h.1)),
    measure_iUnion hd' (fun h => (hEm.inter (measurableSet_drop j)).inter (measurableSet_piece j h.1)),
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun h => ?_)
  rcases lt_or_eq_of_le h.2 with hlt | heq
  · have hsub : E ∩ piece π o x j h.1 ⊆ E ∩ Drop π o x j ∩ piece π o x j h.1 := by
      rintro ρ ⟨hρE, hρp⟩
      refine ⟨⟨hρE, Or.inl ?_⟩, hρp⟩
      rw [piece_of_length_lt hlt] at hρp
      exact fun hr => hρp.2 (reach_mono (by omega) hr)
    exact (measure_mono hsub).trans (le_mul_of_one_le_left (zero_le) (by norm_num))
  · rw [piece_of_length_eq heq]
    by_cases hne : ∃ ρ₀ ∈ atomE π o x h.1, ρ₀ ∈ E
    · obtain ⟨ρ₀, hρ₀, hρ₀E⟩ := hne
      have hall : atomE π o x h.1 ⊆ E := fun ρ hρ =>
        hE h.1 h.2 ρ₀ (by rw [piece_of_length_eq heq]; exact hρ₀) ρ
          (by rw [piece_of_length_eq heq]; exact hρ) hρ₀E
      have e1 : E ∩ atomE π o x h.1 = atomE π o x h.1 := Set.inter_eq_right.2 hall
      have e2 : E ∩ Drop π o x j ∩ atomE π o x h.1 = atomE π o x h.1 ∩ Drop π o x j := by
        rw [Set.inter_assoc, Set.inter_comm (Drop π o x j), ← Set.inter_assoc, e1]
      rw [e1, e2]
      exact measure_atomE_le_three_mul_drop hox h3 heq
    · push Not at hne
      have : E ∩ atomE π o x h.1 = ∅ :=
        Set.eq_empty_of_forall_notMem (fun ρ ⟨h1, h2⟩ => hne ρ h2 h1)
      rw [this]
      simp

variable (π o x) in
/-- The first `n` fresh steps after `j` all drop. -/
def Drops (j : ℕ) : ℕ → Set (Config G)
  | 0 => Set.univ
  | n + 1 => Drops j n ∩ Drop π o x (j + n)

omit [Countable V] in
theorem mem_drops {j : ℕ} {ρ : Config G} : ∀ {n : ℕ},
    ρ ∈ Drops π o x j n ↔ ∀ i < n, ρ ∈ Drop π o x (j + i)
  | 0 => by simp [Drops]
  | n + 1 => by
    simp only [Drops, Set.mem_inter_iff, mem_drops]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

omit [Countable V] in
theorem levelMeas_drops (j : ℕ) : ∀ n : ℕ, LevelMeas π o x (j + n) (Drops π o x j n)
  | 0 => fun _ _ _ _ _ _ _ => Set.mem_univ _
  | n + 1 => by
    show LevelMeas π o x (j + n + 1) (Drops π o x j n ∩ Drop π o x (j + n))
    exact levelMeas_inter (levelMeas_succ (levelMeas_drops j n)) (levelMeas_drop (j + n))

theorem measure_le_pow_three_mul_drops (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3)
    {j : ℕ} {E : Set (Config G)} (hE : LevelMeas π o x j E) : ∀ n : ℕ,
    uniformLaw π E ≤ 3 ^ n * uniformLaw π (E ∩ Drops π o x j n)
  | 0 => by simp [Drops]
  | n + 1 => by
    have hE' : LevelMeas π o x (j + n) (E ∩ Drops π o x j n) :=
      levelMeas_inter (levelMeas_of_le (Nat.le_add_right j n) hE) (levelMeas_drops j n)
    calc uniformLaw π E ≤ 3 ^ n * uniformLaw π (E ∩ Drops π o x j n) :=
          measure_le_pow_three_mul_drops hox h3 hE n
      _ ≤ 3 ^ n * (3 * uniformLaw π (E ∩ Drops π o x j n ∩ Drop π o x (j + n))) := by
          gcongr
          exact measure_le_three_mul_drop hox h3 hE'
      _ = 3 ^ (n + 1) * uniformLaw π (E ∩ Drops π o x j (n + 1)) := by
          rw [pow_succ, mul_assoc, Drops, ← Set.inter_assoc]

variable (π o x) in
/-- The first `k` blocks of `N` fresh steps occur and none consists of drops only. -/
def Bad (N k : ℕ) : Set (Config G) :=
  {ρ | Reach π o x (k * N) ρ ∧ ∀ b < k, ρ ∉ Drops π o x (b * N) N}

omit [Countable V] in
theorem levelMeas_bad (N k : ℕ) : LevelMeas π o x (k * N) (Bad π o x N k) := by
  intro h hh ρ hρ ρ' hρ' ⟨hr, hb⟩
  refine ⟨levelMeas_reach (k * N) h hh ρ hρ ρ' hρ' hr, fun b hbk hρ'D => hb b hbk ?_⟩
  have hlev : LevelMeas π o x (k * N) (Drops π o x (b * N) N) :=
    levelMeas_of_le (by nlinarith) (levelMeas_drops (b * N) N)
  exact hlev h hh ρ' hρ' ρ hρ hρ'D

omit [Countable V] in
theorem bad_succ_subset (N k : ℕ) :
    Bad π o x N (k + 1) ⊆ Bad π o x N k \ Drops π o x (k * N) N := by
  rintro ρ ⟨hr, hb⟩
  refine ⟨⟨reach_mono (by nlinarith) hr, fun b hbk => hb b (by omega)⟩, hb k (lt_add_one k)⟩

omit [Countable V] in
theorem measure_bad_zero_le (N : ℕ) : uniformLaw π (Bad π o x N 0) ≤ 1 := by
  calc uniformLaw π (Bad π o x N 0) ≤ uniformLaw π Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem measure_bad_succ_le (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) (N k : ℕ) :
    uniformLaw π (Bad π o x N (k + 1)) ≤
      (1 - (3 : ENNReal)⁻¹ ^ N) * uniformLaw π (Bad π o x N k) := by
  have hlev := levelMeas_bad (π := π) (o := o) (x := x) N k
  have hm := measurableSet_of_levelMeas hlev
  have hmD : MeasurableSet (Drops π o x (k * N) N) :=
    measurableSet_of_levelMeas (levelMeas_drops (k * N) N)
  have hge : (3 : ENNReal)⁻¹ ^ N * uniformLaw π (Bad π o x N k) ≤
      uniformLaw π (Bad π o x N k ∩ Drops π o x (k * N) N) := by
    have := measure_le_pow_three_mul_drops hox h3 hlev N
    rw [← ENNReal.inv_pow, ENNReal.inv_mul_le_iff (pow_ne_zero _ (by norm_num))
      (ENNReal.pow_ne_top (by norm_num))]
    exact this
  calc uniformLaw π (Bad π o x N (k + 1))
      ≤ uniformLaw π (Bad π o x N k \ Drops π o x (k * N) N) :=
        measure_mono (bad_succ_subset N k)
    _ = uniformLaw π (Bad π o x N k) - uniformLaw π (Bad π o x N k ∩ Drops π o x (k * N) N) := by
        rw [← Set.sdiff_self_inter, measure_sdiff Set.inter_subset_left
          (hm.inter hmD).nullMeasurableSet (measure_ne_top _ _)]
    _ ≤ uniformLaw π (Bad π o x N k) - (3 : ENNReal)⁻¹ ^ N * uniformLaw π (Bad π o x N k) :=
        tsub_le_tsub_left hge _
    _ = (1 - (3 : ENNReal)⁻¹ ^ N) * uniformLaw π (Bad π o x N k) := by
        rw [ENNReal.sub_mul (fun _ _ => measure_ne_top _ _), one_mul]

theorem measure_bad_le (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) (N : ℕ) :
    ∀ k : ℕ, uniformLaw π (Bad π o x N k) ≤ (1 - (3 : ENNReal)⁻¹ ^ N) ^ k
  | 0 => by simpa using measure_bad_zero_le (π := π) (o := o) (x := x) N
  | k + 1 => by
    calc uniformLaw π (Bad π o x N (k + 1))
        ≤ (1 - (3 : ENNReal)⁻¹ ^ N) * uniformLaw π (Bad π o x N k) := measure_bad_succ_le hox h3 N k
      _ ≤ (1 - (3 : ENNReal)⁻¹ ^ N) * (1 - (3 : ENNReal)⁻¹ ^ N) ^ k := by
          gcongr
          exact measure_bad_le hox h3 N k
      _ = (1 - (3 : ENNReal)⁻¹ ^ N) ^ (k + 1) := by rw [pow_succ, mul_comm]

theorem measure_iInter_bad (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) (N : ℕ) :
    uniformLaw π (⋂ k, Bad π o x N k) = 0 := by
  have hθ : (1 - (3 : ENNReal)⁻¹ ^ N) < 1 := by
    apply ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
    exact pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by norm_num))
  have ht : Filter.Tendsto (fun k : ℕ => (1 - (3 : ENNReal)⁻¹ ^ N) ^ k) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_iff.2 hθ
  refine le_antisymm (ge_of_tendsto' ht (fun k => ?_)) (zero_le)
  exact (measure_mono (Set.iInter_subset _ k)).trans (measure_bad_le hox h3 N k)

omit [Countable V] in
/-- If the queue stays below `N` at every fresh step and every fresh step occurs, then no
block of `N` fresh steps consists of drops only. -/
theorem mem_bad_of_forall {N : ℕ} {ρ : Config G} (hr : ∀ j, Reach π o x j ρ)
    (hY : ∀ i, Y π o x i ρ < N) (k : ℕ) : ρ ∈ Bad π o x N k := by
  refine ⟨hr _, fun b _ hD => ?_⟩
  rw [mem_drops] at hD
  have key : ∀ i ≤ N, Y π o x (b * N + i) ρ + i ≤ Y π o x (b * N) ρ := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hd := hD i (by omega)
      simp only [Drop, Set.mem_setOf_eq] at hd
      rcases hd with hd | hd
      · exact absurd (hr _) hd
      · have := ih (by omega)
        show Y π o x (b * N + i + 1) ρ + (i + 1) ≤ Y π o x (b * N) ρ
        omega
  have := key N le_rfl
  have := hY (b * N)
  omega

/-- Almost surely only finitely many vertices are reached. -/
theorem measure_reach_all (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) :
    uniformLaw π {ρ | ∀ j, Reach π o x j ρ} = 0 := by
  refine le_antisymm ?_ (zero_le)
  refine ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero (fun N => ?_)
  have hsub : {ρ : Config G | ∀ j, Reach π o x j ρ} ⊆
      {ρ | ∃ i, N ≤ Y π o x i ρ} ∪ ⋂ k, Bad π o x N k := by
    intro ρ hρ
    by_cases hY : ∃ i, N ≤ Y π o x i ρ
    · exact Or.inl hY
    · push Not at hY
      exact Or.inr (Set.mem_iInter.2 (mem_bad_of_forall hρ hY))
  calc uniformLaw π {ρ : Config G | ∀ j, Reach π o x j ρ}
      ≤ uniformLaw π ({ρ | ∃ i, N ≤ Y π o x i ρ} ∪ ⋂ k, Bad π o x N k) := measure_mono hsub
    _ ≤ uniformLaw π {ρ | ∃ i, N ≤ Y π o x i ρ} + uniformLaw π (⋂ k, Bad π o x N k) :=
        measure_union_le _ _
    _ ≤ (N : ENNReal)⁻¹ + 0 :=
        add_le_add (measure_exists_stop_le hox h3) (measure_iInter_bad hox h3 N).le
    _ = (N : ENNReal)⁻¹ := add_zero _

end Blocks



end Rotor
