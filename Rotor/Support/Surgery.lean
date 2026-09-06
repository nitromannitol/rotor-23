import Rotor.Support.MarkedModel

open Classical

namespace Rotor

/-! ### Prefixes, suffixes, concatenations of open paths -/

theorem isOpenPath_take {ω : BondConfig} {l : List Site} (h : IsOpenPath ω l) (n : ℕ) :
    IsOpenPath ω (l.take n) := by
  have h1 : (l.take n ++ l.drop n).IsChain squareGraph.Adj := by
    rw [List.take_append_drop]; exact h.1.2
  have h2 : (l.take n ++ l.drop n).IsChain (fun u v => ω s(u, v) = true) := by
    rw [List.take_append_drop]; exact h.2
  exact ⟨⟨List.Nodup.sublist (List.take_sublist n l) h.1.1, (List.isChain_append.1 h1).1⟩,
    (List.isChain_append.1 h2).1⟩

theorem isOpenPath_drop {ω : BondConfig} {l : List Site} (h : IsOpenPath ω l) (n : ℕ) :
    IsOpenPath ω (l.drop n) := by
  have h1 : (l.take n ++ l.drop n).IsChain squareGraph.Adj := by
    rw [List.take_append_drop]; exact h.1.2
  have h2 : (l.take n ++ l.drop n).IsChain (fun u v => ω s(u, v) = true) := by
    rw [List.take_append_drop]; exact h.2
  exact ⟨⟨List.Nodup.sublist (List.drop_sublist n l) h.1.1, (List.isChain_append.1 h1).2.1⟩,
    (List.isChain_append.1 h2).2.1⟩

theorem traverses_of_take {l w : List Site} {n : ℕ} (h : Traverses (l.take n) w) : Traverses l w := by
  obtain ⟨i, h⟩ := h
  have key : ∀ w' : List Site, w'.length = w.length → ((l.take n).drop i).take w.length = w' →
      (l.drop i).take w.length = w' := by
    intro w' hw' hwin
    rw [window_iff hw'] at hwin ⊢
    intro j hj
    have := hwin j hj
    have hlt : i + j < n := by
      have h2 : w'[j]? = some (w'[j]'(by omega)) := List.getElem?_eq_getElem _
      rw [h2, List.getElem?_take] at this
      by_contra hc
      rw [if_neg hc] at this
      exact absurd this (by simp)
    rw [List.getElem?_take, if_pos hlt] at this
    exact this
  rcases h with h | h
  · exact ⟨i, Or.inl (key w rfl h)⟩
  · exact ⟨i, Or.inr (key w.reverse List.length_reverse h)⟩

theorem traverses_of_drop {l w : List Site} {n : ℕ} (h : Traverses (l.drop n) w) : Traverses l w := by
  obtain ⟨i, h⟩ := h
  have key : ∀ w' : List Site, w'.length = w.length → ((l.drop n).drop i).take w.length = w' →
      (l.drop (n + i)).take w.length = w' := by
    intro w' hw' hwin
    rw [window_iff hw'] at hwin ⊢
    intro j hj
    have := hwin j hj
    rw [List.getElem?_drop] at this
    rw [show n + i + j = n + (i + j) by omega]
    exact this
  rcases h with h | h
  · exact ⟨n + i, Or.inl (key w rfl h)⟩
  · exact ⟨n + i, Or.inr (key w.reverse List.length_reverse h)⟩

theorem isOpenPath_of_qbonds {ω : BondConfig} {q : List Site} (hq : IsPath squareGraph q)
    (h : ∀ b, QBond q b → ω b = true) : IsOpenPath ω q := by
  refine ⟨hq, List.isChain_iff_getElem.2 (fun i hi => h _ ⟨i, q[i], q[i + 1],
    List.getElem?_eq_getElem _, List.getElem?_eq_getElem _, rfl⟩)⟩

/-- Concatenating three open paths whose junctions are open bonds. -/
theorem isOpenPath_append3 {ω : BondConfig} {l₁ l₂ l₃ : List Site} (h₁ : IsOpenPath ω l₁)
    (h₂ : IsOpenPath ω l₂) (h₃ : IsOpenPath ω l₃)
    (hd₁ : List.Disjoint l₁ l₂) (hd₂ : List.Disjoint l₁ l₃) (hd₃ : List.Disjoint l₂ l₃)
    (hj₁ : ∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, squareGraph.Adj a b ∧ ω s(a, b) = true)
    (hj₂ : ∀ a ∈ l₂.getLast?, ∀ b ∈ l₃.head?, squareGraph.Adj a b ∧ ω s(a, b) = true)
    (h₂ne : l₂ ≠ []) : IsOpenPath ω (l₁ ++ l₂ ++ l₃) := by
  have hlast : (l₁ ++ l₂).getLast? = l₂.getLast? := by
    rw [List.getLast?_append]
    rcases hl : l₂.getLast? with _ | t
    · exact absurd (List.getLast?_eq_none_iff.1 hl) h₂ne
    · rfl
  have hd₂₃ : List.Disjoint (l₁ ++ l₂) l₃ := List.disjoint_append_left.2 ⟨hd₂, hd₃⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.nodup_append, List.nodup_append]
    exact ⟨⟨h₁.1.1, h₂.1.1, fun a ha b hb hab => hd₁ ha (hab ▸ hb)⟩, h₃.1.1,
      fun a ha b hb hab => hd₂₃ ha (hab ▸ hb)⟩
  · rw [List.isChain_append, List.isChain_append, hlast]
    exact ⟨⟨h₁.1.2, h₂.1.2, fun a ha b hb => (hj₁ a ha b hb).1⟩, h₃.1.2,
      fun a ha b hb => (hj₂ a ha b hb).1⟩
  · rw [List.isChain_append, List.isChain_append, hlast]
    exact ⟨⟨h₁.2, h₂.2, fun a ha b hb => (hj₁ a ha b hb).2⟩, h₃.2,
      fun a ha b hb => (hj₂ a ha b hb).2⟩

/-! ### The surgery -/

/-- The surgery for Lemma 5.3: given a pivotal bond `e` of the block `z`, modify the bonds
touching the block so that the mark of `z` becomes pivotal. -/
theorem surgery (x y : Site) (r : ℕ) {z : ℤ × ℤ} (hz : z ∈ Zset r) {e : Sym2 Site}
    (he : ∀ v ∈ e, InBlock (blockCorner x y z) v) (ω : BondConfig) (σ : ℤ × ℤ → Bool)
    {l : List Site}
    (hl : ValidPath x y (Dset x y r) (Zset r) (gridCopy x y) (Function.update ω e true) σ l)
    (hno : ∀ l', ¬ ValidPath x y (Dset x y r) (Zset r) (gridCopy x y)
      (Function.update ω e false) σ l') :
    ∃ ω' : BondConfig,
      (∀ b : Sym2 Site, (∀ v ∈ b, ¬ InBlock (blockCorner x y z) v) → ω' b = ω b) ∧
      (∃ l', ValidPath x y (Dset x y r) (Zset r) (gridCopy x y) ω' (Function.update σ z true) l') ∧
      ∀ l', ¬ ValidPath x y (Dset x y r) (Zset r) (gridCopy x y) ω'
        (Function.update σ z false) l' := by
  obtain ⟨hopen, hhead, hlast, hD, hmarks⟩ := hl
  set c := blockCorner x y z with hc
  have hnoOpen : ¬ IsOpenPath (Function.update ω e false) l :=
    fun h => hno l ⟨h, hhead, hlast, hD, hmarks⟩
  obtain ⟨k, hk, hke⟩ := exists_used_of_update hopen hnoOpen
  have hk0 : InBlock c l[k] := he _ (by rw [← hke]; exact Sym2.mem_mk_left _ _)
  have hk1 : InBlock c l[k + 1] := he _ (by rw [← hke]; exact Sym2.mem_mk_right _ _)
  -- first and last vertex of `l` in the block
  let P : ℕ → Prop := fun i => ∃ v, l[i]? = some v ∧ InBlock c v
  have hPk : P k := ⟨l[k], List.getElem?_eq_getElem _, hk0⟩
  have hPk1 : P (k + 1) := ⟨l[k + 1], List.getElem?_eq_getElem _, hk1⟩
  have hex : ∃ i, P i := ⟨k, hPk⟩
  set k₁ := Nat.find hex with hk₁def
  have hk₁ : P k₁ := Nat.find_spec hex
  have hk₁min : ∀ i, i < k₁ → ¬ P i := fun i hi => Nat.find_min hex hi
  have hk₁le : k₁ ≤ k := Nat.find_min' hex hPk
  set k₂ := Nat.findGreatest P (l.length - 1) with hk₂def
  have hk₂ : P k₂ := Nat.findGreatest_spec (P := P) (by omega : k + 1 ≤ l.length - 1) hPk1
  have hk₂max : ∀ i, k₂ < i → i ≤ l.length - 1 → ¬ P i :=
    fun i hi hi' => Nat.findGreatest_is_greatest hi hi'
  have hk₂ge : k + 1 ≤ k₂ := Nat.le_findGreatest (by omega) hPk1
  have hk₂le : k₂ ≤ l.length - 1 := Nat.findGreatest_le _
  obtain ⟨s, hs, hsB⟩ := hk₁
  obtain ⟨t, ht, htB⟩ := hk₂
  have hsl : k₁ < l.length := (List.getElem?_eq_some_iff.1 hs).1
  have htl : k₂ < l.length := (List.getElem?_eq_some_iff.1 ht).1
  have hst : s ≠ t := by
    intro hst
    have : k₁ = k₂ := (List.getElem?_inj hsl hopen.1.1).1 (hs.trans (hst ▸ ht.symm))
    omega
  have hx0 : l[0]? = some x := by rw [← List.head?_eq_getElem?]; exact hhead
  have hyl : l[l.length - 1]? = some y := by rw [← List.getLast?_eq_getElem?]; exact hlast
  -- `s` and `t` lie on the boundary of the block
  have hsBd : OnBdry c s := by
    rcases Nat.eq_zero_or_pos k₁ with h0 | hpos
    · rw [h0, hx0] at hs
      have hsx : s = x := (Option.some.inj hs).symm
      rw [hsx]; rw [hsx] at hsB
      exact onBdry_of_col x y z hsB rfl
    · obtain ⟨u, hu⟩ : ∃ u, l[k₁ - 1]? = some u := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have huB : ¬ InBlock c u := fun hB => hk₁min (k₁ - 1) (by omega) ⟨u, hu, hB⟩
      have hadj : squareGraph.Adj u s :=
        isChain_getElem? hopen.1.2 hu (by rw [show k₁ - 1 + 1 = k₁ by omega]; exact hs)
      exact onBdry_of_adj_not hsB huB hadj.symm
  have htBd : OnBdry c t := by
    rcases eq_or_lt_of_le hk₂le with hlast' | hlt
    · rw [hlast', hyl] at ht
      have hty : t = y := (Option.some.inj ht).symm
      rw [hty]; rw [hty] at htB
      exact onBdry_of_row x y z htB rfl
    · obtain ⟨u, hu⟩ : ∃ u, l[k₂ + 1]? = some u := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have huB : ¬ InBlock c u := fun hB => hk₂max (k₂ + 1) (by omega) (by omega) ⟨u, hu, hB⟩
      have hadj : squareGraph.Adj t u := isChain_getElem? hopen.1.2 ht hu
      exact onBdry_of_adj_not htB huB hadj
  -- the route
  obtain ⟨q, hqP, hqh, hql, hqB, hqT⟩ := block_route c hsBd htBd hst
  have hqne : q ≠ [] := by rintro rfl; simp at hqh
  have hq0 : q[0]? = some s := by rw [← List.head?_eq_getElem?]; exact hqh
  have hqlast : q[q.length - 1]? = some t := by rw [← List.getLast?_eq_getElem?]; exact hql
  have hqlen : 2 ≤ q.length := by
    by_contra hcon
    have h1 : q.length = 1 := by
      have : 0 < q.length := List.length_pos_iff.2 hqne
      omega
    rw [h1] at hqlast
    exact hst (Option.some.inj (hq0.symm.trans hqlast))
  -- the pieces of `l` outside the window are outside the block
  have htake : ∀ v ∈ l.take k₁, ¬ InBlock c v := by
    intro v hv hB
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
    rw [List.getElem?_take] at hi
    split_ifs at hi with hik
    · exact hk₁min i hik ⟨v, hi, hB⟩
  have hdrop : ∀ v ∈ l.drop (k₂ + 1), ¬ InBlock c v := by
    intro v hv hB
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
    rw [List.getElem?_drop] at hi
    have := (List.getElem?_eq_some_iff.1 hi).1
    exact hk₂max (k₂ + 1 + i) (by omega) (by omega) ⟨v, hi, hB⟩
  -- agreement lemmas for the surgery configuration
  have hagreeOut : ∀ b : Sym2 Site, (∀ v ∈ b, ¬ InBlock c v) →
      surgeryConfig ω q e b = ω b := by
    intro b hb
    apply surgeryConfig_eq_of_not
    · rintro ⟨i, u, v, hu, hv, rfl⟩
      exact hb u (Sym2.mem_mk_left _ _) (hqB u (List.mem_of_getElem? hu))
    · intro hT
      obtain ⟨v, hvb, hvq⟩ := touchesInternal_mem hT
      exact hb v hvb (hqB v hvq)
    · rintro rfl
      exact hb _ (by rw [← hke]; exact Sym2.mem_mk_left _ _) hk0
  have hagreeEnd : ∀ (u w : Site), ¬ InBlock c u →
      (q[0]? = some w ∨ q[q.length - 1]? = some w) → surgeryConfig ω q e s(u, w) = ω s(u, w) := by
    intro u w hu hw
    apply surgeryConfig_eq_of_not
    · rintro ⟨i, a, b, ha, hb, hab⟩
      rcases Sym2.eq_iff.1 hab with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hu (hqB _ (List.mem_of_getElem? ha))
      · exact hu (hqB _ (List.mem_of_getElem? hb))
    · rintro ⟨i, hi, hi', v, hv, hvb⟩
      rcases Sym2.mem_iff.1 hvb with rfl | rfl
      · exact hu (hqB _ (List.mem_of_getElem? hv))
      · rcases hw with hw | hw
        · have : i = 0 := (List.getElem?_inj (by omega) hqP.1).1 (hv.trans hw.symm); omega
        · have : i = q.length - 1 := (List.getElem?_inj (by omega) hqP.1).1 (hv.trans hw.symm); omega
    · intro h; exact hu (he u (by rw [← h]; exact Sym2.mem_mk_left _ _))
  refine ⟨surgeryConfig ω q e, hagreeOut, ?_, ?_⟩
  · -- the new path
    refine ⟨l.take k₁ ++ q ++ l.drop (k₂ + 1), ?_, ?_, ?_, ?_, ?_⟩
    · refine isOpenPath_append3 ?_
        (isOpenPath_of_qbonds hqP (fun b hb => surgeryConfig_of_qbond hb)) ?_ ?_ ?_ ?_ ?_ ?_ hqne
      · refine isOpenPath_of_agree (isOpenPath_take hopen k₁) (fun i hi => ?_)
        have hb : ∀ v ∈ s((l.take k₁)[i], (l.take k₁)[i + 1]), ¬ InBlock c v := by
          intro v hv
          rcases Sym2.mem_iff.1 hv with rfl | rfl
          · exact htake _ (List.getElem_mem _)
          · exact htake _ (List.getElem_mem _)
        rw [hagreeOut _ hb, Function.update_of_ne]
        rintro rfl
        exact hb _ (by rw [← hke]; exact Sym2.mem_mk_left _ _) hk0
      · refine isOpenPath_of_agree (isOpenPath_drop hopen (k₂ + 1)) (fun i hi => ?_)
        have hb : ∀ v ∈ s((l.drop (k₂ + 1))[i], (l.drop (k₂ + 1))[i + 1]), ¬ InBlock c v := by
          intro v hv
          rcases Sym2.mem_iff.1 hv with rfl | rfl
          · exact hdrop _ (List.getElem_mem _)
          · exact hdrop _ (List.getElem_mem _)
        rw [hagreeOut _ hb, Function.update_of_ne]
        rintro rfl
        exact hb _ (by rw [← hke]; exact Sym2.mem_mk_left _ _) hk0
      · exact fun v hv hvq => htake v hv (hqB v hvq)
      · intro v hv hv'
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hv
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hv'
        rw [List.getElem?_take] at hi
        rw [List.getElem?_drop] at hj
        split_ifs at hi with hik
        · have := (List.getElem?_inj (List.getElem?_eq_some_iff.1 hi).1 hopen.1.1).1 (hi.trans hj.symm)
          omega
      · exact fun v hv hv' => hdrop v hv' (hqB v hv)
      · intro a ha b hb
        rw [hqh] at hb
        have hbs : b = s := (Option.mem_some_iff.1 hb).symm
        rw [hbs]
        rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hsl.le,
          List.getElem?_take] at ha
        split_ifs at ha with hpos
        · have ha' : l[k₁ - 1]? = some a := Option.mem_def.1 ha
          have hs' : l[k₁ - 1 + 1]? = some s := by rw [show k₁ - 1 + 1 = k₁ by omega]; exact hs
          refine ⟨isChain_getElem? hopen.1.2 ha' hs', ?_⟩
          have haB : ¬ InBlock c a := fun hB => hk₁min (k₁ - 1) (by omega) ⟨a, ha', hB⟩
          rw [hagreeEnd a s haB (Or.inl hq0)]
          have := isChain_getElem? hopen.2 ha' hs'
          rwa [Function.update_of_ne (fun h => haB (he a (by rw [← h]; exact Sym2.mem_mk_left _ _)))]
            at this
        · simp at ha
      · intro a ha b hb
        rw [hql] at ha
        have hat : a = t := (Option.mem_some_iff.1 ha).symm
        rw [hat]
        rw [List.head?_drop] at hb
        have hb' : l[k₂ + 1]? = some b := Option.mem_def.1 hb
        refine ⟨isChain_getElem? hopen.1.2 ht hb', ?_⟩
        have hbB : ¬ InBlock c b := fun hB => hk₂max (k₂ + 1) (by omega)
          (by have := (List.getElem?_eq_some_iff.1 hb').1; omega) ⟨b, hb', hB⟩
        rw [Sym2.eq_swap, hagreeEnd b t hbB (Or.inr hqlast), Sym2.eq_swap]
        have := isChain_getElem? hopen.2 ht hb'
        rwa [Function.update_of_ne (fun h => hbB (he b (by rw [← h]; exact Sym2.mem_mk_right _ _)))]
          at this
    · rw [List.head?_append, List.head?_append]
      rcases Nat.eq_zero_or_pos k₁ with h0 | hpos
      · rw [h0, List.take_zero]
        have hsx : s = x := by rw [h0, hx0] at hs; exact (Option.some.inj hs).symm
        rw [hqh, hsx]; rfl
      · have : (l.take k₁).head? = some x := by
          rw [List.head?_eq_getElem?, List.getElem?_take, if_pos hpos, hx0]
        rw [this]; rfl
    · rw [List.getLast?_append, List.getLast?_append, hql]
      rcases eq_or_lt_of_le hk₂le with hlast' | hlt
      · have hdropnil : l.drop (k₂ + 1) = [] := List.drop_eq_nil_of_le (by omega)
        have hty : t = y := by rw [hlast', hyl] at ht; exact (Option.some.inj ht).symm
        rw [hdropnil, hty]; rfl
      · have : (l.drop (k₂ + 1)).getLast? = some y := by
          rw [List.getLast?_eq_getElem?, List.length_drop, List.getElem?_drop,
            show k₂ + 1 + (l.length - (k₂ + 1) - 1) = l.length - 1 by omega]
          exact hyl
        rw [this]; rfl
    · intro v hv
      simp only [List.mem_append] at hv
      rcases hv with (hv | hv) | hv
      · exact hD v (List.mem_of_mem_take hv)
      · exact mem_Dset_of_inBlock hz (hqB v hv)
      · exact hD v (List.mem_of_mem_drop hv)
    · intro z' hz' hT
      by_cases hzz : z' = z
      · rw [hzz, Function.update_self]
      · rw [Function.update_of_ne hzz]
        apply hmarks z' hz'
        have hcp : ∀ v ∈ gridCopy x y z', v ∉ q := fun v hv hvq =>
          hzz (eq_of_inBlock_interiorB x y (hqB v hvq) (interiorB_of_mem_copyAt hv)).symm
        rcases traverses_append_of_disjoint hT hcp hqne with h | h
        · exact traverses_of_take h
        · exact traverses_of_drop h
  · -- no valid path once the mark is removed
    intro p hp
    obtain ⟨hpo, hph, hpl, hpD, hpm⟩ := hp
    by_cases huse : ∃ i, ∃ hi : i + 1 < p.length, QBond q s(p[i], p[i + 1])
    · obtain ⟨i, hi, j, u, v, hju, hjv, hb⟩ := huse
      have hj : j + 1 < q.length := (List.getElem?_eq_some_iff.1 hjv).1
      have hends : EndsOff q p := by
        intro m hm hm'
        obtain ⟨w, hw⟩ : ∃ w, q[m]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hwB : InBlock c w := hqB w (List.mem_of_getElem? hw)
        rw [hw]
        constructor
        · intro hxw
          rw [hph] at hxw
          have hxw' : x = w := Option.some.inj hxw
          have h0 : k₁ ≤ 0 := Nat.find_min' hex ⟨w, by rw [← hxw']; exact hx0, hwB⟩
          have hk₁0 : k₁ = 0 := by omega
          rw [hk₁0, hx0] at hs
          have hsx : x = s := Option.some.inj hs
          have : 0 = m := (List.getElem?_inj (by omega) hqP.1).1 
            (by rw [hq0, hw, ← hsx, hxw'])
          omega
        · intro hyw
          rw [hpl] at hyw
          have hyw' : y = w := Option.some.inj hyw
          have hge : l.length - 1 ≤ k₂ :=
            Nat.le_findGreatest le_rfl ⟨w, by rw [← hyw']; exact hyl, hwB⟩
          have hk₂' : k₂ = l.length - 1 := by omega
          rw [hk₂', hyl] at ht
          have hty : y = t := Option.some.inj ht
          have : q.length - 1 = m := (List.getElem?_inj (by omega) hqP.1).1 
            (by rw [hqlast, hw, ← hty, hyw'])
          omega
      have hTq : Traverses p q := by
        refine traverses_of_forced _ (forcedPath_surgery ω hqP.1 e) hpo hends hi hj ?_
        rcases Sym2.eq_iff.1 hb with ⟨h0, h1⟩ | ⟨h0, h1⟩
        · left
          exact ⟨by rw [List.getElem?_eq_getElem (by omega : i < p.length), h0, hju],
            by rw [List.getElem?_eq_getElem hi, h1, hjv]⟩
        · right
          exact ⟨by rw [List.getElem?_eq_getElem (by omega : i < p.length), h0, hjv],
            by rw [List.getElem?_eq_getElem hi, h1, hju]⟩
      have hTc : Traverses p (gridCopy x y z) := traverses_trans hTq hqT
      have := hpm z hz hTc
      rw [Function.update_self] at this
      exact Bool.false_ne_true this
    · push Not at huse
      apply hno p
      refine ⟨?_, hph, hpl, hpD, ?_⟩
      · refine isOpenPath_mono hpo (fun i hi hop => ?_)
        rw [surgeryConfig_true_iff] at hop
        rcases hop with hQ | ⟨-, hne, hω⟩
        · exact absurd hQ (huse i hi)
        · rw [Function.update_of_ne hne]; exact hω
      · intro z' hz' hT
        by_cases hzz : z' = z
        · exfalso
          rw [hzz] at hT
          have h6 : (gridCopy x y z).length = 6 := copyAt_length _
          have h6' : (copyAt c).length = 6 := copyAt_length _
          obtain ⟨m, hm, hm'⟩ := traverses_pair hT (i := 0)
            (by rw [h6]; omega)
          obtain ⟨a, ha⟩ : ∃ a, (gridCopy x y z)[0]? = some a :=
            ⟨_, List.getElem?_eq_getElem (by rw [h6]; omega)⟩
          obtain ⟨b, hb⟩ : ∃ b, (gridCopy x y z)[0 + 1]? = some b :=
            ⟨_, List.getElem?_eq_getElem (by rw [h6]; omega)⟩
          have hQ : QBond q s(a, b) :=
            qbond_of_traverses hqT (by rw [h6']; omega) ha hb
          apply huse m hm
          have hpm0 : p[m]? = some p[m] := List.getElem?_eq_getElem (by omega)
          have hpm1 : p[m + 1]? = some p[m + 1] := List.getElem?_eq_getElem hm
          rcases hm' with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · have e0 : p[m] = a := Option.some.inj (hpm0.symm.trans (h0.trans ha))
            have e1 : p[m + 1] = b := Option.some.inj (hpm1.symm.trans (h1.trans hb))
            rw [e0, e1]; exact hQ
          · have e0 : p[m] = b := Option.some.inj (hpm0.symm.trans (h0.trans hb))
            have e1 : p[m + 1] = a := Option.some.inj (hpm1.symm.trans (h1.trans ha))
            rw [e0, e1, Sym2.eq_swap]; exact hQ
        · have := hpm z' hz' hT
          rwa [Function.update_of_ne hzz] at this

end Rotor
