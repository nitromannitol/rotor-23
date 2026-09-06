import Rotor.Support.SelfAvoiding

/-!
Existence of a stuck extension within a bounded number of steps, `rotor.tex:1408-1418`:
"a nonbacktracking walk with distinct vertices, all of degree three, has two continuations at
every step … From every directed edge, some nonbacktracking walk of at most `m` steps therefore
repeats a vertex or reaches a vertex of degree at most two: otherwise two distinct continuations
of length `⌊m/2⌋` have the same endpoint, and following one to that endpoint and the other in
reverse gives such a repetition."
-/

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

theorem mem_NodupExt_iff {l : List V} (hl : Adm G l) {n : ℕ} {q : List V} :
    q ∈ NodupExt G l n ↔ q.length = l.length + n ∧ q.drop n = l ∧ q.Nodup ∧ q.IsChain G.Adj := by
  constructor
  · intro h
    obtain ⟨hnd, hch, -⟩ := adm_of_mem_NodupExt hl h
    exact ⟨length_of_mem_NodupExt h, drop_of_mem_NodupExt h, hnd, hch⟩
  · induction n generalizing q with
    | zero =>
      rintro ⟨-, hdrop, -, -⟩
      simp only [List.drop_zero] at hdrop
      simp [hdrop]
    | succ n ih =>
      rintro ⟨hlen, hdrop, hnd, hch⟩
      match q with
      | [] => simp only [List.length_nil] at hlen; omega
      | c :: q'' =>
        rw [List.drop_succ_cons] at hdrop
        have hq'' : q'' ∈ NodupExt G l n := ih ⟨by simp only [List.length_cons] at hlen; omega,
          hdrop, hnd.of_cons, hch.of_cons⟩
        obtain ⟨-, -, hlen2⟩ := adm_of_mem_NodupExt hl hq''
        match q'' with
        | [] => simp at hlen2
        | b :: rest =>
          rw [NodupExt_succ, mem_biUnion]
          refine ⟨b :: rest, hq'', (mem_ext1_cons).2 ⟨hch.rel.symm, (List.nodup_cons.1 hnd).1⟩⟩

theorem exists_cons_of_mem_NodupExt_succ {l : List V} {n : ℕ} {q : List V}
    (h : q ∈ NodupExt G l (n + 1)) : ∃ c t, q = c :: t ∧ t ∈ NodupExt G l n := by
  rw [NodupExt_succ, mem_biUnion] at h
  obtain ⟨t, ht, hq⟩ := h
  obtain ⟨b, rest, c, rfl, -, -, rfl⟩ := exists_of_mem_ext1 hq
  exact ⟨c, b :: rest, rfl, ht⟩

theorem mem_of_mem_NodupExt {l : List V} {n : ℕ} {q : List V} (h : q ∈ NodupExt G l n)
    {x : V} (hx : x ∈ l) : x ∈ q := by
  rw [← drop_of_mem_NodupExt h] at hx
  exact List.mem_of_mem_drop hx

/-- Two distinct neighbours of the head already on the path leave at most one
continuation. -/
theorem stuck_of_two_nbrs (h3 : ∀ v : V, G.degree v ≤ 3) {b : V} {rest : List V} {a w : V}
    (ha : a ∈ rest) (hw : w ∈ rest) (hne : a ≠ w) (hba : G.Adj b a) (hbw : G.Adj b w) :
    Stuck G (b :: rest) := by
  refine ⟨b, rest, rfl, ?_⟩
  have hsub : {a, w} ⊆ (G.neighborFinset b).filter (fun c => c ∈ b :: rest) := by
    intro c hc
    simp only [mem_insert, mem_singleton] at hc
    rw [mem_filter, SimpleGraph.mem_neighborFinset]
    rcases hc with rfl | rfl
    · exact ⟨hba, List.mem_cons_of_mem _ ha⟩
    · exact ⟨hbw, List.mem_cons_of_mem _ hw⟩
  have h2 : 2 ≤ ((G.neighborFinset b).filter (fun c => c ∈ b :: rest)).card := by
    have := card_le_card hsub
    rwa [card_pair hne] at this
  have hsum := card_filter_add_card_filter_not (s := G.neighborFinset b)
    (fun c => c ∈ b :: rest)
  rw [G.card_neighborFinset_eq_degree] at hsum
  have := h3 b
  omega

theorem card_ext1 (b : V) (rest : List V) :
    (ext1 G (b :: rest)).card = ((G.neighborFinset b).filter (fun c => c ∉ b :: rest)).card := by
  rw [ext1]
  exact card_image_of_injective _ (fun x y hxy => by simpa using hxy)

theorem two_le_card_ext1 {q : List V} (hq : Adm G q) (hs : ¬ Stuck G q) : 2 ≤ (ext1 G q).card := by
  obtain ⟨-, -, hlen⟩ := hq
  match q with
  | [] => simp at hlen
  | b :: rest =>
    rw [card_ext1]
    by_contra hlt
    exact hs ⟨b, rest, rfl, by omega⟩

/-- Unstuck paths have at least two continuations, so the count doubles at every step. -/
theorem two_pow_le_card_NodupExt {l : List V} (hl : Adm G l) :
    ∀ h : ℕ, (∀ j < h, ∀ q ∈ NodupExt G l j, ¬ Stuck G q) → 2 ^ h ≤ (NodupExt G l h).card
  | 0, _ => by simp
  | h + 1, hno => by
    rw [NodupExt_succ, card_biUnion (fun q _ q' _ hne => ext1_disjoint hne)]
    have hrec := two_pow_le_card_NodupExt hl h (fun j hj => hno j (by omega))
    have h2 : (NodupExt G l h).card • 2 ≤ ∑ q ∈ NodupExt G l h, (ext1 G q).card :=
      card_nsmul_le_sum _ _ _ (fun q hq =>
        two_le_card_ext1 (adm_of_mem_NodupExt hl hq) (hno h (lt_add_one h) q hq))
    rw [smul_eq_mul] at h2
    calc 2 ^ (h + 1) = 2 ^ h * 2 := pow_succ 2 h
      _ ≤ (NodupExt G l h).card * 2 := Nat.mul_le_mul_right 2 hrec
      _ ≤ _ := h2

/-- Pushing a walk onto a path until it meets the path: either a stuck extension appears
before the meeting point, or the walk's first vertex is the second vertex of the path. -/
theorem push (h3 : ∀ v : V, G.degree v ≤ 3) (v₀ : V) : ∀ (u : List V) (p : List V) (k : ℕ),
    Adm G p → u.IsChain G.Adj → u.Nodup → (∀ x ∈ u.head?, G.Adj (p.headD v₀) x) →
    p.headD v₀ ∉ u → (∃ x ∈ u.take k, x ∈ p) →
    (∃ j < k, ∃ q ∈ NodupExt G p j, Stuck G q) ∨ (∃ x ∈ u.head?, ∃ y p', p = p.headD v₀ :: y :: p' ∧ x = y)
  | [], p, k, _, _, _, _, _, hmeet => by simp at hmeet
  | x :: u', p, k, hp, hch, hnd, hadj, hz, hmeet => by
    obtain ⟨hpnd, hpch, hplen⟩ := hp
    match p, hplen with
    | [], hplen => simp at hplen
    | [_], hplen => simp at hplen
    | z :: y :: p', _ =>
      simp only [List.headD_cons] at hadj hz
      have hzx : G.Adj z x := hadj x rfl
      by_cases hxp : x ∈ z :: y :: p'
      · by_cases hxy : x = y
        · right
          exact ⟨x, rfl, y, p', rfl, hxy⟩
        · left
          have hx' : x ∈ y :: p' := by
            rcases List.mem_cons.1 hxp with rfl | h
            · exact absurd List.mem_cons_self hz
            · exact h
          have hk : 0 < k := by
            rcases k with _ | k
            · simp at hmeet
            · exact Nat.succ_pos k
          refine ⟨0, hk, z :: y :: p', by simp, ?_⟩
          exact stuck_of_two_nbrs h3 List.mem_cons_self hx' (Ne.symm hxy) hpch.rel hzx
      · -- push x onto p
        have hp₁ : Adm G (x :: z :: y :: p') :=
          ⟨List.nodup_cons.2 ⟨hxp, hpnd⟩, List.isChain_cons.2 ⟨fun w hw => by
            simp at hw; subst hw; exact hzx.symm, hpch⟩, by simp⟩
        have hmem₁ : x :: z :: y :: p' ∈ NodupExt G (z :: y :: p') 1 := by
          rw [NodupExt_succ, NodupExt_zero, singleton_biUnion]
          exact (mem_ext1_cons).2 ⟨hzx, hxp⟩
        rcases k with _ | k
        · simp at hmeet
        obtain ⟨x', hx'u, hx'p⟩ := hmeet
        have hx'u' : x' ∈ u'.take k := by
          rw [List.take_succ_cons, List.mem_cons] at hx'u
          rcases hx'u with rfl | h
          · exact absurd hx'p hxp
          · exact h
        have hih := push h3 v₀ u' (x :: z :: y :: p') k hp₁ hch.of_cons hnd.of_cons
          (fun w hw => by simp only [List.headD_cons]; exact hch.rel_head? hw)
          (by simp only [List.headD_cons]; exact (List.nodup_cons.1 hnd).1)
          ⟨x', hx'u', List.mem_cons_of_mem _ hx'p⟩
        rcases hih with ⟨j, hj, q, hq, hs⟩ | ⟨w, hw, y', p'', hp'', hwy⟩
        · left
          refine ⟨1 + j, by omega, q, ?_, hs⟩
          rw [NodupExt_add, mem_biUnion]
          exact ⟨_, hmem₁, hq⟩
        · exfalso
          simp only [List.headD_cons, List.cons.injEq] at hp''
          obtain ⟨-, rfl, -⟩ := hp''
          subst hwy
          have : w ∈ x :: u' := List.mem_cons_of_mem _ (List.mem_of_mem_head? hw)
          exact hz this

/-- `head` is injective on the extensions by `h` vertices when no extension within
`2h - 1` steps is stuck. -/
theorem headD_injOn (h3 : ∀ v : V, G.degree v ≤ 3) {q₀ : List V} (hq₀ : Adm G q₀) (v₀ : V) :
    ∀ h : ℕ, (∀ j ≤ 2 * h - 1, ∀ q ∈ NodupExt G q₀ j, ¬ Stuck G q) →
      ∀ q₁ ∈ NodupExt G q₀ h, ∀ q₂ ∈ NodupExt G q₀ h, q₁.headD v₀ = q₂.headD v₀ → q₁ = q₂
  | 0, _, q₁, hq₁, q₂, hq₂, _ => by
    simp only [NodupExt_zero, mem_singleton] at hq₁ hq₂
    rw [hq₁, hq₂]
  | h + 1, hno, q₁, hq₁, q₂, hq₂, hhead => by
    by_contra hne
    obtain ⟨z₁, t₁, rfl, ht₁⟩ := exists_cons_of_mem_NodupExt_succ hq₁
    obtain ⟨z₂, t₂, rfl, ht₂⟩ := exists_cons_of_mem_NodupExt_succ hq₂
    simp only [List.headD_cons] at hhead
    subst hhead
    have hne' : t₁ ≠ t₂ := fun h => hne (by rw [h])
    have hadm₁ := adm_of_mem_NodupExt hq₀ hq₁
    have hadm₂ := adm_of_mem_NodupExt hq₀ hq₂
    have hadmt₂ := adm_of_mem_NodupExt hq₀ ht₂
    -- the first vertex of `q₀` lies in `t₂.take (h + 1)` and in `z₁ :: t₁`
    have hq₀ne : q₀ ≠ [] := by
      obtain ⟨-, -, hl⟩ := hq₀
      intro h; simp [h] at hl
    have hmeet : ∃ x ∈ t₂.take (h + 1), x ∈ z₁ :: t₁ := by
      have hdrop := drop_of_mem_NodupExt ht₂
      have hlen := length_of_mem_NodupExt ht₂
      have hh : h < t₂.length := by
        rw [hlen]
        have := List.length_pos_iff.2 hq₀ne
        omega
      refine ⟨t₂[h], ?_, ?_⟩
      · have hlt : h < (t₂.take (h + 1)).length := by
          rw [List.length_take]; omega
        have := List.getElem_mem hlt
        rwa [List.getElem_take] at this
      · have h0 : 0 < (t₂.drop h).length := by rw [List.length_drop]; omega
        have hmem : (t₂.drop h)[0] ∈ q₀ := by
          rw [← hdrop]; exact List.getElem_mem h0
        rw [List.getElem_drop] at hmem
        exact List.mem_cons_of_mem _ (mem_of_mem_NodupExt ht₁ hmem)
    have hpush := push h3 v₀ t₂ (z₁ :: t₁) (h + 1) hadm₁ hadmt₂.2.1 hadmt₂.1
      (fun x hx => by simp only [List.headD_cons]; exact hadm₂.2.1.rel_head? hx)
      (by simp only [List.headD_cons]; exact (List.nodup_cons.1 hadm₂.1).1) hmeet
    rcases hpush with ⟨j, hj, q, hq, hs⟩ | ⟨w, hw, y, p', hp', hwy⟩
    · refine hno (h + 1 + j) (by omega) q ?_ hs
      rw [NodupExt_add, mem_biUnion]
      exact ⟨_, hq₁, hq⟩
    · simp only [List.headD_cons, List.cons.injEq, true_and] at hp'
      subst hwy
      have e2 : t₂.headD v₀ = w := by
        rw [List.headD_eq_head?_getD, Option.mem_def.1 hw]
        rfl
      have e1 : t₁.headD v₀ = w := by rw [hp']; rfl
      exact hne' (headD_injOn h3 hq₀ v₀ h (fun j hj => hno j (by omega)) t₁ ht₁ t₂ ht₂
        (e1.trans e2.symm))

theorem dist_headD_le (hG : G.Connected) (v₀ : V) {l : List V} :
    ∀ {n : ℕ} {q : List V}, q ∈ NodupExt G l n → G.dist (l.headD v₀) (q.headD v₀) ≤ n
  | 0, q, h => by
    simp only [NodupExt_zero, mem_singleton] at h
    subst h
    simp
  | n + 1, q, h => by
    rw [NodupExt_succ, mem_biUnion] at h
    obtain ⟨t, ht, hq⟩ := h
    obtain ⟨b, rest, c, rfl, hadj, -, rfl⟩ := exists_of_mem_ext1 hq
    have hrec := dist_headD_le hG v₀ ht
    simp only [List.headD_cons] at hrec ⊢
    calc G.dist (l.headD v₀) c ≤ G.dist (l.headD v₀) b + G.dist b c := hG.dist_triangle
      _ ≤ n + 1 := by
          rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj]
          omega

/-- From every path some self-avoiding extension of at most `2h - 1` steps is stuck, once
`2^h` exceeds the size of a ball of radius `h`. -/
theorem exists_stuck_of_ball_bound (h3 : ∀ v : V, G.degree v ≤ 3) (hG : G.Connected) {C : ℝ}
    (hball : ∀ (x : V) (r : ℕ), ∃ s : Finset V,
      (∀ y, G.dist x y ≤ r → y ∈ s) ∧ (s.card : ℝ) ≤ C * (r + 1) ^ 2)
    {h : ℕ} (hh : C * (h + 1) ^ 2 < 2 ^ h) (q : List V) (hq : Adm G q) :
    ∃ j ≤ 2 * h - 1, ∃ q' ∈ NodupExt G q j, Stuck G q' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀⟩ := hG.nonempty
  have hinj := headD_injOn h3 hq v₀ h hcon
  have hcount := two_pow_le_card_NodupExt hq h (fun j hj => hcon j (by omega))
  obtain ⟨s, hs, hcard⟩ := hball (q.headD v₀) h
  have hle : (NodupExt G q h).card ≤ s.card := by
    refine card_le_card_of_injOn (fun q' => q'.headD v₀) ?_ ?_
    · intro q' hq'
      exact hs _ (dist_headD_le hG v₀ hq')
    · intro q₁ hq₁ q₂ hq₂ he
      exact hinj q₁ hq₁ q₂ hq₂ he
  have : (2 : ℝ) ^ h ≤ C * (h + 1) ^ 2 := by
    calc (2 : ℝ) ^ h = ((2 ^ h : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((NodupExt G q h).card : ℝ) := by exact_mod_cast hcount
      _ ≤ (s.card : ℝ) := by exact_mod_cast hle
      _ ≤ C * (h + 1) ^ 2 := hcard
  linarith

/-- `2^h` eventually exceeds `C (h+1)^2`. -/
theorem exists_two_pow_gt (C : ℝ) (hC : 0 < C) : ∃ h : ℕ, 1 ≤ h ∧ C * (h + 1) ^ 2 < 2 ^ h := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 (one_lt_two : (1 : ℝ) < 2)
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * C) by positivity))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  have h1 := hN (max N 1) (le_max_left _ _)
  set h := max N 1 with hhdef
  have hh : (1 : ℝ) ≤ h := by exact_mod_cast le_max_right N 1
  have h2pos : (0 : ℝ) < 2 ^ h := by positivity
  rw [div_lt_iff₀ h2pos] at h1
  have h4 : ((h : ℝ) + 1) ^ 2 ≤ 4 * (h : ℝ) ^ 2 := by nlinarith
  calc C * ((h : ℝ) + 1) ^ 2 ≤ C * (4 * (h : ℝ) ^ 2) := by gcongr
    _ = 4 * C * (h : ℝ) ^ 2 := by ring
    _ < 4 * C * (1 / (4 * C) * 2 ^ h) := by gcongr
    _ = 2 ^ h := by field_simp

end Rotor
