import Rotor.Support.Exploration4

/-!
The exploration in fresh time, `rotor.tex:1362-1376`: the `j`-th fresh step is the first
processing of an edge into the `j`-th reached vertex; `Y j` is the queue length at that
step.  Between fresh steps the queue does not grow (an entry into a reached vertex adds at
most one edge and removes one), and a fresh step into `v` from `u` adds at most
`r_v(u) - 1` edges.  On the atom of a history `h`, everything up to the `|h|`-th fresh step
is determined.
-/

open Finset MeasureTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (o x : V)

/-- The `j`-th reached vertex exists. -/
def Reach (j : ℕ) (ρ : Config G) : Prop := ∃ t, j ≤ (St π o x ρ t).hist.length

open Classical in
/-- The time of the `j`-th fresh step (`0` if it never occurs). -/
noncomputable def τf (j : ℕ) (ρ : Config G) : ℕ := if h : Reach π o x j ρ then Nat.find h else 0

open Classical in
/-- The queue length at the `j`-th fresh step (`0` if it never occurs). -/
noncomputable def Y (j : ℕ) (ρ : Config G) : ℕ :=
  if Reach π o x j ρ then (St π o x ρ (τf π o x j ρ)).queue.length else 0

variable {π o x}

theorem hist_length_mono (ρ : Config G) {t t' : ℕ} (h : t ≤ t') :
    (St π o x ρ t).hist.length ≤ (St π o x ρ t').hist.length :=
  ((qProc π o x).hist_run_prefix ρ h).length_le

theorem hist_length_succ_le (ρ : Config G) (t : ℕ) :
    (St π o x ρ (t + 1)).hist.length ≤ (St π o x ρ t).hist.length + 1 :=
  (qProc π o x).length_hist_run_succ_le ρ t

theorem le_hist_length_τf {j : ℕ} {ρ : Config G} (hj : Reach π o x j ρ) :
    j ≤ (St π o x ρ (τf π o x j ρ)).hist.length := by
  classical
  unfold τf
  rw [dif_pos hj]
  exact Nat.find_spec hj

theorem τf_le {j : ℕ} {ρ : Config G} (hj : Reach π o x j ρ) {t : ℕ}
    (ht : j ≤ (St π o x ρ t).hist.length) : τf π o x j ρ ≤ t := by
  classical
  unfold τf
  rw [dif_pos hj]
  exact Nat.find_min' hj ht

theorem hist_length_τf {j : ℕ} {ρ : Config G} (hj : Reach π o x j ρ) :
    (St π o x ρ (τf π o x j ρ)).hist.length = j := by
  classical
  have h1 := le_hist_length_τf hj
  refine le_antisymm ?_ h1
  rcases Nat.eq_zero_or_pos (τf π o x j ρ) with h0 | hpos
  · rw [h0]
    show (qInit o x).hist.length ≤ j
    simp [qInit]
  · obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hlt : (St π o x ρ s).hist.length < j := by
      by_contra hge
      push Not at hge
      have := τf_le hj hge
      omega
    have := hist_length_succ_le (π := π) (o := o) (x := x) ρ s
    rw [hs, Nat.succ_eq_add_one]
    omega

theorem Y_of_reach {j : ℕ} {ρ : Config G} (hj : Reach π o x j ρ) :
    Y π o x j ρ = (St π o x ρ (τf π o x j ρ)).queue.length := by
  unfold Y
  rw [if_pos hj]

theorem Y_of_not_reach {j : ℕ} {ρ : Config G} (hj : ¬ Reach π o x j ρ) : Y π o x j ρ = 0 := by
  unfold Y
  rw [if_neg hj]

theorem reach_zero (ρ : Config G) : Reach π o x 0 ρ := ⟨0, Nat.zero_le _⟩

theorem τf_zero (ρ : Config G) : τf π o x 0 ρ = 0 :=
  Nat.le_zero.1 (τf_le (reach_zero ρ) (Nat.zero_le _))

theorem Y_zero (ρ : Config G) : Y π o x 0 ρ = 1 := by
  rw [Y_of_reach (reach_zero ρ), τf_zero]
  rfl

theorem reach_mono {j j' : ℕ} (h : j' ≤ j) {ρ : Config G} (hj : Reach π o x j ρ) :
    Reach π o x j' ρ := by
  obtain ⟨t, ht⟩ := hj
  exact ⟨t, h.trans ht⟩

theorem τf_mono {j j' : ℕ} (h : j' ≤ j) {ρ : Config G} (hj : Reach π o x j ρ) :
    τf π o x j' ρ ≤ τf π o x j ρ :=
  τf_le (reach_mono h hj) (h.trans (le_hist_length_τf hj))

/-- Once the queue is empty nothing changes. -/
theorem St_of_queue_nil {ρ : Config G} {t : ℕ} (h : (St π o x ρ t).queue = []) :
    ∀ k, St π o x ρ (t + k) = St π o x ρ t
  | 0 => rfl
  | k + 1 => by
    rw [← add_assoc, St_succ, St_of_queue_nil h k]
    exact qStep_queue_nil π o ρ h

/-- The queue does not grow while no new vertex is reached. -/
theorem queue_length_le_of_hist_length_le (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3)
    (ρ : Config G) (t : ℕ) : ∀ k, (St π o x ρ (t + k)).hist.length ≤ (St π o x ρ t).hist.length →
    (St π o x ρ (t + k)).queue.length ≤ (St π o x ρ t).queue.length
  | 0, _ => le_rfl
  | k + 1, hk => by
    have hk' : (St π o x ρ (t + k)).hist.length ≤ (St π o x ρ t).hist.length :=
      (hist_length_mono ρ (by omega : t + k ≤ t + (k + 1))).trans hk
    refine le_trans ?_ (queue_length_le_of_hist_length_le hox h3 ρ t k hk')
    rw [← add_assoc]
    rcases hq : (St π o x ρ (t + k)).queue with _ | ⟨⟨u, v⟩, rest⟩
    · rw [St_succ, qStep_queue_nil π o ρ hq, hq]
    · refine (queue_length_succ_le_of_mem_hist π o x ρ hox h3 hq ?_).trans (by rw [hq])
      by_contra hv
      have hh : (St π o x ρ (t + k + 1)).hist = (St π o x ρ (t + k)).hist ++ [v] := by
        rw [St_succ, qStep_hist, hq]
        simp [hv]
      have h2 : (St π o x ρ (t + k + 1)).hist.length ≤ (St π o x ρ t).hist.length := hk
      rw [hh, List.length_append, List.length_singleton] at h2
      have h3' := hist_length_mono (π := π) (o := o) (x := x) ρ (by omega : t ≤ t + k)
      omega

section Atom

open QueryProcess

variable (π o x) in
/-- The exploration's atoms. -/
noncomputable abbrev atomE (h : History G) : Set (Config G) := (qProc π o x).atomF h

variable (π o x) in
/-- The exploration's next-read events. -/
noncomputable abbrev nxtE (h : History G) (v : V) : Set (Config G) := (qProc π o x).Nxt h v

/-- The history of the query process is the `hist` field. -/
theorem hist_run_eq (ρ : Config G) (t : ℕ) :
    (qProc π o x).hist ((qProc π o x).run ρ t) = (St π o x ρ t).hist := rfl

theorem reach_of_atomE {h : History G} {ρ : Config G} (hρ : ρ ∈ atomE π o x h) :
    Reach π o x h.length ρ := by
  obtain ⟨⟨t, ht⟩, -⟩ := hρ
  rw [hist_run_eq] at ht
  exact ⟨t, by rw [ht, verts, List.length_map]⟩

/-- Two configurations in the same atom agree on the rotors read. -/
theorem agree_of_atomE {h : History G} {ρ ρ' : Config G} (hρ : ρ ∈ atomE π o x h)
    (hρ' : ρ' ∈ atomE π o x h) : ∀ v ∈ verts h, ρ v = ρ' v := by
  intro v hv
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
  rw [hρ.2 y hy, hρ'.2 y hy]

/-- Up to the `|h|`-th fresh step the run is determined by the atom. -/
theorem St_eq_of_atomE {h : History G} {ρ ρ' : Config G} (hρ : ρ ∈ atomE π o x h)
    (hρ' : ρ' ∈ atomE π o x h) {t : ℕ} (ht : (St π o x ρ t).hist.length ≤ h.length) :
    St π o x ρ' t = St π o x ρ t := by
  obtain ⟨⟨t₀, ht₀⟩, -⟩ := id hρ
  rw [hist_run_eq] at ht₀
  have hpre : (St π o x ρ t).hist <+: verts h := by
    rcases le_total t t₀ with htt | htt
    · rw [← ht₀]; exact (qProc π o x).hist_run_prefix ρ htt
    · have this : verts h <+: (St π o x ρ t).hist := by
        rw [← ht₀]; exact (qProc π o x).hist_run_prefix ρ htt
      rw [show (St π o x ρ t).hist = verts h from
        (this.eq_of_length_le (by rw [verts, List.length_map]; exact ht)).symm]
  exact (qProc π o x).run_local ρ ρ' t (fun v hv => agree_of_atomE hρ hρ' v (hpre.subset hv))

theorem τf_eq_of_atomE {h : History G} {ρ ρ' : Config G} (hρ : ρ ∈ atomE π o x h)
    (hρ' : ρ' ∈ atomE π o x h) : τf π o x h.length ρ = τf π o x h.length ρ' := by
  have key : ∀ ρ ρ' : Config G, ρ ∈ atomE π o x h → ρ' ∈ atomE π o x h →
      τf π o x h.length ρ' ≤ τf π o x h.length ρ := by
    intro ρ ρ' hρ hρ'
    have hr := reach_of_atomE hρ
    have hlen := hist_length_τf hr
    have hst := St_eq_of_atomE hρ hρ' hlen.le
    exact τf_le (reach_of_atomE hρ') (by rw [hst, hlen])
  exact le_antisymm (key ρ' ρ hρ' hρ) (key ρ ρ' hρ hρ')

theorem Y_eq_of_atomE {h : History G} {ρ ρ' : Config G} (hρ : ρ ∈ atomE π o x h)
    (hρ' : ρ' ∈ atomE π o x h) : Y π o x h.length ρ = Y π o x h.length ρ' := by
  rw [Y_of_reach (reach_of_atomE hρ), Y_of_reach (reach_of_atomE hρ'), ← τf_eq_of_atomE hρ hρ',
    St_eq_of_atomE hρ hρ' (hist_length_τf (reach_of_atomE hρ)).le]

theorem Y_eq_of_atomE_le {h : History G} {ρ ρ' : Config G} (hρ : ρ ∈ atomE π o x h)
    (hρ' : ρ' ∈ atomE π o x h) {i : ℕ} (hi : i ≤ h.length) : Y π o x i ρ = Y π o x i ρ' := by
  have hpre : h.take i <+: h := List.take_prefix i h
  have := Y_eq_of_atomE ((qProc π o x).atomF_prefix hpre hρ) ((qProc π o x).atomF_prefix hpre hρ')
  rwa [List.length_take, min_eq_left hi] at this

theorem nxt_unique {h : History G} {v v' : V} {ρ : Config G} (hv : ρ ∈ nxtE π o x h v)
    (hv' : ρ ∈ nxtE π o x h v') : v = v' := by
  obtain ⟨t, ht⟩ := hv
  obtain ⟨t', ht'⟩ := hv'
  rw [hist_run_eq] at ht ht'
  have hcmp : (St π o x ρ t).hist <+: (St π o x ρ t').hist ∨
      (St π o x ρ t').hist <+: (St π o x ρ t).hist := by
    rcases le_total t t' with htt | htt
    · exact Or.inl ((qProc π o x).hist_run_prefix ρ htt)
    · exact Or.inr ((qProc π o x).hist_run_prefix ρ htt)
  rw [ht, ht'] at hcmp
  rcases hcmp with hc | hc
  · have := hc.eq_of_length (by simp)
    simpa using this
  · have := hc.eq_of_length (by simp)
    simpa using this.symm

/-- Reaching one more vertex from an atom means some next read. -/
theorem reach_succ_iff {h : History G} {ρ : Config G} (hρ : ρ ∈ atomE π o x h) :
    Reach π o x (h.length + 1) ρ ↔ ∃ v, ρ ∈ nxtE π o x h v := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨⟨t₀, ht₀⟩, -⟩ := hρ
    rw [hist_run_eq] at ht₀
    have hpre : (St π o x ρ t₀).hist <+: (St π o x ρ t).hist := by
      rcases le_total t₀ t with htt | htt
      · exact (qProc π o x).hist_run_prefix ρ htt
      · have this : (St π o x ρ t).hist <+: (St π o x ρ t₀).hist :=
          (qProc π o x).hist_run_prefix ρ htt
        rw [this.eq_of_length_le (by rw [ht₀, verts, List.length_map]; omega)]
    obtain ⟨l₂, hl₂⟩ := hpre
    have hl₂ne : l₂ ≠ [] := by
      intro h0
      rw [h0, List.append_nil, ht₀] at hl₂
      have := congrArg List.length hl₂
      rw [verts, List.length_map] at this
      omega
    obtain ⟨v, l₃, rfl⟩ := List.exists_cons_of_ne_nil hl₂ne
    obtain ⟨t', -, ht'⟩ := (qProc π o x).exists_run_hist_eq_prefix ρ t (verts h ++ [v]) (by
      show verts h ++ [v] <+: (St π o x ρ t).hist
      rw [← hl₂, ht₀]
      exact ⟨l₃, by simp⟩)
    exact ⟨v, t', ht'⟩
  · rintro ⟨v, t, ht⟩
    rw [hist_run_eq] at ht
    exact ⟨t, by rw [ht, List.length_append, verts, List.length_map, List.length_singleton]⟩

theorem nxt_eq_of_atomE {h : History G} {v v' : V} {ρ ρ' : Config G}
    (hρ : ρ ∈ atomE π o x h ∩ nxtE π o x h v) (hρ' : ρ' ∈ atomE π o x h)
    (hv' : ρ' ∈ nxtE π o x h v') : v = v' := by
  have : ρ' ∈ atomE π o x h ∩ nxtE π o x h v :=
    (qProc π o x).atomF_inter_Nxt_determined h v ρ ρ' (fun w hw =>
      agree_of_atomE hρ.1 hρ' w (by simpa using hw)) hρ
  exact nxt_unique this.2 hv'

/-- The time of the read after `h`, given the two histories around it. -/
theorem τf_succ_eq_of {h : History G} {v : V} {ρ : Config G} {t₁ : ℕ}
    (ht₁ : (St π o x ρ t₁).hist = verts h) (ht₁' : (St π o x ρ (t₁ + 1)).hist = verts h ++ [v]) :
    τf π o x (h.length + 1) ρ = t₁ + 1 := by
  have hlen' : (St π o x ρ (t₁ + 1)).hist.length = h.length + 1 := by
    rw [ht₁', List.length_append, verts, List.length_map, List.length_singleton]
  have hr : Reach π o x (h.length + 1) ρ := ⟨t₁ + 1, hlen'.ge⟩
  apply le_antisymm (τf_le hr hlen'.ge)
  by_contra hlt
  push Not at hlt
  have h1 := le_hist_length_τf hr
  have h2 := hist_length_mono (π := π) (o := o) (x := x) ρ
    (show τf π o x (h.length + 1) ρ ≤ t₁ by omega)
  rw [ht₁, verts, List.length_map] at h2
  omega

theorem exists_τf_succ_of_nxt {h : History G} {v : V} {ρ : Config G}
    (hρ : ρ ∈ atomE π o x h ∩ nxtE π o x h v) :
    ∃ t₁, τf π o x (h.length + 1) ρ = t₁ + 1 ∧ (St π o x ρ t₁).hist = verts h ∧
      (St π o x ρ (t₁ + 1)).hist = verts h ++ [v] := by
  obtain ⟨t, ht⟩ := hρ.2
  obtain ⟨t₁, ht₁, ht₁'⟩ := (qProc π o x).exists_hist_eq_and_succ ρ ht
  rw [hist_run_eq] at ht₁ ht₁'
  exact ⟨t₁, τf_succ_eq_of ht₁ ht₁', ht₁, ht₁'⟩

theorem not_mem_verts_of_nxt {h : History G} {v : V} {ρ : Config G}
    (hρ : ρ ∈ atomE π o x h ∩ nxtE π o x h v) : v ∉ verts h := by
  obtain ⟨t₁, -, -, ht₁'⟩ := exists_τf_succ_of_nxt hρ
  have hnd := (qProc π o x).hist_run_nodup ρ (t₁ + 1)
  rw [hist_run_eq, ht₁', List.nodup_append] at hnd
  intro hv
  exact hnd.2.2 v hv v (List.mem_singleton_self v) rfl

/-- Just before the read of `v`, the head of the queue is an edge `u → v` into the fresh
vertex `v`. -/
theorem head_of_nxt (hox : G.Adj o x) {h : History G} {v : V} {ρ : Config G} {t₁ : ℕ}
    (ht₁ : (St π o x ρ t₁).hist = verts h) (ht₁' : (St π o x ρ (t₁ + 1)).hist = verts h ++ [v]) :
    ∃ u rest, (St π o x ρ t₁).queue = (u, v) :: rest ∧ G.Adj v u ∧ (St π o x ρ t₁).M v = 0 := by
  rcases hq : (St π o x ρ t₁).queue with _ | ⟨⟨u, v'⟩, rest⟩
  · exfalso
    rw [St_succ, qStep_queue_nil π o ρ hq, ht₁] at ht₁'
    simpa using congrArg List.length ht₁'
  · have hh : (St π o x ρ (t₁ + 1)).hist = if v' ∈ (St π o x ρ t₁).hist then (St π o x ρ t₁).hist
        else (St π o x ρ t₁).hist ++ [v'] := by
      rw [St_succ, qStep_hist, hq]
    rw [ht₁', ht₁] at hh
    split_ifs at hh with hmem
    · exfalso
      simpa using congrArg List.length hh
    · have hv : v = v' := by simpa using List.append_cancel_left hh
      subst hv
      refine ⟨u, rest, rfl, (queue_adj π o x ρ hox t₁ (u, v) (by rw [hq]; simp)).symm, ?_⟩
      by_contra hM
      have := (mem_hist_iff_M_pos π o x ρ hox t₁ v).2 (Nat.pos_of_ne_zero hM)
      rw [ht₁] at this
      exact hmem this

/-- The fresh step into `v` from `u`: the queue length at the next fresh step is at most
the previous one plus `r_v(u) - 2`, uniformly on the atom. -/
theorem Y_succ_bound (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) {h : History G} {v : V}
    {ρ : Config G} (hρ : ρ ∈ atomE π o x h ∩ nxtE π o x h v) :
    ∃ u, G.Adj v u ∧ ∀ ρ' ∈ atomE π o x h ∩ nxtE π o x h v,
      Y π o x (h.length + 1) ρ' + 2 ≤ Y π o x h.length ρ' + rankOf π ρ' v u := by
  obtain ⟨t₁, -, ht₁, ht₁'⟩ := exists_τf_succ_of_nxt hρ
  obtain ⟨u, rest, hq, hadj, hM⟩ := head_of_nxt hox ht₁ ht₁'
  refine ⟨u, hadj, fun ρ' hρ' => ?_⟩
  have hst : St π o x ρ' t₁ = St π o x ρ t₁ :=
    St_eq_of_atomE hρ.1 hρ'.1 (by rw [ht₁, verts, List.length_map])
  have ht₁ρ' : (St π o x ρ' t₁).hist = verts h := by rw [hst, ht₁]
  have ht₁ρ'' : (St π o x ρ' (t₁ + 1)).hist = verts h ++ [v] := by
    rw [St_succ, qStep_hist, hst, hq, ht₁]
    have : v ∉ verts h := not_mem_verts_of_nxt hρ
    simp [this]
  have hτ' := τf_succ_eq_of ht₁ρ' ht₁ρ''
  have hq' : (St π o x ρ' t₁).queue = (u, v) :: rest := by rw [hst, hq]
  have hM' : (St π o x ρ' t₁).M v = 0 := by rw [hst, hM]
  have hr1 : Reach π o x (h.length + 1) ρ' := (reach_succ_iff hρ'.1).2 ⟨v, hρ'.2⟩
  have hr0 : Reach π o x h.length ρ' := reach_of_atomE hρ'.1
  rw [Y_of_reach hr1, Y_of_reach hr0, hτ']
  have hfresh := queue_length_succ_le_fresh π o x ρ' hq' hM'
  have hτ0 : τf π o x h.length ρ' ≤ t₁ :=
    τf_le hr0 (by rw [ht₁ρ', verts, List.length_map])
  have hbetween : (St π o x ρ' t₁).queue.length ≤ (St π o x ρ' (τf π o x h.length ρ')).queue.length := by
    have := queue_length_le_of_hist_length_le hox h3 ρ' (τf π o x h.length ρ') (t₁ - τf π o x h.length ρ')
      (by rw [Nat.add_sub_cancel' hτ0, ht₁ρ', verts, List.length_map, hist_length_τf hr0])
    rwa [Nat.add_sub_cancel' hτ0] at this
  have hrpos := rankOf_pos π ρ' hadj
  omega

theorem Y_pos_of_nxt {h : History G} {v : V} {ρ : Config G}
    (hρ : ρ ∈ atomE π o x h ∩ nxtE π o x h v) : 1 ≤ Y π o x h.length ρ := by
  have hr0 := reach_of_atomE hρ.1
  rw [Y_of_reach hr0]
  by_contra h0
  push Not at h0
  have hnil : (St π o x ρ (τf π o x h.length ρ)).queue = [] :=
    List.length_eq_zero_iff.1 (by omega)
  obtain ⟨t₁, -, ht₁, ht₁'⟩ := exists_τf_succ_of_nxt hρ
  have hle : τf π o x h.length ρ ≤ t₁ + 1 :=
    (τf_le hr0 (by rw [ht₁, verts, List.length_map])).trans (Nat.le_succ t₁)
  have := St_of_queue_nil hnil (t₁ + 1 - τf π o x h.length ρ)
  rw [Nat.add_sub_cancel' hle] at this
  have hlen := congrArg (fun s : QueueState V => s.hist.length) this
  rw [ht₁', hist_length_τf hr0, List.length_append, verts, List.length_map,
    List.length_singleton] at hlen
  omega

end Atom

section Measure

open QueryProcess

omit [DecidableEq V] in
theorem uniformAt_singleton (v : V) (a : G.neighborSet v) :
    uniformAt π v {a} = (G.degree v : ENNReal)⁻¹ := by
  haveI := π.nonempty v
  unfold uniformAt
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a), PMF.uniformOfFintype_apply,
    G.card_neighborSet_eq_degree]

theorem measurableSet_atomE (h : History G) : MeasurableSet (atomE π o x h) :=
  (qProc π o x).measurableSet_atomF h

theorem measurableSet_atomE_nxt (h : History G) (v : V) :
    MeasurableSet (atomE π o x h ∩ nxtE π o x h v) :=
  (qProc π o x).measurableSet_atomF_inter_Nxt h v

/-- `Σ_a (r_a(u) - 1) ≤ deg v` when `deg v ≤ 3`. -/
theorem sum_cycRank_sub_one_le (h3 : ∀ v : V, G.degree v ≤ 3) {v u : V} (hadj : G.Adj v u) :
    ∑ a : G.neighborSet v, (cycRank (π.next v) (π.cyclic v) a ⟨u, hadj⟩ - 1) ≤ G.degree v := by
  have himg := image_cycRank_left (π.next v) (π.cyclic v) (⟨u, hadj⟩ : G.neighborSet v)
  rw [G.card_neighborSet_eq_degree] at himg
  have hsum : ∑ a : G.neighborSet v, (cycRank (π.next v) (π.cyclic v) a ⟨u, hadj⟩ - 1)
      = ∑ k ∈ Finset.Icc 1 (G.degree v), (k - 1) := by
    rw [← himg, Finset.sum_image]
    intro a _ b _ hab
    exact cycRank_left_injective (π.next v) (π.cyclic v) _ hab
  rw [hsum]
  have hd1 : 1 ≤ G.degree v := (G.degree_pos_iff_exists_adj v).2 ⟨u, hadj⟩
  have hd3 := h3 v
  generalize G.degree v = d at hd1 hd3 ⊢
  interval_cases d <;> decide

/-- The supermartingale step on an atom: the expected queue length does not increase at a
fresh step. -/
theorem lintegral_Y_succ_le (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) (h : History G)
    (v : V) :
    ∫⁻ ρ in atomE π o x h ∩ nxtE π o x h v, (Y π o x (h.length + 1) ρ : ENNReal) ∂(uniformLaw π)
      ≤ ∫⁻ ρ in atomE π o x h ∩ nxtE π o x h v, (Y π o x h.length ρ : ENNReal) ∂(uniformLaw π) := by
  set A := atomE π o x h ∩ nxtE π o x h v with hA
  rcases Set.eq_empty_or_nonempty A with hAe | ⟨ρ₀, hρ₀⟩
  · rw [hAe]; simp
  obtain ⟨u, hadj, hbound⟩ := Y_succ_bound hox h3 hρ₀
  have hv : v ∉ verts h := not_mem_verts_of_nxt hρ₀
  set Y₀ := Y π o x h.length ρ₀ with hY₀def
  have hY₀ : ∀ ρ ∈ A, Y π o x h.length ρ = Y₀ := fun ρ hρ => Y_eq_of_atomE hρ.1 hρ₀.1
  have hY₀pos : 1 ≤ Y₀ := Y_pos_of_nxt hρ₀
  let f : G.neighborSet v → ENNReal :=
    fun a => ((Y₀ + cycRank (π.next v) (π.cyclic v) a ⟨u, hadj⟩ - 2 : ℕ) : ENNReal)
  have hpt : ∀ ρ ∈ A, (Y π o x (h.length + 1) ρ : ENNReal) ≤ f (ρ v) := by
    intro ρ hρ
    have := hbound ρ hρ
    rw [hY₀ ρ hρ, rankOf_eq π ρ hadj, rank_eq_cycRank] at this
    simp only [f]
    exact_mod_cast (by omega :
      Y π o x (h.length + 1) ρ ≤ Y₀ + cycRank (π.next v) (π.cyclic v) (ρ v) ⟨u, hadj⟩ - 2)
  have hd1 : 1 ≤ G.degree v := (G.degree_pos_iff_exists_adj v).2 ⟨u, hadj⟩
  have hsumN : ∑ a : G.neighborSet v, (Y₀ + cycRank (π.next v) (π.cyclic v) a ⟨u, hadj⟩ - 2)
      ≤ G.degree v * Y₀ := by
    have h1 : ∀ a : G.neighborSet v, Y₀ + cycRank (π.next v) (π.cyclic v) a ⟨u, hadj⟩ - 2
        = (Y₀ - 1) + (cycRank (π.next v) (π.cyclic v) a ⟨u, hadj⟩ - 1) := by
      intro a
      have := cycRank_pos (π.next v) (π.cyclic v) a ⟨u, hadj⟩
      omega
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, G.card_neighborSet_eq_degree,
      smul_eq_mul]
    have := sum_cycRank_sub_one_le (π := π) h3 hadj
    calc G.degree v * (Y₀ - 1) + ∑ a : G.neighborSet v,
          (cycRank (π.next v) (π.cyclic v) a ⟨u, hadj⟩ - 1)
        ≤ G.degree v * (Y₀ - 1) + G.degree v := by omega
      _ = G.degree v * Y₀ := by rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hY₀pos]
  calc ∫⁻ ρ in A, (Y π o x (h.length + 1) ρ : ENNReal) ∂(uniformLaw π)
      ≤ ∫⁻ ρ in A, f (ρ v) ∂(uniformLaw π) :=
        setLIntegral_mono' (measurableSet_atomE_nxt h v) hpt
    _ = uniformLaw π A * ∑ a, f a * uniformAt π v {a} :=
        (qProc π o x).setLIntegral_atomF_Nxt (uniformAt π) hv f
    _ ≤ uniformLaw π A * Y₀ := by
        gcongr
        simp_rw [uniformAt_singleton, ← Finset.sum_mul]
        have hcast : ∑ a, f a = ((∑ a : G.neighborSet v,
            (Y₀ + cycRank (π.next v) (π.cyclic v) a ⟨u, hadj⟩ - 2) : ℕ) : ENNReal) := by
          simp [f]
        rw [hcast]
        have hd0 : (G.degree v : ENNReal) ≠ 0 := by exact_mod_cast (by omega : G.degree v ≠ 0)
        calc ((∑ a : G.neighborSet v, (Y₀ + cycRank (π.next v) (π.cyclic v) a ⟨u, hadj⟩ - 2) : ℕ)
              : ENNReal) * (G.degree v : ENNReal)⁻¹
            ≤ ((G.degree v * Y₀ : ℕ) : ENNReal) * (G.degree v : ENNReal)⁻¹ := by
              gcongr
          _ = Y₀ := by
              rw [Nat.cast_mul, mul_comm (G.degree v : ENNReal), mul_assoc,
                ENNReal.mul_inv_cancel hd0 (ENNReal.natCast_ne_top _), mul_one]
    _ = ∫⁻ ρ in A, (Y π o x h.length ρ : ENNReal) ∂(uniformLaw π) := by
        rw [setLIntegral_congr_fun (measurableSet_atomE_nxt h v)
          (fun ρ hρ => by rw [hY₀ ρ hρ]), setLIntegral_const, mul_comm]

/-- A fresh step adds nothing with conditional probability at least `1/3`. -/
theorem measure_drop_ge (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3) (h : History G)
    (v : V) :
    uniformLaw π (atomE π o x h ∩ nxtE π o x h v)
      ≤ 3 * uniformLaw π (atomE π o x h ∩ nxtE π o x h v ∩
        {ρ | Y π o x (h.length + 1) ρ + 1 ≤ Y π o x h.length ρ}) := by
  set A := atomE π o x h ∩ nxtE π o x h v with hA
  rcases Set.eq_empty_or_nonempty A with hAe | ⟨ρ₀, hρ₀⟩
  · rw [hAe]; simp
  obtain ⟨u, hadj, hbound⟩ := Y_succ_bound hox h3 hρ₀
  have hv : v ∉ verts h := not_mem_verts_of_nxt hρ₀
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : G.neighborSet v, cycRank (π.next v) (π.cyclic v) a₀ ⟨u, hadj⟩ = 1 := by
    have himg := image_cycRank_left (π.next v) (π.cyclic v) (⟨u, hadj⟩ : G.neighborSet v)
    have h1 : 1 ∈ Finset.Icc 1 (Fintype.card (G.neighborSet v)) :=
      Finset.mem_Icc.2 ⟨le_rfl, Fintype.card_pos_iff.2 ⟨⟨u, hadj⟩⟩⟩
    rw [← himg] at h1
    obtain ⟨a₀, -, ha₀⟩ := Finset.mem_image.1 h1
    exact ⟨a₀, ha₀⟩
  have hsub : atomE π o x (h ++ [⟨v, a₀⟩]) ⊆
      A ∩ {ρ | Y π o x (h.length + 1) ρ + 1 ≤ Y π o x h.length ρ} := by
    intro ρ hρ
    have hρ' : ρ ∈ (qProc π o x).atomF (h ++ [⟨v, a₀⟩]) := hρ
    rw [(qProc π o x).atomF_append] at hρ'
    replace hρ := hρ'
    refine ⟨hρ.1, ?_⟩
    have := hbound ρ hρ.1
    rw [rankOf_eq π ρ hadj, rank_eq_cycRank, show ρ v = a₀ from hρ.2, ha₀] at this
    show Y π o x (h.length + 1) ρ + 1 ≤ Y π o x h.length ρ
    omega
  have hmeas : uniformLaw π (atomE π o x (h ++ [⟨v, a₀⟩])) =
      uniformAt π v {a₀} * uniformLaw π A :=
    (qProc π o x).productLaw_atomF_append (uniformAt π) hv a₀
  rw [uniformAt_singleton] at hmeas
  have hd3 : (G.degree v : ENNReal) ≤ 3 := by exact_mod_cast h3 v
  have hd0 : (G.degree v : ENNReal) ≠ 0 := by
    exact_mod_cast ((G.degree_pos_iff_exists_adj v).2 ⟨u, hadj⟩).ne'
  calc uniformLaw π A = G.degree v * ((G.degree v : ENNReal)⁻¹ * uniformLaw π A) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hd0 (ENNReal.natCast_ne_top _), one_mul]
    _ = G.degree v * uniformLaw π (atomE π o x (h ++ [⟨v, a₀⟩])) := by
        rw [← hmeas]
    _ ≤ 3 * uniformLaw π (A ∩ {ρ | Y π o x (h.length + 1) ρ + 1 ≤ Y π o x h.length ρ}) := by
        gcongr

end Measure


end Rotor
