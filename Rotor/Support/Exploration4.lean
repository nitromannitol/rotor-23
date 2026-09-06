import Rotor.Support.QueryAtoms
import Rotor.Support.StepProb

/-!
The exploration of `rotor.tex:1320-1340` (Section 4):

  "Fix a directed edge `e = o → x` and add it to a first-in, first-out queue.  For every
   `v ∈ V ∖ {o}`, set `M_v = 0`.  While the queue is nonempty, remove and process its first
   edge `u → v`: if `r_v(u) ≤ M_v`, do nothing; otherwise add to the queue, in increasing
   order of `r_v(w)`, every edge `v → w` not already added that satisfies `w ∼ v`, `w ≠ o`,
   `M_v < r_v(w) < r_v(u)`, and then set `M_v = r_v(u)`."

The state records the queue, `M`, and the list of vertices whose rotors have been read
(the reached vertices, in order of first processing).  Reading `ρ` only at the head of the
processed edge makes the exploration a `QueryProcess`.
-/

open Finset

namespace Rotor

/-- The state of the exploration. -/
structure QueueState (V : Type*) where
  /-- the queue of directed edges, head first -/
  queue : List (V × V)
  /-- `M_v` -/
  M : V → ℕ
  /-- the vertices whose rotor has been read, in order -/
  hist : List V

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

open Classical in
/-- `r_v(u)`, and `0` unless `u ∼ v`. -/
noncomputable def rankOf (ρ : Config G) (v u : V) : ℕ :=
  if h : G.Adj v u then rank π ρ v ⟨u, h⟩ else 0

/-- The edges `v → w` added while processing an entry of rank `r` into `v` when `M_v = m`. -/
noncomputable def newEdges (ρ : Config G) (o v : V) (m r : ℕ) : List (V × V) :=
  ((Finset.univ : Finset (G.neighborSet v)).filter
    (fun w => w.1 ≠ o ∧ m < rank π ρ v w ∧ rank π ρ v w < r)).toList.map (fun w => (v, w.1))

/-- One processing step. -/
noncomputable def qStep (o : V) (ρ : Config G) (s : QueueState V) : QueueState V :=
  match s.queue with
  | [] => s
  | (u, v) :: rest =>
    if rankOf π ρ v u ≤ s.M v then
      { queue := rest, M := s.M, hist := if v ∈ s.hist then s.hist else s.hist ++ [v] }
    else
      { queue := rest ++ newEdges π ρ o v (s.M v) (rankOf π ρ v u),
        M := Function.update s.M v (rankOf π ρ v u),
        hist := if v ∈ s.hist then s.hist else s.hist ++ [v] }

/-- The initial state for the edge `o → x`. -/
def qInit (o x : V) : QueueState V := { queue := [(o, x)], M := fun _ => 0, hist := [] }

omit [G.LocallyFinite] in
theorem rankOf_congr {ρ ρ' : Config G} {v : V} (h : ρ v = ρ' v) (u : V) :
    rankOf π ρ v u = rankOf π ρ' v u := by
  unfold rankOf
  split_ifs
  · exact rank_congr π v h _
  · rfl

theorem newEdges_congr {ρ ρ' : Config G} {v : V} (h : ρ v = ρ' v) (o : V) (m r : ℕ) :
    newEdges π ρ o v m r = newEdges π ρ' o v m r := by
  unfold newEdges
  congr 2
  ext w
  simp only [mem_filter, mem_univ, true_and, rank_congr π v h w]

theorem qStep_hist (o : V) (ρ : Config G) (s : QueueState V) :
    (qStep π o ρ s).hist = match s.queue with
      | [] => s.hist
      | (_, v) :: _ => if v ∈ s.hist then s.hist else s.hist ++ [v] := by
  rcases hq : s.queue with _ | ⟨⟨u, v⟩, rest⟩
  · simp only [qStep, hq]
  · simp only [qStep, hq]
    split_ifs <;> rfl

/-- The exploration as a query process. -/
noncomputable def qProc (o x : V) : QueryProcess G (QueueState V) where
  init := qInit o x
  step := qStep π o
  hist := QueueState.hist
  hist_init := rfl
  hist_step := by
    intro ρ s
    rw [qStep_hist]
    rcases hq : s.queue with _ | ⟨⟨u, v⟩, rest⟩
    · exact Or.inl rfl
    · by_cases hv : v ∈ s.hist
      · exact Or.inl (by simp [hv])
      · exact Or.inr ⟨v, hv, by simp [hv]⟩
  local_step := by
    intro ρ ρ' s h
    rw [qStep_hist] at h
    rcases hq : s.queue with _ | ⟨⟨u, v⟩, rest⟩
    · simp only [qStep, hq]
    · simp only [hq] at h
      have hv : ρ v = ρ' v := h v (by split_ifs with hmem <;> simp [hmem])
      simp only [qStep, hq, rankOf_congr π hv u, newEdges_congr π hv o]
  read_step := by
    intro ρ ρ' s _
    rw [qStep_hist, qStep_hist]


section Run

variable (o x : V) (ρ : Config G)

/-- The state after `t` processing steps. -/
noncomputable abbrev St (t : ℕ) : QueueState V := (qProc π o x).run ρ t

theorem St_zero : St π o x ρ 0 = qInit o x := rfl

theorem St_succ (t : ℕ) : St π o x ρ (t + 1) = qStep π o ρ (St π o x ρ t) :=
  QueryProcess.run_succ _ _ _

theorem mem_newEdges {v : V} {m r : ℕ} {e : V × V} :
    e ∈ newEdges π ρ o v m r ↔ e.1 = v ∧ ∃ h : G.Adj v e.2, e.2 ≠ o ∧
      m < rank π ρ v ⟨e.2, h⟩ ∧ rank π ρ v ⟨e.2, h⟩ < r := by
  unfold newEdges
  simp only [List.mem_map, Finset.mem_toList, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    exact ⟨rfl, w.2, hw1, hw2, hw3⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨e.2, h2⟩, ⟨h3, h4, h5⟩, Prod.ext h1.symm rfl⟩

theorem qStep_queue_nil {s : QueueState V} (hq : s.queue = []) : qStep π o ρ s = s := by
  simp only [qStep, hq]

theorem qStep_queue_cons {s : QueueState V} {u v : V} {rest : List (V × V)}
    (hq : s.queue = (u, v) :: rest) :
    (qStep π o ρ s).queue = rest ++
      (if rankOf π ρ v u ≤ s.M v then [] else newEdges π ρ o v (s.M v) (rankOf π ρ v u)) := by
  simp only [qStep, hq]
  split_ifs <;> simp

theorem qStep_M_cons {s : QueueState V} {u v : V} {rest : List (V × V)}
    (hq : s.queue = (u, v) :: rest) :
    (qStep π o ρ s).M = if rankOf π ρ v u ≤ s.M v then s.M
      else Function.update s.M v (rankOf π ρ v u) := by
  simp only [qStep, hq]
  split_ifs <;> rfl

theorem M_le_qStep (s : QueueState V) (v : V) : s.M v ≤ (qStep π o ρ s).M v := by
  rcases hq : s.queue with _ | ⟨⟨u, v'⟩, rest⟩
  · rw [qStep_queue_nil π o ρ hq]
  · rw [qStep_M_cons π o ρ hq]
    split_ifs with h
    · exact le_rfl
    · by_cases hv : v = v'
      · subst hv
        rw [Function.update_self]
        exact (not_le.1 h).le
      · rw [Function.update_of_ne hv]

theorem M_mono {t t' : ℕ} (h : t ≤ t') (v : V) : (St π o x ρ t).M v ≤ (St π o x ρ t').M v := by
  induction t' with
  | zero => rw [Nat.le_zero.1 h]
  | succ t' ih =>
    rcases Nat.lt_or_ge t (t' + 1) with h' | h'
    · exact (ih (by omega)).trans (by rw [St_succ]; exact M_le_qStep π o ρ _ v)
    · rw [Nat.le_antisymm h h']

omit [G.LocallyFinite] in
theorem rankOf_pos {v u : V} (h : G.Adj v u) : 1 ≤ rankOf π ρ v u := by
  unfold rankOf
  rw [dif_pos h, rank_eq_cycRank]
  exact cycRank_pos _ (π.cyclic v) _ _

theorem rankOf_le_degree (v u : V) : rankOf π ρ v u ≤ G.degree v := by
  unfold rankOf
  split_ifs
  · rw [← G.card_neighborSet_eq_degree, rank_eq_cycRank]
    exact cycRank_le _ (π.cyclic v) _ _
  · exact Nat.zero_le _

omit [G.LocallyFinite] in
theorem rankOf_eq {v u : V} (h : G.Adj v u) : rankOf π ρ v u = rank π ρ v ⟨u, h⟩ := by
  unfold rankOf
  rw [dif_pos h]

theorem queue_adj (hox : G.Adj o x) : ∀ t : ℕ, ∀ e ∈ (St π o x ρ t).queue, G.Adj e.1 e.2
  | 0, e, he => by
    simp only [St_zero, qInit, List.mem_singleton] at he
    subst he
    exact hox
  | t + 1, e, he => by
    rw [St_succ] at he
    rcases hq : (St π o x ρ t).queue with _ | ⟨⟨u, v⟩, rest⟩
    · rw [qStep_queue_nil π o ρ hq, hq] at he
      simp at he
    · rw [qStep_queue_cons π o ρ hq, List.mem_append] at he
      rcases he with he | he
      · exact queue_adj hox t e (by rw [hq]; exact List.mem_cons_of_mem _ he)
      · split_ifs at he
        · simp at he
        · obtain ⟨h1, h2, -⟩ := (mem_newEdges π o ρ).1 he
          rw [h1]; exact h2

theorem mem_hist_iff_M_pos (hox : G.Adj o x) : ∀ (t : ℕ) (v : V),
    v ∈ (St π o x ρ t).hist ↔ 0 < (St π o x ρ t).M v
  | 0, v => by
    show v ∈ (qInit o x).hist ↔ 0 < (qInit o x).M v
    simp [qInit]
  | t + 1, v => by
    have ih := mem_hist_iff_M_pos hox t
    rw [St_succ]
    rcases hq : (St π o x ρ t).queue with _ | ⟨⟨u, v'⟩, rest⟩
    · rw [qStep_queue_nil π o ρ hq]; exact ih v
    · have hadj : G.Adj v' u := (queue_adj π o x ρ hox t (u, v') (by rw [hq]; simp)).symm
      have hr := rankOf_pos π ρ hadj
      rw [qStep_M_cons π o ρ hq]
      have hhist : (qStep π o ρ (St π o x ρ t)).hist =
          if v' ∈ (St π o x ρ t).hist then (St π o x ρ t).hist else (St π o x ρ t).hist ++ [v'] := by
        rw [qStep_hist, hq]
      rw [hhist]
      by_cases hv : v = v'
      · subst hv
        by_cases hmem : v ∈ (St π o x ρ t).hist
        · rw [if_pos hmem]
          by_cases hle : rankOf π ρ v u ≤ (St π o x ρ t).M v
          · rw [if_pos hle]; exact ih v
          · rw [if_neg hle, Function.update_self]; exact ⟨fun _ => hr, fun _ => hmem⟩
        · rw [if_neg hmem, List.mem_append, List.mem_singleton]
          by_cases hle : rankOf π ρ v u ≤ (St π o x ρ t).M v
          · rw [if_pos hle]; exact ⟨fun _ => lt_of_lt_of_le hr hle, fun _ => Or.inr rfl⟩
          · rw [if_neg hle, Function.update_self]; exact ⟨fun _ => hr, fun _ => Or.inr rfl⟩
      · by_cases hmem : v' ∈ (St π o x ρ t).hist
        · rw [if_pos hmem]
          by_cases hle : rankOf π ρ v' u ≤ (St π o x ρ t).M v'
          · rw [if_pos hle]; exact ih v
          · rw [if_neg hle, Function.update_of_ne hv]; exact ih v
        · rw [if_neg hmem, List.mem_append, List.mem_singleton, or_iff_left hv]
          by_cases hle : rankOf π ρ v' u ≤ (St π o x ρ t).M v'
          · rw [if_pos hle]; exact ih v
          · rw [if_neg hle, Function.update_of_ne hv]; exact ih v

theorem length_newEdges_le (v : V) (m r : ℕ) : (newEdges π ρ o v m r).length ≤ r - m - 1 := by
  unfold newEdges
  rw [List.length_map, Finset.length_toList]
  calc ((Finset.univ : Finset (G.neighborSet v)).filter
        (fun w => w.1 ≠ o ∧ m < rank π ρ v w ∧ rank π ρ v w < r)).card
      ≤ (Finset.Ioo m r).card := by
        refine card_le_card_of_injOn (fun w => rank π ρ v w) ?_ ?_
        · intro w hw
          simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hw
          exact mem_Ioo.2 ⟨hw.2.1, hw.2.2⟩
        · intro w _ w' _ he
          exact cycRank_right_injective (π.next v) (π.cyclic v) (ρ v) he
    _ = r - m - 1 := by rw [Nat.card_Ioo]

/-- Processing an edge into an already reached vertex does not lengthen the queue. -/
theorem queue_length_succ_le_of_mem_hist (hox : G.Adj o x) (h3 : ∀ v : V, G.degree v ≤ 3)
    {t : ℕ} {u v : V} {rest : List (V × V)} (hq : (St π o x ρ t).queue = (u, v) :: rest)
    (hv : v ∈ (St π o x ρ t).hist) :
    (St π o x ρ (t + 1)).queue.length ≤ (St π o x ρ t).queue.length := by
  rw [St_succ, qStep_queue_cons π o ρ hq, hq, List.length_append, List.length_cons]
  split_ifs with h
  · simp
  · have hM := (mem_hist_iff_M_pos π o x ρ hox t v).1 hv
    have h1 := length_newEdges_le π o ρ v ((St π o x ρ t).M v) (rankOf π ρ v u)
    have h2 := rankOf_le_degree π ρ v u
    have h3' := h3 v
    omega

/-- Processing an edge into a fresh vertex adds at most `r_v(u) - 1` edges. -/
theorem queue_length_succ_le_fresh {t : ℕ} {u v : V} {rest : List (V × V)}
    (hq : (St π o x ρ t).queue = (u, v) :: rest) (hv : (St π o x ρ t).M v = 0) :
    (St π o x ρ (t + 1)).queue.length + 1 ≤ (St π o x ρ t).queue.length + (rankOf π ρ v u - 1) := by
  rw [St_succ, qStep_queue_cons π o ρ hq, hq, List.length_append, List.length_cons]
  split_ifs with h
  · simp
  · have h1 := length_newEdges_le π o ρ v ((St π o x ρ t).M v) (rankOf π ρ v u)
    rw [hv] at h1 ⊢
    omega

/-- FIFO: the queue at time `t + p` begins with the tail of the queue at time `t` from
position `p`. -/
theorem queue_drop (t : ℕ) : ∀ p : ℕ, p ≤ (St π o x ρ t).queue.length →
    ∃ L, (St π o x ρ (t + p)).queue = (St π o x ρ t).queue.drop p ++ L
  | 0, _ => ⟨[], by simp⟩
  | p + 1, hp => by
    obtain ⟨L, hL⟩ := queue_drop t p (by omega)
    rw [← add_assoc, St_succ]
    obtain ⟨e, rest, hrest⟩ : ∃ e rest, (St π o x ρ t).queue.drop p = e :: rest := by
      have : (St π o x ρ t).queue.drop p ≠ [] := by
        rw [ne_eq, List.drop_eq_nil_iff]; omega
      exact List.exists_cons_of_ne_nil this
    have hq : (St π o x ρ (t + p)).queue = (e.1, e.2) :: (rest ++ L) := by
      rw [hL, hrest, List.cons_append]
    have h2 : (St π o x ρ t).queue.drop (p + 1) = rest := by
      rw [← List.tail_drop, hrest]
      rfl
    refine ⟨L ++ (if rankOf π ρ e.2 e.1 ≤ (St π o x ρ (t + p)).M e.2 then []
      else newEdges π ρ o e.2 ((St π o x ρ (t + p)).M e.2) (rankOf π ρ e.2 e.1)), ?_⟩
    show (qStep π o ρ (St π o x ρ (t + p))).queue = _
    rw [qStep_queue_cons π o ρ hq, h2, List.append_assoc]

/-- The edge at position `p` of the queue is processed `p` steps later. -/
theorem head_eq_of_lt {t p : ℕ} (hp : p < (St π o x ρ t).queue.length) :
    ∃ rest, (St π o x ρ (t + p)).queue = (St π o x ρ t).queue[p] :: rest := by
  obtain ⟨L, hL⟩ := queue_drop π o x ρ t p hp.le
  exact ⟨_, by rw [hL, List.drop_eq_getElem_cons hp, List.cons_append]⟩

/-- Processing `u → v` makes `M_v ≥ r_v(u)`. -/
theorem rankOf_le_M_succ {t : ℕ} {u v : V} {rest : List (V × V)}
    (hq : (St π o x ρ t).queue = (u, v) :: rest) :
    rankOf π ρ v u ≤ (St π o x ρ (t + 1)).M v := by
  rw [St_succ, qStep_M_cons π o ρ hq]
  split_ifs with h
  · exact h
  · rw [Function.update_self]

/-- Every queued edge other than the initial one was added while processing an entry of
larger rank into its tail. -/
theorem exists_added (hox : G.Adj o x) {a b : V} (hne : a ≠ o) :
    ∀ s : ℕ, (a, b) ∈ (St π o x ρ s).queue →
      ∃ s₀ < s, ∃ hab : G.Adj a b, rank π ρ a ⟨b, hab⟩ < (St π o x ρ (s₀ + 1)).M a
  | 0, h => by
    simp only [St_zero, qInit, List.mem_singleton, Prod.mk.injEq] at h
    exact absurd h.1 hne
  | s + 1, h => by
    rw [St_succ] at h
    rcases hq : (St π o x ρ s).queue with _ | ⟨⟨u, v⟩, rest⟩
    · rw [qStep_queue_nil π o ρ hq, hq] at h
      simp at h
    · rw [qStep_queue_cons π o ρ hq, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨s₀, hs₀, hab, hlt⟩ :=
          exists_added hox hne s (by rw [hq]; exact List.mem_cons_of_mem _ h)
        exact ⟨s₀, by omega, hab, hlt⟩
      · split_ifs at h with hle
        · simp at h
        · obtain ⟨h1, hab, -, -, hlt⟩ := (mem_newEdges π o ρ).1 h
          simp only at h1 hab hlt
          subst h1
          refine ⟨s, lt_add_one s, hab, ?_⟩
          rw [St_succ, qStep_M_cons π o ρ hq, if_neg hle, Function.update_self]
          exact hlt

/-- The invariant behind `rotor.tex:1338-1341`: every exit `v → w` with `w ≠ o` and
`r_v(w) ≤ M_v` has been added, unless `w → v` was processed and increased `M_v`. -/
theorem inv_added (hox : G.Adj o x) : ∀ (t : ℕ) (v w : V) (hvw : G.Adj v w), w ≠ o →
    rank π ρ v ⟨w, hvw⟩ ≤ (St π o x ρ t).M v →
    (∃ s ≤ t, (v, w) ∈ (St π o x ρ s).queue) ∨
    (∃ s < t, (St π o x ρ s).queue.head? = some (w, v) ∧
      (St π o x ρ s).M v < rank π ρ v ⟨w, hvw⟩)
  | 0, v, w, hvw, _, hle => by
    simp only [St_zero, qInit] at hle
    have := cycRank_pos (π.next v) (π.cyclic v) (ρ v) ⟨w, hvw⟩
    rw [rank_eq_cycRank] at hle
    omega
  | t + 1, v, w, hvw, hwo, hle => by
    have lift : (∃ s ≤ t, (v, w) ∈ (St π o x ρ s).queue) ∨
        (∃ s < t, (St π o x ρ s).queue.head? = some (w, v) ∧
          (St π o x ρ s).M v < rank π ρ v ⟨w, hvw⟩) →
        (∃ s ≤ t + 1, (v, w) ∈ (St π o x ρ s).queue) ∨
        (∃ s < t + 1, (St π o x ρ s).queue.head? = some (w, v) ∧
          (St π o x ρ s).M v < rank π ρ v ⟨w, hvw⟩) := by
      rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
      · exact Or.inl ⟨s, by omega, h⟩
      · exact Or.inr ⟨s, by omega, h⟩
    rcases hq : (St π o x ρ t).queue with _ | ⟨⟨u, v'⟩, rest⟩
    · rw [St_succ, qStep_queue_nil π o ρ hq] at hle
      exact lift (inv_added hox t v w hvw hwo hle)
    · rw [St_succ, qStep_M_cons π o ρ hq] at hle
      split_ifs at hle with hle'
      · exact lift (inv_added hox t v w hvw hwo hle)
      · by_cases hv : v = v'
        · subst hv
          rw [Function.update_self] at hle
          rcases le_or_gt (rank π ρ v ⟨w, hvw⟩) ((St π o x ρ t).M v) with h1 | h1
          · exact lift (inv_added hox t v w hvw hwo h1)
          · rcases lt_or_eq_of_le hle with h2 | h2
            · left
              refine ⟨t + 1, le_rfl, ?_⟩
              rw [St_succ, qStep_queue_cons π o ρ hq, if_neg hle', List.mem_append]
              exact Or.inr ((mem_newEdges π o ρ).2 ⟨rfl, hvw, hwo, h1, h2⟩)
            · right
              have hadj : G.Adj v u :=
                (queue_adj π o x ρ hox t (u, v) (by rw [hq]; simp)).symm
              rw [rankOf_eq π ρ hadj] at h2 hle'
              have hwu : w = u := by
                have := cycRank_right_injective (π.next v) (π.cyclic v) (ρ v) h2
                exact congrArg Subtype.val this
              subst hwu
              exact ⟨t, lt_add_one t, by rw [hq]; rfl, not_le.1 hle'⟩
        · rw [Function.update_of_ne hv] at hle
          exact lift (inv_added hox t v w hvw hwo hle)

/-- `rotor.tex:1348-1362`: along an infinite live path `y` starting with `o → x`, every
`M_{y(i+1)}` eventually reaches `r_{y(i+1)}(y i)`. -/
theorem rankOf_le_M_of_infLive (hox : G.Adj o x) {y : ℕ → V} (hpath : IsInfPath G y)
    (hlive : IsInfLive π ρ y) (h0 : y 0 = o) (h1 : y 1 = x) :
    ∀ i : ℕ, ∃ t, rankOf π ρ (y (i + 1)) (y i) ≤ (St π o x ρ t).M (y (i + 1))
  | 0 => ⟨1, by
      rw [h0, h1]
      exact rankOf_le_M_succ π o x ρ (t := 0) (u := o) (v := x) (rest := []) rfl⟩
  | i + 1 => by
    obtain ⟨t, ht⟩ := rankOf_le_M_of_infLive hox hpath hlive h0 h1 i
    obtain ⟨hw, hu, hlt⟩ := hlive i
    have hne : y (i + 2) ≠ o := by
      rw [← h0]
      intro h
      have := hpath.1 h
      omega
    have hle : rank π ρ (y (i + 1)) ⟨y (i + 2), hw⟩ ≤ (St π o x ρ t).M (y (i + 1)) := by
      rw [rankOf_eq π ρ hu] at ht
      exact hlt.le.trans ht
    rcases inv_added π o x ρ hox t (y (i + 1)) (y (i + 2)) hw hne hle with
      ⟨s, -, hmem⟩ | ⟨s, -, hhead, -⟩
    · obtain ⟨p, hp, hget⟩ := List.getElem_of_mem hmem
      obtain ⟨rest, hrest⟩ := head_eq_of_lt π o x ρ hp
      rw [hget] at hrest
      exact ⟨s + p + 1, rankOf_le_M_succ π o x ρ hrest⟩
    · have hmem : (y (i + 2), y (i + 1)) ∈ (St π o x ρ s).queue := List.mem_of_mem_head? hhead
      obtain ⟨s₀, -, hab, hlt'⟩ := exists_added π o x ρ hox hne s hmem
      exact ⟨s₀ + 1, by rw [rankOf_eq π ρ hab]; exact hlt'.le⟩

/-- An infinite live path forces infinitely many reached vertices. -/
theorem exists_hist_length_ge (hox : G.Adj o x) {y : ℕ → V} (hpath : IsInfPath G y)
    (hlive : IsInfLive π ρ y) (h0 : y 0 = o) (h1 : y 1 = x) (j : ℕ) :
    ∃ t, j ≤ (St π o x ρ t).hist.length := by
  classical
  choose T hT using rankOf_le_M_of_infLive π o x ρ hox hpath hlive h0 h1
  refine ⟨(Finset.range j).sup T, ?_⟩
  have hmem : ∀ i ∈ Finset.range j, y (i + 1) ∈ (St π o x ρ ((Finset.range j).sup T)).hist := by
    intro i hi
    have hTi : T i ≤ (Finset.range j).sup T := Finset.le_sup hi
    have hpos : 0 < (St π o x ρ (T i)).M (y (i + 1)) :=
      lt_of_lt_of_le (rankOf_pos π ρ (hpath.2 i).symm) (hT i)
    have hmem' := (mem_hist_iff_M_pos π o x ρ hox (T i) _).2 hpos
    exact ((qProc π o x).hist_run_prefix ρ hTi).subset hmem'
  have hinj : Set.InjOn (fun i => y (i + 1)) ↑(Finset.range j) := by
    intro a _ b _ hab
    have := hpath.1 hab
    omega
  calc j = (Finset.range j).card := (Finset.card_range j).symm
    _ = ((Finset.range j).image (fun i => y (i + 1))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (St π o x ρ ((Finset.range j).sup T)).hist.toFinset.card := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
        exact List.mem_toFinset.2 (hmem i hi)
    _ ≤ (St π o x ρ ((Finset.range j).sup T)).hist.length := List.toFinset_card_le _

end Run

end Rotor
