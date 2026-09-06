import Rotor.Support.ChainWeight

/-!
Adaptive reading of independent rotors, `rotor.tex:1370-1376` ("For each reached `v`, its
rotor is unexamined when the first edge entering `v` is processed.  Conditional on the past,
`r_v(u)` is uniform") and `rotor.tex:1919-1924` (Section 5, conditional probabilities given
the earlier test outcomes).

A `QueryProcess` is a deterministic state machine driven by the rotors that, at each step,
may read the rotor at one new vertex; the vertex read depends only on the rotors read so
far.  The atom of a history `h` (the vertices read so far with the values found) is the set
of configurations that produce it; it is determined by the coordinates in `h`, so the next
rotor read is independent of it and uniform.
-/

open MeasureTheory ProbabilityTheory

namespace Rotor

variable {V : Type*} {G : SimpleGraph V}

/-- A deterministic process driven by the rotors, reading the rotor at one new vertex at a
time. -/
structure QueryProcess (G : SimpleGraph V) (S : Type*) where
  /-- the initial state -/
  init : S
  /-- one step, reading the rotors `ρ` -/
  step : Config G → S → S
  /-- the vertices whose rotors have been read, in order -/
  hist : S → List V
  hist_init : hist init = []
  hist_step : ∀ ρ s, hist (step ρ s) = hist s ∨
    ∃ v, v ∉ hist s ∧ hist (step ρ s) = hist s ++ [v]
  /-- the step depends on the rotors only through the vertices read so far, including the
  one read at this step -/
  local_step : ∀ ρ ρ' s, (∀ v ∈ hist (step ρ s), ρ v = ρ' v) → step ρ s = step ρ' s
  /-- which vertex is read depends only on the rotors read before -/
  read_step : ∀ ρ ρ' s, (∀ v ∈ hist s, ρ v = ρ' v) → hist (step ρ s) = hist (step ρ' s)

namespace QueryProcess

variable {S : Type*} (Q : QueryProcess G S)

/-- The state after `t` steps. -/
def run (ρ : Config G) (t : ℕ) : S := (Q.step ρ)^[t] Q.init

@[simp] theorem run_zero (ρ : Config G) : Q.run ρ 0 = Q.init := rfl

theorem run_succ (ρ : Config G) (t : ℕ) : Q.run ρ (t + 1) = Q.step ρ (Q.run ρ t) :=
  Function.iterate_succ_apply' _ _ _

theorem hist_prefix_step (ρ : Config G) (s : S) : Q.hist s <+: Q.hist (Q.step ρ s) := by
  rcases Q.hist_step ρ s with h | ⟨v, -, h⟩
  · rw [h]
  · rw [h]; exact List.prefix_append _ _

theorem hist_run_prefix (ρ : Config G) {t t' : ℕ} (h : t ≤ t') :
    Q.hist (Q.run ρ t) <+: Q.hist (Q.run ρ t') := by
  induction t' with
  | zero => rw [Nat.le_zero.1 h]
  | succ t' ih =>
    rcases Nat.lt_or_ge t (t' + 1) with h' | h'
    · exact (ih (by omega)).trans (by rw [run_succ]; exact Q.hist_prefix_step ρ _)
    · rw [Nat.le_antisymm h h']

theorem hist_run_nodup (ρ : Config G) : ∀ t : ℕ, (Q.hist (Q.run ρ t)).Nodup
  | 0 => by simp [Q.hist_init]
  | t + 1 => by
    rw [run_succ]
    rcases Q.hist_step ρ (Q.run ρ t) with h | ⟨v, hv, h⟩
    · rw [h]; exact hist_run_nodup ρ t
    · rw [h, List.nodup_append]
      exact ⟨hist_run_nodup ρ t, List.nodup_singleton v, fun a ha b hb => by
        simp only [List.mem_singleton] at hb; subst hb; exact fun h => hv (h ▸ ha)⟩

/-- Locality: the run depends on the rotors only at the vertices read. -/
theorem run_local (ρ ρ' : Config G) : ∀ t : ℕ,
    (∀ v ∈ Q.hist (Q.run ρ t), ρ v = ρ' v) → Q.run ρ' t = Q.run ρ t
  | 0, _ => rfl
  | t + 1, h => by
    have hpre := Q.hist_run_prefix ρ (Nat.le_succ t)
    have ih := run_local ρ ρ' t (fun v hv => h v (hpre.subset hv))
    rw [run_succ, run_succ, ih]
    exact (Q.local_step ρ ρ' (Q.run ρ t) (fun v hv => h v (by rwa [run_succ]))).symm

/-- The vertex read at the next step depends only on the rotors read so far. -/
theorem hist_run_succ_congr (ρ ρ' : Config G) (t : ℕ)
    (h : ∀ v ∈ Q.hist (Q.run ρ t), ρ v = ρ' v) :
    Q.hist (Q.run ρ' (t + 1)) = Q.hist (Q.run ρ (t + 1)) := by
  rw [run_succ, run_succ, Q.run_local ρ ρ' t h]
  exact (Q.read_step ρ ρ' (Q.run ρ t) h).symm

/-- Every prefix of the history is the history at some earlier time. -/
theorem exists_run_hist_eq_prefix (ρ : Config G) : ∀ (t : ℕ) (l : List V),
    l <+: Q.hist (Q.run ρ t) → ∃ t' ≤ t, Q.hist (Q.run ρ t') = l
  | 0, l, hl => ⟨0, le_rfl, by
      rw [run_zero, Q.hist_init] at hl ⊢; exact (List.prefix_nil.1 hl).symm⟩
  | t + 1, l, hl => by
    rw [run_succ] at hl
    rcases Q.hist_step ρ (Q.run ρ t) with h | ⟨v, -, h⟩
    · rw [h] at hl
      obtain ⟨t', ht', e⟩ := exists_run_hist_eq_prefix ρ t l hl
      exact ⟨t', by omega, e⟩
    · rw [h] at hl
      rcases List.prefix_concat_iff.1 hl with h' | h'
      · exact ⟨t + 1, le_rfl, by rw [run_succ, h, h']⟩
      · obtain ⟨t', ht', e⟩ := exists_run_hist_eq_prefix ρ t l h'
        exact ⟨t', by omega, e⟩

/-- A history: the vertices read, with the rotors found there. -/
abbrev History (G : SimpleGraph V) := List (Σ v : V, G.neighborSet v)

/-- The vertices of a history. -/
def verts (h : History G) : List V := h.map Sigma.fst

/-- The atom of a history: the configurations whose reads begin with `h`. -/
def atomF (h : History G) : Set (Config G) :=
  {ρ | (∃ t, Q.hist (Q.run ρ t) = verts h) ∧ ∀ x ∈ h, ρ x.1 = x.2}

/-- The event that the vertex read after the history `h` is `v`. -/
def Nxt (h : History G) (v : V) : Set (Config G) :=
  {ρ | ∃ t, Q.hist (Q.run ρ t) = verts h ++ [v]}

theorem atomF_nil : Q.atomF ([] : History G) = Set.univ := by
  ext ρ
  simp only [atomF, verts, List.map_nil, List.not_mem_nil, false_implies, implies_true,
    and_true, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨0, by simp [Q.hist_init]⟩

theorem atomF_determined [DecidableEq V] (h : History G) :
    DeterminedBy (↑(verts h).toFinset) (Q.atomF h) := by
  intro ρ ρ' hagree ⟨⟨t, ht⟩, hval⟩
  have hagree' : ∀ v ∈ Q.hist (Q.run ρ t), ρ v = ρ' v := fun v hv =>
    hagree v (by rw [List.coe_toFinset]; rwa [ht] at hv)
  refine ⟨⟨t, by rw [Q.run_local ρ ρ' t hagree', ht]⟩, fun x hx => ?_⟩
  rw [← hagree' x.1 (by rw [ht]; exact List.mem_map_of_mem hx), hval x hx]

theorem length_hist_run_succ_le (ρ : Config G) (t : ℕ) :
    (Q.hist (Q.run ρ (t + 1))).length ≤ (Q.hist (Q.run ρ t)).length + 1 := by
  rw [run_succ]
  rcases Q.hist_step ρ (Q.run ρ t) with h | ⟨v, -, h⟩
  · rw [h]; omega
  · rw [h, List.length_append, List.length_singleton]

/-- If the history is `l ++ [v]` at time `t`, then at the last time before `t` it was `l`,
and the step from there reads `v`. -/
theorem exists_hist_eq_and_succ (ρ : Config G) {t : ℕ} {l : List V} {v : V}
    (ht : Q.hist (Q.run ρ t) = l ++ [v]) :
    ∃ t₁, Q.hist (Q.run ρ t₁) = l ∧ Q.hist (Q.run ρ (t₁ + 1)) = l ++ [v] := by
  classical
  have hex : ∃ t, Q.hist (Q.run ρ t) = l ++ [v] := ⟨t, ht⟩
  have h₀ : Q.hist (Q.run ρ (Nat.find hex)) = l ++ [v] := Nat.find_spec hex
  cases ht₀ : Nat.find hex with
  | zero =>
    rw [ht₀, run_zero, Q.hist_init] at h₀
    simpa using congrArg List.length h₀
  | succ t₁ =>
    rw [ht₀] at h₀
    refine ⟨t₁, ?_, h₀⟩
    have hpre := Q.hist_run_prefix ρ (Nat.le_succ t₁)
    rw [h₀] at hpre
    have hne : Q.hist (Q.run ρ t₁) ≠ l ++ [v] := Nat.find_min hex (by omega)
    have hlt : (Q.hist (Q.run ρ t₁)).length < (l ++ [v]).length := by
      rcases lt_or_eq_of_le hpre.length_le with h | h
      · exact h
      · exact absurd (hpre.eq_of_length h) hne
    have hlen := Q.length_hist_run_succ_le ρ t₁
    rw [h₀, List.length_append, List.length_singleton] at hlen
    rw [List.length_append, List.length_singleton] at hlt
    have hpre' : Q.hist (Q.run ρ t₁) <+: l :=
      List.prefix_of_prefix_length_le hpre (List.prefix_append l [v]) (by omega)
    exact hpre'.eq_of_length (by omega)

theorem atomF_inter_Nxt_determined [DecidableEq V] (h : History G) (v : V) :
    DeterminedBy (↑(verts h).toFinset) (Q.atomF h ∩ Q.Nxt h v) := by
  intro ρ ρ' hagree ⟨hmem, ⟨t, ht⟩⟩
  refine ⟨Q.atomF_determined h ρ ρ' hagree hmem, ?_⟩
  obtain ⟨t₁, ht₁, ht₁'⟩ := Q.exists_hist_eq_and_succ ρ ht
  refine ⟨t₁ + 1, ?_⟩
  rw [Q.hist_run_succ_congr ρ ρ' t₁ (fun w hw => hagree w (by
    rw [List.coe_toFinset]; rwa [ht₁] at hw)), ht₁']

theorem atomF_append (h : History G) (v : V) (a : G.neighborSet v) :
    Q.atomF (h ++ [⟨v, a⟩]) = (Q.atomF h ∩ Q.Nxt h v) ∩ (fun ρ : Config G => ρ v) ⁻¹' {a} := by
  ext ρ
  simp only [atomF, Nxt, verts, List.map_append, List.map_cons, List.map_nil, Set.mem_setOf_eq,
    Set.mem_inter_iff, List.mem_append, List.mem_singleton, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨t, ht⟩, hval⟩
    obtain ⟨t', -, ht'⟩ := Q.exists_run_hist_eq_prefix ρ t (h.map Sigma.fst)
      (by rw [ht]; exact List.prefix_append _ _)
    exact ⟨⟨⟨⟨t', ht'⟩, fun x hx => hval x (Or.inl hx)⟩, ⟨t, ht⟩⟩, hval ⟨v, a⟩ (Or.inr rfl)⟩
  · rintro ⟨⟨⟨-, hval⟩, ⟨t, ht⟩⟩, hva⟩
    refine ⟨⟨t, ht⟩, fun x hx => ?_⟩
    rcases hx with hx | rfl
    · exact hval x hx
    · exact hva

theorem atomF_prefix {h h' : History G} (hh : h <+: h') {ρ : Config G} (hρ : ρ ∈ Q.atomF h') :
    ρ ∈ Q.atomF h := by
  obtain ⟨⟨t, ht⟩, hval⟩ := hρ
  obtain ⟨t', -, ht'⟩ := Q.exists_run_hist_eq_prefix ρ t (verts h) (by
    rw [ht]; exact hh.map Sigma.fst)
  exact ⟨⟨t', ht'⟩, fun x hx => hval x (hh.subset hx)⟩

end QueryProcess

section Measure

variable [DecidableEq V] [G.LocallyFinite] {S : Type*} (Q : QueryProcess G S)

namespace QueryProcess

theorem measurableSet_atomF (h : History G) : MeasurableSet (Q.atomF h) :=
  (Q.atomF_determined h).measurableSet _

theorem measurableSet_atomF_inter_Nxt (h : History G) (v : V) :
    MeasurableSet (Q.atomF h ∩ Q.Nxt h v) :=
  (Q.atomF_inter_Nxt_determined h v).measurableSet _

/-- The rotor read next is independent of the past and has its own law. -/
theorem productLaw_atomF_append (ν : ∀ v : V, Measure (G.neighborSet v))
    [∀ v, IsProbabilityMeasure (ν v)] {h : History G} {v : V} (hv : v ∉ verts h)
    (a : G.neighborSet v) :
    productLaw ν (Q.atomF (h ++ [⟨v, a⟩])) = ν v {a} * productLaw ν (Q.atomF h ∩ Q.Nxt h v) := by
  rw [Q.atomF_append, Set.inter_comm, productLaw]
  exact infinitePi_eval_inter ν v {a} (verts h).toFinset (by simpa using hv)
    (Q.atomF_inter_Nxt_determined h v)

/-- Integrating a function of the rotor read next over the atom. -/
theorem setLIntegral_atomF_Nxt (ν : ∀ v : V, Measure (G.neighborSet v))
    [∀ v, IsProbabilityMeasure (ν v)] {h : History G} {v : V} (hv : v ∉ verts h)
    (f : G.neighborSet v → ENNReal) :
    ∫⁻ ρ in Q.atomF h ∩ Q.Nxt h v, f (ρ v) ∂(productLaw ν)
      = productLaw ν (Q.atomF h ∩ Q.Nxt h v) * ∑ a, f a * ν v {a} := by
  have hpt : ∀ ρ : Config G, f (ρ v) =
      ∑ a, (((fun ρ : Config G => ρ v) ⁻¹' {a}).indicator (fun _ => f a)) ρ := by
    intro ρ
    rw [Finset.sum_eq_single (ρ v)]
    · simp
    · intro a _ ha
      simp [Set.indicator, Ne.symm ha]
    · simp
  simp_rw [hpt]
  have hms : ∀ a : G.neighborSet v, MeasurableSet ((fun ρ : Config G => ρ v) ⁻¹' {a}) :=
    fun a => (measurable_pi_apply v) (measurableSet_singleton a)
  rw [lintegral_finset_sum _ (fun a _ => measurable_const.indicator (hms a)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [lintegral_indicator (hms a), setLIntegral_const, Measure.restrict_apply (hms a),
    Set.inter_comm, ← Q.atomF_append, Q.productLaw_atomF_append ν hv a]
  ring

end QueryProcess

end Measure

end Rotor
