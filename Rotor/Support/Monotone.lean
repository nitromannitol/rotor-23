/-
Monotonicity of the circuit map, `prop:monotonicity` (`rotor.tex:801-809`):
"Lemma boundary-routing and Lemma least-action imply monotonicity of the
circuit map."  The argument: a complete boundary routing of `S`, with its
actuations inside `U` deleted, is a legal boundary routing of `U`, because
the particles that the deleted actuations would have delivered to `V ∖ U`
are already present in the initial state of the `U`-routing (one per edge
from `U` into each vertex, and no edge is traversed twice).  The abelian
property then makes every complete `U`-routing actuate every vertex outside
`U` that the `S`-routing actuates.
-/
import Rotor.Support.BoundaryRouting

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

/-! ### The splitting characterization of legality -/

theorem isLegal_split (S : Finset V) (ξ : RState G) (l₁ : List V) (v : V) (l₂ : List V)
    (h : IsLegal π S ξ (l₁ ++ v :: l₂)) : v ∉ S ∧ 0 < (run π S ξ l₁).σ v := by
  rw [isLegal_append, isLegal_cons] at h
  exact ⟨h.2.1, h.2.2.1⟩

theorem isLegal_of_split (S : Finset V) (ξ : RState G) (vs : List V)
    (h : ∀ l₁ v l₂, vs = l₁ ++ v :: l₂ → v ∉ S ∧ 0 < (run π S ξ l₁).σ v) :
    IsLegal π S ξ vs := by
  induction vs generalizing ξ with
  | nil => trivial
  | cons v vs ih =>
    rw [isLegal_cons]
    obtain ⟨h1, h2⟩ := h [] v vs rfl
    refine ⟨h1, h2, ih _ (fun l₁ w l₂ hl => ?_)⟩
    have := h (v :: l₁) w l₂ (by rw [hl]; rfl)
    simpa using this

/-! ### Deleting the actuations inside `U` -/

/-- Two states agree outside `U`: their rotors agree at every vertex outside `U`. -/
def AgreeOutside (U : Finset V) (ξ ξ' : RState G) : Prop := ∀ x, x ∉ U → ξ.ρ x = ξ'.ρ x

theorem agreeOutside_actuate_both (S U : Finset V) (ξ ξ' : RState G)
    (h : AgreeOutside U ξ ξ') (v : V) (hv : v ∉ U) :
    AgreeOutside U (actuate π S ξ v) (actuate π U ξ' v) := by
  intro x hx
  by_cases hxv : x = v
  · subst hxv; rw [actuate_ρ_self, actuate_ρ_self, h x hx]
  · rw [actuate_ρ_of_ne π S ξ v x hxv, actuate_ρ_of_ne π U ξ' v x hxv, h x hx]

theorem agreeOutside_actuate_left (S U : Finset V) (ξ ξ' : RState G)
    (h : AgreeOutside U ξ ξ') (v : V) (hv : v ∈ U) :
    AgreeOutside U (actuate π S ξ v) ξ' := by
  intro x hx
  have hxv : x ≠ v := fun e => hx (e ▸ hv)
  rw [actuate_ρ_of_ne π S ξ v x hxv, h x hx]

/-- The traversed edges of the routing with the actuations inside `U` deleted
are the traversed edges with tails outside `U`, and the runs still agree
outside `U`. -/
theorem traversed_filter (S U : Finset V) (ξ ξ' : RState G) (h : AgreeOutside U ξ ξ')
    (p : List V) :
    traversed π U ξ' (p.filter (fun v => decide (v ∉ U))) =
      (traversed π S ξ p).filter (fun e => decide (e.1 ∉ U)) ∧
    AgreeOutside U (run π S ξ p) (run π U ξ' (p.filter (fun v => decide (v ∉ U)))) := by
  induction p generalizing ξ ξ' with
  | nil => exact ⟨rfl, h⟩
  | cons v p ih =>
    by_cases hv : v ∈ U
    · have hf : (v :: p).filter (fun v => decide (v ∉ U)) = p.filter (fun v => decide (v ∉ U)) := by
        simp [hv]
      rw [hf, traversed_cons, run_cons]
      have := ih (actuate π S ξ v) ξ' (agreeOutside_actuate_left π S U ξ ξ' h v hv)
      refine ⟨?_, this.2⟩
      rw [this.1, List.filter_cons]
      simp [hv]
    · have hf : (v :: p).filter (fun v => decide (v ∉ U)) = v :: p.filter (fun v => decide (v ∉ U)) := by
        simp [hv]
      rw [hf, traversed_cons, traversed_cons, run_cons, run_cons]
      have := ih (actuate π S ξ v) (actuate π U ξ' v) (agreeOutside_actuate_both π S U ξ ξ' h v hv)
      refine ⟨?_, this.2⟩
      rw [this.1, List.filter_cons, h v hv]
      simp [hv]

/-! ### Particle counts without legality: a lower bound -/

/-- Without legality, the particle count is at least the virtual count:
`ℕ`-subtraction only ever leaves more particles. -/
theorem run_σ_add_count_ge (S : Finset V) (ξ : RState G) (vs : List V) (x : V) (hx : x ∉ S) :
    ξ.σ x + arrivals π S ξ vs x ≤ (run π S ξ vs).σ x + vs.count x := by
  induction vs generalizing ξ with
  | nil => simp [arrivals]
  | cons v vs ih =>
    rw [run_cons]
    have h := ih (actuate π S ξ v)
    simp only [arrivals, traversed_cons, List.countP_cons, List.count_cons] at h ⊢
    rw [actuate_σ] at h
    by_cases hxv : x = v
    · subst hxv
      have hne : (π.next x (ξ.ρ x)).1 ≠ x := next_head_ne π ξ x
      have hne' : ¬ (x = (π.next x (ξ.ρ x)).1 ∧ (π.next x (ξ.ρ x)).1 ∉ S) := fun h => hne h.1.symm
      simp only [if_true, hne', if_false, add_zero, decide_eq_true_eq, hne, beq_self_eq_true,
        if_true] at h ⊢
      omega
    · have hvx : (v == x) = false := by simpa using Ne.symm hxv
      simp only [hxv, if_false, hvx, Bool.false_eq_true, add_zero, decide_eq_true_eq] at h ⊢
      by_cases hh : (π.next v (ξ.ρ v)).1 = x
      · simp only [hh, hx, not_false_eq_true, and_self, if_true] at h ⊢
        omega
      · have hh' : ¬ (x = (π.next v (ξ.ρ v)).1 ∧ (π.next v (ξ.ρ v)).1 ∉ S) := fun h => hh h.1.symm
        simp only [hh, hh', if_false, add_zero] at h ⊢
        omega

/-! ### Counting the arrivals from `U ∖ S` -/

open Classical in
theorem countP_head_tail_le [G.LocallyFinite] (S U : Finset V) (L : List (V × V)) (hL : L.Nodup)
    (x : V) (hadj : ∀ e ∈ L, G.Adj e.1 e.2) (hS : ∀ e ∈ L, e.1 ∉ S) :
    L.countP (fun e => decide (e.2 = x) && decide (e.1 ∈ U)) ≤
      ((U \ S).filter (fun t => G.Adj t x)).card := by
  rw [List.countP_eq_length_filter]
  set L' := L.filter (fun e => decide (e.2 = x) && decide (e.1 ∈ U)) with hL'
  have hsub : ∀ t ∈ L'.map Prod.fst, t ∈ (U \ S).filter (fun t => G.Adj t x) := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    rw [hL', List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at he
    rw [Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨⟨he.2.2, hS e he.1⟩, he.2.1 ▸ hadj e he.1⟩
  have hnd : (L'.map Prod.fst).Nodup := by
    refine List.Nodup.map_on ?_ (hL.filter _)
    intro e₁ he₁ e₂ he₂ h
    rw [hL', List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at he₁ he₂
    exact Prod.ext h (he₁.2.1.trans he₂.2.1.symm)
  calc L'.length = (L'.map Prod.fst).length := (List.length_map _).symm
    _ = (L'.map Prod.fst).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ _ := Finset.card_le_card (fun t ht => hsub t (List.mem_toFinset.1 ht))

open Classical in
theorem card_inEdges_split [G.LocallyFinite] (S U : Finset V) (hSU : S ⊆ U) (x : V) :
    (U.filter (fun u => G.Adj u x)).card =
      (S.filter (fun s => G.Adj s x)).card + ((U \ S).filter (fun t => G.Adj t x)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hU, hadj⟩
      by_cases hs : t ∈ S
      · exact Or.inl ⟨hs, hadj⟩
      · exact Or.inr ⟨⟨hU, hs⟩, hadj⟩
    · rintro (⟨hs, hadj⟩ | ⟨⟨hU, _⟩, hadj⟩)
      · exact ⟨hSU hs, hadj⟩
      · exact ⟨hU, hadj⟩
  · rw [Finset.disjoint_left]
    intro t ht ht'
    simp only [Finset.mem_filter, Finset.mem_sdiff] at ht ht'
    exact ht'.1.2 ht.1

/-! ### The comparison of particle counts outside `U` -/

open Classical in
/-- Along a legal `S`-routing `p`, the particles outside `U` are at most those
of the `U`-routing with the actuations inside `U` deleted. -/
theorem σ_le_filtered [G.LocallyFinite] (S U : Finset V) (hSU : S ⊆ U) (ρ : Config G) (p : List V)
    (hleg : IsLegal π S (boundaryInit S ρ) p) (x : V) (hx : x ∉ U) :
    (run π S (boundaryInit S ρ) p).σ x ≤
      (run π U (boundaryInit U ρ) (p.filter (fun v => decide (v ∉ U)))).σ x := by
  have hxS : x ∉ S := fun h => hx (hSU h)
  have hagree : AgreeOutside U (boundaryInit S ρ) (boundaryInit U ρ) := fun _ _ => rfl
  obtain ⟨htr, -⟩ := traversed_filter π S U (boundaryInit S ρ) (boundaryInit U ρ) hagree p
  have hS := run_σ_eq π S (boundaryInit S ρ) p x hxS hleg
  have hU := run_σ_add_count_ge π U (boundaryInit U ρ) (p.filter (fun v => decide (v ∉ U))) x hx
  have hcount : (p.filter (fun v => decide (v ∉ U))).count x = p.count x := by
    rw [List.count_filter]; simp [hx]
  have hinitS : (boundaryInit S ρ).σ x = (S.filter (fun s => G.Adj s x)).card := by
    simp [boundaryInit, hxS]
  have hinitU : (boundaryInit U ρ).σ x = (U.filter (fun u => G.Adj u x)).card := by
    simp [boundaryInit, hx]
  have hsplit := card_inEdges_split (G := G) S U hSU x
  -- arrivals in the `S`-routing split by the tail
  have harrS : arrivals π S (boundaryInit S ρ) p x =
      arrivals π U (boundaryInit U ρ) (p.filter (fun v => decide (v ∉ U))) x +
        (traversed π S (boundaryInit S ρ) p).countP
          (fun e => decide (e.2 = x) && decide (e.1 ∈ U)) := by
    unfold arrivals
    rw [htr, List.countP_filter]
    rw [List.countP_eq_countP_filter_add (traversed π S (boundaryInit S ρ) p)
      (fun e => decide (e.2 = x)) (fun e => decide (e.1 ∉ U))]
    rw [List.countP_filter, List.countP_filter]
    congr 1
    congr 1
    funext e
    simp
  have hbound := countP_head_tail_le S U (traversed π S (boundaryInit S ρ) p)
    (traversed_nodup π S ρ p hleg) x (adj_of_mem_traversed π S _ p)
    (fun e he => IsLegal.not_mem_sink π S _ p hleg e.1 (fst_mem_of_mem_traversed π S _ p e he))
  rw [hcount, hinitU] at hU
  rw [hinitS, harrS] at hS
  omega

/-! ### Legality of the deleted routing -/

theorem isLegal_filter_of (U : Finset V) (ξU : RState G) (q : V → Bool) (p : List V)
    (h : ∀ l₁ v l₂, p = l₁ ++ v :: l₂ → q v = true →
      v ∉ U ∧ 0 < (run π U ξU (l₁.filter q)).σ v) :
    IsLegal π U ξU (p.filter q) := by
  induction p generalizing ξU with
  | nil => simp
  | cons v p ih =>
    by_cases hv : q v = true
    · rw [List.filter_cons_of_pos hv, isLegal_cons]
      obtain ⟨h1, h2⟩ := h [] v p rfl hv
      simp only [List.filter_nil, run_nil] at h2
      refine ⟨h1, h2, ih (actuate π U ξU v) (fun l₁ w l₂ hl hw => ?_)⟩
      have := h (v :: l₁) w l₂ (by rw [hl]; rfl) hw
      rwa [List.filter_cons_of_pos hv, run_cons] at this
    · rw [List.filter_cons_of_neg hv]
      refine ih ξU (fun l₁ w l₂ hl hw => ?_)
      have := h (v :: l₁) w l₂ (by rw [hl]; rfl) hw
      rwa [List.filter_cons_of_neg hv] at this

/-- Deleting the actuations inside `U` from a legal `S`-routing leaves a legal
`U`-routing. -/
theorem isLegal_filter [G.LocallyFinite] (S U : Finset V) (hSU : S ⊆ U) (ρ : Config G)
    (p : List V) (hleg : IsLegal π S (boundaryInit S ρ) p) :
    IsLegal π U (boundaryInit U ρ) (p.filter (fun v => decide (v ∉ U))) := by
  refine isLegal_filter_of π U _ _ p (fun l₁ v l₂ hl hv => ?_)
  have hvU : v ∉ U := by simpa using hv
  have hleg' : IsLegal π S (boundaryInit S ρ) (l₁ ++ v :: l₂) := hl ▸ hleg
  have hpre : IsLegal π S (boundaryInit S ρ) l₁ := ((isLegal_append π S _ l₁ _).1 hleg').1
  have hpos := (isLegal_split π S _ l₁ v l₂ hleg').2
  exact ⟨hvU, lt_of_lt_of_le hpos (σ_le_filtered π S U hSU ρ l₁ hpre v hvU)⟩

/-! ### The circuit map -/

theorem Φ_of_terminates (ρ : Config G) (S : Finset V) (h : Terminates π S ρ) :
    Φ π ρ S = S ∪ (Classical.choose h).toFinset := by
  simp [Φ, h]

theorem subset_Φ (ρ : Config G) (S : Finset V) : S ⊆ Φ π ρ S := by
  unfold Φ
  split_ifs <;> simp

theorem mem_Φ_imp (ρ : Config G) (S : Finset V) (x : V) (hx : x ∈ Φ π ρ S) :
    x ∈ S ∨ ∃ ws, IsComplete π S (boundaryInit S ρ) ws ∧ x ∈ ws := by
  unfold Φ at hx
  split_ifs at hx with h
  · rw [Finset.mem_union, List.mem_toFinset] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr ⟨_, Classical.choose_spec h, hx⟩
  · exact Or.inl hx

/-- A vertex actuated in some complete boundary routing lies in `Φ S`: all
complete routings actuate the same vertices (abelian property (b)). -/
theorem mem_Φ_of_mem_complete (hAb : External.Abelian G) [Infinite V] (hG : G.Connected)
    (S : Finset V) (hS : S.Nonempty) (ρ : Config G) (ws : List V)
    (hws : IsComplete π S (boundaryInit S ρ) ws) (x : V) (hx : x ∈ ws) : x ∈ Φ π ρ S := by
  have hT : Terminates π S ρ := ⟨ws, hws⟩
  rw [Φ_of_terminates π ρ S hT, Finset.mem_union, List.mem_toFinset]
  right
  have hc := Classical.choose_spec hT
  have := ((hAb π inferInstance hG S hS _ ws (Classical.choose hT) hws.1 hc.1).2 hws.2 hc.2).2.2 x
  rw [← List.count_pos_iff] at hx ⊢
  omega

/-- `prop:monotonicity`. -/
theorem Φ_mono (hAb : External.Abelian G) [Infinite V] [G.LocallyFinite] (hG : G.Connected)
    (ρ : Config G) (S U : Finset V) (hS : S.Nonempty) (hSU : S ⊆ U)
    (hTU : Terminates π U ρ) : Φ π ρ S ⊆ Φ π ρ U := by
  intro x hx
  rcases mem_Φ_imp π ρ S x hx with hxS | ⟨vs, hvs, hxvs⟩
  · exact subset_Φ π ρ U (hSU hxS)
  · by_cases hxU : x ∈ U
    · exact subset_Φ π ρ U hxU
    · have hleg' := isLegal_filter π S U hSU ρ vs hvs.1
      obtain ⟨ws, hws⟩ := hTU
      have hU : U.Nonempty := hS.mono hSU
      have hcnt := ((hAb π inferInstance hG U hU _ ws _ hws.1 hleg').1 hws.2).2 x
      have hxin : x ∈ vs.filter (fun v => decide (v ∉ U)) :=
        List.mem_filter.2 ⟨hxvs, by simpa using hxU⟩
      have : x ∈ ws := by
        rw [← List.count_pos_iff] at hxin ⊢
        omega
      exact mem_Φ_of_mem_complete π hAb hG U hU ρ ws hws x this

end Rotor
