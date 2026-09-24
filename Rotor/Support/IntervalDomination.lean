import Rotor.Support.BondFinite
import Rotor.Support.HistoryProb
import Rotor.Support.DualGuards

/-!
Proposition 5.1 (`prop:square-passage`), part 3: the sequential domination of an interval of
nonforced tests by Bernoulli(1/2) percolation (`rotor.tex:2180-2195`, Step 1).  The potential
`intPot` is the conditional probability of the constrained crossing given the outcomes of the
interval; each nonforced test opens with probability at most `1/2`, so the expected potential
does not increase, and at a witness (a pattern-free path of edges tested open in the interval,
from the root to the sphere) the potential is `1`.
-/

open Finset MeasureTheory ENNReal Classical

namespace Rotor

/-! ### The tests of an interval -/

theorem tested_replay_append_nil (f d : Site) (h : List Bool) (hs : (replay f d h).active = [])
    (o : Bool) : (replay f d (h ++ [o])).tested = (replay f d h).tested := by
  rw [replay_append, explStepWith_nil hs]

theorem tested_replay_append_cons (f d : Site) (h : List Bool) {e : Site × Site}
    {rest : List (Site × Site)} (he : (replay f d h).active = e :: rest) (o : Bool) :
    (replay f d (h ++ [o])).tested = (replay f d h).tested ++ [(e.1, e.2, o)] := by
  rw [replay_append, explStepWith_cons he]

theorem tested_prefix_replay (f d : Site) {h₀ h' : List Bool} (hp : h₀ <+: h') :
    (replay f d h₀).tested <+: (replay f d h').tested := by
  obtain ⟨t, rfl⟩ := hp
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t o ih =>
    rw [← List.append_assoc]
    refine ih.trans ?_
    rcases hs : (replay f d (h₀ ++ t)).active with _ | ⟨e, rest⟩
    · rw [tested_replay_append_nil f d _ hs]
    · rw [tested_replay_append_cons f d _ hs]
      exact List.prefix_append _ _

/-- The tests recorded after the history `h₀`. -/
noncomputable def intervalTests (f d : Site) (h₀ h' : List Bool) : List (Site × Site × Bool) :=
  (replay f d h').tested.drop (replay f d h₀).tested.length

theorem intervalTests_self (f d : Site) (h₀ : List Bool) : intervalTests f d h₀ h₀ = [] := by
  simp [intervalTests]

theorem tested_eq_append_intervalTests (f d : Site) {h₀ h' : List Bool} (hp : h₀ <+: h') :
    (replay f d h').tested = (replay f d h₀).tested ++ intervalTests f d h₀ h' := by
  have := tested_prefix_replay f d hp
  rw [List.prefix_iff_eq_take] at this
  unfold intervalTests
  conv_lhs => rw [← List.take_append_drop (replay f d h₀).tested.length (replay f d h').tested]
  rw [← this]

theorem intervalTests_append_cons (f d : Site) {h₀ h' : List Bool} (hp : h₀ <+: h')
    {e : Site × Site} {rest : List (Site × Site)} (he : (replay f d h').active = e :: rest)
    (o : Bool) : intervalTests f d h₀ (h' ++ [o]) = intervalTests f d h₀ h' ++ [(e.1, e.2, o)] := by
  unfold intervalTests
  rw [tested_replay_append_cons f d h' he o,
    List.drop_append_of_le_length (tested_prefix_replay f d hp).length_le]

theorem intervalTests_append_nil (f d : Site) (h₀ h' : List Bool)
    (hs : (replay f d h').active = []) (o : Bool) :
    intervalTests f d h₀ (h' ++ [o]) = intervalTests f d h₀ h' := by
  unfold intervalTests
  rw [tested_replay_append_nil f d h' hs]

theorem intervalTests_sublist (f d : Site) (h₀ h' : List Bool) :
    List.Sublist (intervalTests f d h₀ h') (replay f d h').tested :=
  List.drop_sublist _ _

/-- The bonds of the interval tests are distinct. -/
theorem intervalTests_nodup (f : Site) {d : Site} (hd : IsUnit d) (h₀ h' : List Bool) :
    ((intervalTests f d h₀ h').map (fun t => bond (t.1, t.2.1))).Nodup :=
  (explInv_replay f hd h').tested_nodup.sublist ((intervalTests_sublist f d h₀ h').map _)

/-- The configurations with the interval's outcomes. -/
def intervalCyl (f d : Site) (h₀ h' : List Bool) : Set BondConfig :=
  {ω | ∀ t ∈ intervalTests f d h₀ h', ω (bond (t.1, t.2.1)) = t.2.2}

theorem intervalCyl_self (f d : Site) (h₀ : List Bool) : intervalCyl f d h₀ h₀ = Set.univ := by
  ext ω; simp [intervalCyl, intervalTests_self]

theorem intervalCyl_append_cons (f d : Site) {h₀ h' : List Bool} (hp : h₀ <+: h')
    {e : Site × Site} {rest : List (Site × Site)} (he : (replay f d h').active = e :: rest)
    (o : Bool) : intervalCyl f d h₀ (h' ++ [o]) =
      intervalCyl f d h₀ h' ∩ {ω | ω (bond (e.1, e.2)) = o} := by
  ext ω
  simp only [intervalCyl, intervalTests_append_cons f d hp he o, List.mem_append,
    List.mem_singleton, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun t ht => h t (Or.inl ht), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ t (ht | rfl)
    · exact h1 t ht
    · exact h2

theorem measurableSet_intervalCyl (f d : Site) (h₀ h' : List Bool) :
    MeasurableSet (intervalCyl f d h₀ h') := by
  have : intervalCyl f d h₀ h' = ⋂ t ∈ {t | t ∈ intervalTests f d h₀ h'},
      (fun ω : BondConfig => ω (bond (t.1, t.2.1))) ⁻¹' {t.2.2} := by
    ext ω; simp [intervalCyl]
  rw [this]
  exact MeasurableSet.biInter (List.finite_toSet _).countable
    (fun t _ => measurable_pi_apply _ MeasurableSet.of_discrete)

theorem find?_of_nodup_map {α β : Type*} [DecidableEq β] {g : α → β} :
    ∀ {l : List α}, (l.map g).Nodup → ∀ {t : α}, t ∈ l →
      l.find? (fun t' => decide (g t' = g t)) = some t
  | [], _, t, ht => by simp at ht
  | a :: l, hnd, t, ht => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hgt : g a = g t
    · have : a = t := by
        rcases List.mem_cons.1 ht with rfl | ht'
        · rfl
        · exact absurd (hgt ▸ List.mem_map_of_mem ht') hnd.1
      subst this
      rw [List.find?_cons_of_pos (by simp)]
    · rw [List.find?_cons_of_neg (by simpa using hgt)]
      rcases List.mem_cons.1 ht with rfl | ht'
      · exact absurd rfl hgt
      · exact find?_of_nodup_map hnd.2 ht'

/-- The outcome recorded for the bond `b` in the tests `L` (closed if untested). -/
def outcomeOf (L : List (Site × Site × Bool)) (b : Sym2 Site) : Bool :=
  match L.find? (fun t => decide (bond (t.1, t.2.1) = b)) with
  | some t => t.2.2
  | none => false

theorem outcomeOf_mem {L : List (Site × Site × Bool)}
    (hnd : (L.map (fun t => bond (t.1, t.2.1))).Nodup) {t : Site × Site × Bool} (ht : t ∈ L) :
    outcomeOf L (bond (t.1, t.2.1)) = t.2.2 := by
  unfold outcomeOf
  rw [find?_of_nodup_map hnd ht]

theorem intervalCyl_eq_cylBonds (f : Site) {d : Site} (hd : IsUnit d) (h₀ h' : List Bool) :
    intervalCyl f d h₀ h' =
      cylBonds ((intervalTests f d h₀ h').map (fun t => bond (t.1, t.2.1))).toFinset
        (outcomeOf (intervalTests f d h₀ h')) := by
  have hnd := intervalTests_nodup f hd h₀ h'
  ext ω
  simp only [intervalCyl, cylBonds, Set.mem_setOf_eq, List.mem_toFinset, List.mem_map]
  constructor
  · rintro h b ⟨t, ht, rfl⟩
    rw [h t ht, outcomeOf_mem hnd ht]
  · intro h t ht
    rw [h _ ⟨t, ht, rfl⟩, outcomeOf_mem hnd ht]

theorem bondLaw_half_intervalCyl (f : Site) {d : Site} (hd : IsUnit d) (h₀ h' : List Bool) :
    bondLaw (1 / 2) half_le_one (intervalCyl f d h₀ h') =
      (1 / 2 : ℝ≥0∞) ^ (intervalTests f d h₀ h').length := by
  rw [intervalCyl_eq_cylBonds f hd, bondLaw_half_cyl,
    List.toFinset_card_of_nodup (intervalTests_nodup f hd h₀ h'), List.length_map]

/-! ### The potential -/

/-- The conditional probability of `A` given the interval's outcomes. -/
noncomputable def intPot (f d : Site) (h₀ : List Bool) (A : Set BondConfig) (h' : List Bool) : ℝ≥0∞ :=
  bondLaw (1 / 2) half_le_one (A ∩ intervalCyl f d h₀ h') * 2 ^ (intervalTests f d h₀ h').length

theorem intPot_self (f d : Site) (h₀ : List Bool) (A : Set BondConfig) :
    intPot f d h₀ A h₀ = bondLaw (1 / 2) half_le_one A := by
  simp [intPot, intervalCyl_self, intervalTests_self]

theorem intPot_of_subset (f : Site) {d : Site} (hd : IsUnit d) (h₀ : List Bool) {A : Set BondConfig}
    {h' : List Bool} (hsub : intervalCyl f d h₀ h' ⊆ A) : intPot f d h₀ A h' = 1 := by
  unfold intPot
  rw [Set.inter_eq_right.2 hsub, bondLaw_half_intervalCyl f hd, one_div, ← ENNReal.inv_pow,
    ENNReal.inv_mul_cancel (pow_ne_zero _ (by norm_num)) (ENNReal.pow_ne_top (by norm_num))]

/-- Increasing events. -/
def IncreasingEvent (A : Set BondConfig) : Prop :=
  ∀ ω ω' : BondConfig, (∀ b, ω b = true → ω' b = true) → ω ∈ A → ω' ∈ A

theorem bond_new_of_active (f : Site) {d : Site} (hd : IsUnit d) (h' : List Bool) {e : Site × Site}
    {rest : List (Site × Site)} (he : (replay f d h').active = e :: rest) :
    ∀ t ∈ (replay f d h').tested, bond (t.1, t.2.1) ≠ bond (e.1, e.2) := fun t ht h =>
  (explInv_replay f hd h').active_tested e (by rw [he]; exact List.mem_cons_self) t ht h.symm

/-- One nonforced test does not increase the expected potential. -/
theorem intPot_step (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d)) (F₀ : Finset (Sym2 Site))
    {A : Set BondConfig} (hA : BondDetermined F₀ A) (hinc : IncreasingEvent A)
    {h₀ h' : List Bool} (hp : h₀ <+: h') {e : Site × Site} {rest : List (Site × Site)}
    (he : (replay f d h').active = e :: rest)
    (hW : ¬ TestedAs (replay f d h').tested (sideW e.1 e.2) false) :
    2 * (Pm f d (h' ++ [true]) * intPot f d h₀ A (h' ++ [true]) +
      Pm f d (h' ++ [false]) * intPot f d h₀ A (h' ++ [false])) ≤
    2 * (Pm f d h' * intPot f d h₀ A h') := by
  have hdu : IsUnit d := by have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this
  obtain ⟨e₁, e₂⟩ := e
  dsimp only at hW
  have hnew : ∀ t ∈ intervalTests f d h₀ h', bond (t.1, t.2.1) ≠ bond (e₁, e₂) :=
    fun t ht => bond_new_of_active f hdu h' he t ((intervalTests_sublist f d h₀ h').subset ht)
  -- the cylinders
  have hCt := intervalCyl_append_cons f d hp he true
  have hCf := intervalCyl_append_cons f d hp he false
  have hLt := intervalTests_append_cons f d hp he true
  have hLf := intervalTests_append_cons f d hp he false
  have hsplit : A ∩ intervalCyl f d h₀ h' =
      (A ∩ intervalCyl f d h₀ (h' ++ [true])) ∪ (A ∩ intervalCyl f d h₀ (h' ++ [false])) := by
    rw [hCt, hCf, ← Set.inter_union_distrib_left, ← Set.inter_union_distrib_left]
    congr 1
    refine (Set.inter_eq_left.2 ?_).symm
    intro ω _
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases ω (bond (e₁, e₂)) with _ | _ <;> simp
  have hdisj : Disjoint (A ∩ intervalCyl f d h₀ (h' ++ [true]))
      (A ∩ intervalCyl f d h₀ (h' ++ [false])) := by
    rw [hCt, hCf, Set.disjoint_left]
    rintro ω ⟨-, -, h1⟩ ⟨-, -, h2⟩
    simp only [Set.mem_setOf_eq] at h1 h2
    rw [h1] at h2; exact Bool.noConfusion h2
  have hmeasA := measurableSet_of_determined F₀ hA
  have hmu : bondLaw (1 / 2) half_le_one (A ∩ intervalCyl f d h₀ h') =
      bondLaw (1 / 2) half_le_one (A ∩ intervalCyl f d h₀ (h' ++ [true])) +
      bondLaw (1 / 2) half_le_one (A ∩ intervalCyl f d h₀ (h' ++ [false])) := by
    rw [hsplit, measure_union hdisj (hmeasA.inter (measurableSet_intervalCyl f d h₀ _))]
  -- the potentials
  have hpot : intPot f d h₀ A (h' ++ [true]) + intPot f d h₀ A (h' ++ [false]) =
      2 * intPot f d h₀ A h' := by
    unfold intPot
    rw [hLt, hLf]
    simp only [List.length_append, List.length_singleton]
    rw [pow_succ, hmu]
    ring
  -- monotonicity in the new bond
  have hmono : bondLaw (1 / 2) half_le_one (A ∩ intervalCyl f d h₀ (h' ++ [false])) ≤
      bondLaw (1 / 2) half_le_one (A ∩ intervalCyl f d h₀ (h' ++ [true])) := by
    set F := (F₀ ∪ ((intervalTests f d h₀ h').map (fun t => bond (t.1, t.2.1))).toFinset) ∪
      {bond (e₁, e₂)} with hF
    have hbF : bond (e₁, e₂) ∈ F := Finset.mem_union.2 (Or.inr (Finset.mem_singleton.2 rfl))
    have hdet : ∀ o, BondDetermined F (A ∩ intervalCyl f d h₀ (h' ++ [o])) := by
      intro o ω ω' hωω'
      have hA' := hA ω ω' (fun c hc => hωω' c (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hc)))))
      have hC : ω ∈ intervalCyl f d h₀ (h' ++ [o]) ↔ ω' ∈ intervalCyl f d h₀ (h' ++ [o]) := by
        simp only [intervalCyl, intervalTests_append_cons f d hp he o, List.mem_append,
          List.mem_singleton, Set.mem_setOf_eq]
        have hc : ∀ t ∈ intervalTests f d h₀ h', ω (bond (t.1, t.2.1)) = ω' (bond (t.1, t.2.1)) :=
          fun t ht => hωω' _ (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr
            (List.mem_toFinset.2 (List.mem_map.2 ⟨t, ht, rfl⟩))))))
        have hcb : ω (bond (e₁, e₂)) = ω' (bond (e₁, e₂)) := hωω' _ hbF
        constructor
        · rintro h t (ht | rfl)
          · rw [← hc t ht]; exact h t (Or.inl ht)
          · rw [← hcb]; exact h _ (Or.inr rfl)
        · rintro h t (ht | rfl)
          · rw [hc t ht]; exact h t (Or.inl ht)
          · rw [hcb]; exact h _ (Or.inr rfl)
      simp only [Set.mem_inter_iff]
      rw [hA', hC]
    refine bondLaw_half_le_of_flip F (hdet false) (hdet true) hbF ?_ ?_
    · rintro ω ⟨-, hω⟩
      rw [hCf] at hω
      exact hω.2
    · rintro ω ⟨hωA, hω⟩
      rw [hCf] at hω
      rw [hCt]
      refine ⟨hinc ω _ (fun c hc => ?_) hωA, fun t ht => ?_, ?_⟩
      · by_cases hcb : c = bond (e₁, e₂)
        · subst hcb; simp
        · rw [Function.update_of_ne hcb]; exact hc
      · rw [Function.update_of_ne (hnew t ht)]; exact hω.1 t ht
      · show Function.update ω (bond (e₁, e₂)) true (bond (e₁, e₂)) = true
        simp
  -- the probabilities of the two outcomes
  have hPm := Pm_split f hdu h' he
  have hPf := Pm_nonforced f d hd h' he hW
  have hPle : Pm f d (h' ++ [true]) ≤ Pm f d (h' ++ [false]) := by
    have : Pm f d (h' ++ [true]) + Pm f d (h' ++ [false]) ≤
        Pm f d (h' ++ [false]) + Pm f d (h' ++ [false]) := by
      rw [hPm, ← two_mul]; exact hPf
    exact ENNReal.le_of_add_le_add_right (Pm_ne_top f d _) this
  have hpotle : intPot f d h₀ A (h' ++ [false]) ≤ intPot f d h₀ A (h' ++ [true]) := by
    unfold intPot
    rw [hLt, hLf]
    simp only [List.length_append, List.length_singleton]
    gcongr
  -- the algebra
  have key : 2 * (Pm f d h' * intPot f d h₀ A h') =
      (Pm f d (h' ++ [true]) + Pm f d (h' ++ [false])) *
        (intPot f d h₀ A (h' ++ [true]) + intPot f d h₀ A (h' ++ [false])) := by
    rw [mul_left_comm, hpot, hPm]
  rw [key]
  obtain ⟨δ, hδ⟩ := exists_add_of_le hPle
  obtain ⟨γ, hγ⟩ := exists_add_of_le hpotle
  rw [hδ, hγ]
  set a := Pm f d (h' ++ [true])
  set y := intPot f d h₀ A (h' ++ [false])
  have : (a + (a + δ)) * ((y + γ) + y) = 2 * (a * (y + γ) + (a + δ) * y) + δ * γ := by ring
  rw [this]
  exact le_self_add

/-! ### Interval histories -/

/-- `h'` extends `h₀` by nonforced tests only. -/
def IntervalHist (f d : Site) (h₀ h' : List Bool) : Prop :=
  h₀ <+: h' ∧ ∀ i, h₀.length ≤ i → i < h'.length →
    ∀ (e : Site × Site) (rest : List (Site × Site)), (replay f d (h'.take i)).active = e :: rest →
      ¬ TestedAs (replay f d (h'.take i)).tested (sideW e.1 e.2) false

theorem intervalHist_self (f d : Site) (h₀ : List Bool) : IntervalHist f d h₀ h₀ :=
  ⟨List.prefix_refl _, fun _ h1 h2 => by omega⟩

theorem intervalHist_of_prefix {f d : Site} {h₀ h' h'' : List Bool} (h : IntervalHist f d h₀ h')
    (hp : h₀ <+: h'') (hp' : h'' <+: h') : IntervalHist f d h₀ h'' := by
  refine ⟨hp, fun i h1 h2 e rest he => ?_⟩
  have htake : h'.take i = h''.take i := by
    rw [List.prefix_iff_eq_take] at hp'
    rw [hp', List.take_take, min_eq_left h2.le]
  rw [← htake] at he ⊢
  exact h.2 i h1 (by have := hp'.length_le; omega) e rest he

theorem intervalHist_dropLast {f d : Site} {h₀ h' : List Bool} (h : IntervalHist f d h₀ h')
    (hlt : h₀.length < h'.length) :
    IntervalHist f d h₀ h'.dropLast ∧
    ∀ (e : Site × Site) (rest : List (Site × Site)), (replay f d h'.dropLast).active = e :: rest →
      ¬ TestedAs (replay f d h'.dropLast).tested (sideW e.1 e.2) false := by
  have hd' : h'.dropLast = h'.take (h'.length - 1) := List.dropLast_eq_take
  have hlen : h'.dropLast.length = h'.length - 1 := by rw [hd', List.length_take]; omega
  refine ⟨intervalHist_of_prefix h ?_ (List.dropLast_prefix _), ?_⟩
  · exact List.prefix_of_prefix_length_le h.1 (List.dropLast_prefix _) (by omega)
  · intro e rest he
    rw [hd'] at he ⊢
    exact h.2 (h'.length - 1) (by omega) (by omega) e rest he

/-- The expected potential of the two children is at most that of the parent. -/
theorem intPot_children_le (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d))
    (F₀ : Finset (Sym2 Site)) {A : Set BondConfig} (hA : BondDetermined F₀ A)
    (hinc : IncreasingEvent A) {h₀ p : List Bool} (hI : IntervalHist f d h₀ p)
    (hnf : ∀ (e : Site × Site) (rest : List (Site × Site)), (replay f d p).active = e :: rest →
      ¬ TestedAs (replay f d p).tested (sideW e.1 e.2) false) :
    Pm f d (p ++ [true]) * intPot f d h₀ A (p ++ [true]) +
      Pm f d (p ++ [false]) * intPot f d h₀ A (p ++ [false]) ≤ Pm f d p * intPot f d h₀ A p := by
  rcases he : (replay f d p).active with _ | ⟨e, rest⟩
  · rw [Pm_stuck f d p he true, Pm_stuck f d p he false]
    simp
  · have := intPot_step f hd F₀ hA hinc hI.1 he (hnf e rest he)
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 this

/-- The supermartingale bound over a prefix-free family of interval histories. -/
theorem intPot_sum_le (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d))
    (F₀ : Finset (Sym2 Site)) {A : Set BondConfig} (hA : BondDetermined F₀ A)
    (hinc : IncreasingEvent A) (h₀ : List Bool) :
    ∀ (n : ℕ) (S : Finset (List Bool)),
      (∀ h' ∈ S, IntervalHist f d h₀ h' ∧ h'.length ≤ h₀.length + n) →
      (∀ h' ∈ S, ∀ h'' ∈ S, h' <+: h'' → h' = h'') →
      ∑ h' ∈ S, Pm f d h' * intPot f d h₀ A h' ≤ Pm f d h₀ * intPot f d h₀ A h₀
  | 0, S, hS, _ => by
    have hall : ∀ h' ∈ S, h' = h₀ := fun h' hh' =>
      ((hS h' hh').1.1.eq_of_length (by
        have := (hS h' hh').2; have := (hS h' hh').1.1.length_le; omega)).symm
    calc ∑ h' ∈ S, Pm f d h' * intPot f d h₀ A h'
        ≤ ∑ h' ∈ {h₀}, Pm f d h' * intPot f d h₀ A h' :=
          Finset.sum_le_sum_of_subset (fun h' hh' => by
            rw [Finset.mem_singleton]; exact hall h' hh')
      _ = _ := Finset.sum_singleton _ _
  | n + 1, S, hS, hpf => by
    classical
    set L := h₀.length + n + 1 with hL
    set Stop := S.filter (fun h' => h'.length = L) with hStop
    set Srest := S.filter (fun h' => ¬ h'.length = L) with hSrest
    set P := Stop.image List.dropLast with hP
    have hsplit : S = Srest ∪ Stop := by
      rw [hSrest, hStop, Finset.union_comm, Finset.filter_union_filter_not_eq]
    have hdisj : Disjoint Srest Stop := by
      rw [hSrest, hStop]; exact (Finset.disjoint_filter_filter_not S S _).symm
    have hStop_mem : ∀ x ∈ Stop, x ∈ S ∧ x.length = L := fun x hx => Finset.mem_filter.1 hx
    have hSrest_mem : ∀ x ∈ Srest, x ∈ S ∧ x.length ≤ h₀.length + n := fun x hx => by
      have h1 := Finset.mem_filter.1 hx
      have h2 := (hS x h1.1).2
      exact ⟨h1.1, by omega⟩
    have hP_mem : ∀ p ∈ P, ∃ x ∈ Stop, p = x.dropLast := fun p hp => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp; exact ⟨x, hx, rfl⟩
    have hP_len : ∀ p ∈ P, p.length = h₀.length + n := fun p hp => by
      obtain ⟨x, hx, rfl⟩ := hP_mem p hp
      rw [List.length_dropLast, (hStop_mem x hx).2]; omega
    have hP_int : ∀ p ∈ P, IntervalHist f d h₀ p ∧
        ∀ (e : Site × Site) (rest : List (Site × Site)), (replay f d p).active = e :: rest →
          ¬ TestedAs (replay f d p).tested (sideW e.1 e.2) false := fun p hp => by
      obtain ⟨x, hx, rfl⟩ := hP_mem p hp
      exact intervalHist_dropLast (hS x (hStop_mem x hx).1).1 (by rw [(hStop_mem x hx).2]; omega)
    have htop : ∑ x ∈ Stop, Pm f d x * intPot f d h₀ A x ≤
        ∑ p ∈ P, Pm f d p * intPot f d h₀ A p := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := Stop) (t := P) (g := List.dropLast)
        (fun x hx => Finset.mem_image_of_mem _ hx)]
      refine Finset.sum_le_sum (fun p hp => ?_)
      obtain ⟨hI', hnf⟩ := hP_int p hp
      calc ∑ y ∈ Stop.filter (fun y => y.dropLast = p), Pm f d y * intPot f d h₀ A y
          ≤ ∑ y ∈ {p ++ [true], p ++ [false]}, Pm f d y * intPot f d h₀ A y := by
            refine Finset.sum_le_sum_of_subset (fun y hy => ?_)
            obtain ⟨hyS, hyp⟩ := Finset.mem_filter.1 hy
            have hne : y ≠ [] := by
              intro h
              rw [h] at hyS
              have := (hStop_mem [] hyS).2
              simp [hL] at this
            have hy' := List.dropLast_append_getLast hne
            rw [hyp] at hy'
            rw [Finset.mem_insert, Finset.mem_singleton, ← hy']
            rcases hb : y.getLast hne with _ | _ <;> simp
        _ = Pm f d (p ++ [true]) * intPot f d h₀ A (p ++ [true]) +
            Pm f d (p ++ [false]) * intPot f d h₀ A (p ++ [false]) :=
            Finset.sum_pair (by simp)
        _ ≤ Pm f d p * intPot f d h₀ A p := intPot_children_le f hd F₀ hA hinc hI' hnf
    have hdisj' : Disjoint Srest P := by
      rw [Finset.disjoint_left]
      intro p hpr hpP
      obtain ⟨x, hx, rfl⟩ := hP_mem p hpP
      have hxS := (hStop_mem x hx).1
      have hpS := (hSrest_mem _ hpr).1
      have := hpf _ hpS x hxS (List.dropLast_prefix x)
      have hlen := congrArg List.length this
      rw [List.length_dropLast, (hStop_mem x hx).2] at hlen
      omega
    have hpf' : ∀ h' ∈ Srest ∪ P, ∀ h'' ∈ Srest ∪ P, h' <+: h'' → h' = h'' := by
      intro u hu v hv huv
      rcases Finset.mem_union.1 hu with hu | hu <;> rcases Finset.mem_union.1 hv with hv | hv
      · exact hpf u (hSrest_mem u hu).1 v (hSrest_mem v hv).1 huv
      · obtain ⟨x, hx, rfl⟩ := hP_mem v hv
        have := hpf u (hSrest_mem u hu).1 x (hStop_mem x hx).1 (huv.trans (List.dropLast_prefix x))
        subst this
        exfalso
        have h1 := (hSrest_mem _ hu).2
        have h2 := (hStop_mem _ hx).2
        omega
      · exact huv.eq_of_length (by
          have := hP_len u hu; have := (hSrest_mem v hv).2; have := huv.length_le; omega)
      · exact huv.eq_of_length (by rw [hP_len u hu, hP_len v hv])
    have hS' : ∀ h' ∈ Srest ∪ P, IntervalHist f d h₀ h' ∧ h'.length ≤ h₀.length + n := by
      intro h' hh'
      rcases Finset.mem_union.1 hh' with hh' | hh'
      · exact ⟨(hS h' (hSrest_mem h' hh').1).1, (hSrest_mem h' hh').2⟩
      · exact ⟨(hP_int h' hh').1, (hP_len h' hh').le⟩
    have ih := intPot_sum_le f hd F₀ hA hinc h₀ n (Srest ∪ P) hS' hpf'
    calc ∑ h' ∈ S, Pm f d h' * intPot f d h₀ A h'
        = ∑ h' ∈ Srest, Pm f d h' * intPot f d h₀ A h' +
          ∑ h' ∈ Stop, Pm f d h' * intPot f d h₀ A h' := by
          rw [hsplit, Finset.sum_union hdisj]
      _ ≤ ∑ h' ∈ Srest, Pm f d h' * intPot f d h₀ A h' +
          ∑ p ∈ P, Pm f d p * intPot f d h₀ A p := by gcongr
      _ = ∑ h' ∈ Srest ∪ P, Pm f d h' * intPot f d h₀ A h' := (Finset.sum_union hdisj').symm
      _ ≤ _ := ih

theorem tsum_le_of_forall_finset {ι : Type*} (g : ι → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ s : Finset ι, ∑ i ∈ s, g i ≤ c) : ∑' i, g i ≤ c := by
  rw [ENNReal.tsum_eq_iSup_sum]; exact iSup_le h

/-! ### Witnesses -/

/-- A witness in the interval: a pattern-free path of edges tested open in the interval, from
`r` to the sphere of radius `s` inside the box. -/
def IntervalWit (f d : Site) (h₀ : List Bool) (r : Site) (s : ℕ) (h' : List Bool) : Prop :=
  IntervalHist f d h₀ h' ∧ ∃ l : List Site, IsPath squareGraph l ∧ l.head? = some r ∧
    (∀ y ∈ l, linfDist y r ≤ s) ∧ (∃ y ∈ l.getLast?, linfDist y r = s) ∧ ¬ ContainsPattern l ∧
    l.IsChain (fun a b => (a, b, true) ∈ intervalTests f d h₀ h')

/-- A minimal witness. -/
def MinWit (f d : Site) (h₀ : List Bool) (r : Site) (s : ℕ) (h' : List Bool) : Prop :=
  IntervalWit f d h₀ r s h' ∧
    ∀ h'', h₀ <+: h'' → h'' <+: h' → h'' ≠ h' → ¬ IntervalWit f d h₀ r s h''

theorem minWit_prefix_free {f d : Site} {h₀ : List Bool} {r : Site} {s : ℕ} {h' h'' : List Bool}
    (h1 : MinWit f d h₀ r s h') (h2 : MinWit f d h₀ r s h'') (hp : h' <+: h'') : h' = h'' := by
  by_contra hne
  exact h2.2 h' h1.1.1.1 hp hne h1.1

theorem intervalCyl_subset_of_wit {f d : Site} {h₀ : List Bool} {r : Site} {s : ℕ}
    {h' : List Bool} (hw : IntervalWit f d h₀ r s h') :
    intervalCyl f d h₀ h' ⊆ constrainedCrossing r s := by
  intro ω hω
  obtain ⟨-, l, hl, hhead, hin, hlast, hpat, hchain⟩ := hw
  refine ⟨l, ⟨hl, ?_⟩, hhead, hin, hlast, hpat⟩
  refine hchain.imp (fun {a b} hab => ?_)
  exact hω _ hab

/-! ### The box and its bonds -/

/-- The sites within `ℓ^∞` distance `s` of `r`. -/
noncomputable def boxSites (r : Site) (s : ℕ) : Finset Site :=
  (Finset.Icc (r.1 - s) (r.1 + s)) ×ˢ (Finset.Icc (r.2 - s) (r.2 + s))

theorem mem_boxSites {r : Site} {s : ℕ} {y : Site} : y ∈ boxSites r s ↔ linfDist y r ≤ s := by
  simp only [boxSites, Finset.mem_product, Finset.mem_Icc, linfDist, max_le_iff, abs_le]
  omega

/-- The bonds inside the box. -/
noncomputable def boxBonds (r : Site) (s : ℕ) : Finset (Sym2 Site) :=
  (boxSites r s ×ˢ boxSites r s).image (fun p => s(p.1, p.2))

theorem mem_boxBonds_of {r : Site} {s : ℕ} {a b : Site} (ha : linfDist a r ≤ s)
    (hb : linfDist b r ≤ s) : s(a, b) ∈ boxBonds r s :=
  Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨mem_boxSites.2 ha, mem_boxSites.2 hb⟩, rfl⟩

theorem constrainedCrossing_determined (r : Site) (s : ℕ) :
    BondDetermined (boxBonds r s) (constrainedCrossing r s) := by
  have key : ∀ ω ω' : BondConfig, (∀ b ∈ boxBonds r s, ω b = ω' b) →
      ω ∈ constrainedCrossing r s → ω' ∈ constrainedCrossing r s := by
    rintro ω ω' hωω' ⟨l, ⟨hl, hch⟩, hhead, hin, hlast, hpat⟩
    refine ⟨l, ⟨hl, ?_⟩, hhead, hin, hlast, hpat⟩
    rw [List.isChain_iff_getElem] at hch ⊢
    intro i hi
    have := hch i hi
    rw [← hωω' _ (mem_boxBonds_of (hin _ (List.getElem_mem _)) (hin _ (List.getElem_mem _)))]
    exact this
  intro ω ω' h
  exact ⟨key ω ω' h, key ω' ω (fun b hb => (h b hb).symm)⟩

theorem constrainedCrossing_increasing (r : Site) (s : ℕ) :
    IncreasingEvent (constrainedCrossing r s) := by
  rintro ω ω' hle ⟨l, ⟨hl, hch⟩, hhead, hin, hlast, hpat⟩
  exact ⟨l, ⟨hl, hch.imp (fun {a b} hab => hle _ hab)⟩, hhead, hin, hlast, hpat⟩

/-- The interval domination: the minimal witnesses have total probability at most that of the
constrained crossing under Bernoulli(1/2), times the probability of the interval's start. -/
theorem interval_domination (f : Site) {d : Site} (hd : squareGraph.Adj f (f + d))
    (h₀ : List Bool) (r : Site) (s : ℕ) :
    ∑' h' : {h' // MinWit f d h₀ r s h'}, Pm f d h'.1 ≤
      Pm f d h₀ * bondLaw (1 / 2) half_le_one (constrainedCrossing r s) := by
  have hdu : IsUnit d := by have := isUnit_of_adj hd; rwa [add_sub_cancel_left] at this
  have hA := constrainedCrossing_determined r s
  have hinc := constrainedCrossing_increasing r s
  rw [← intPot_self f d h₀ (constrainedCrossing r s)]
  refine tsum_le_of_forall_finset _ _ (fun S => ?_)
  have hpot1 : ∀ h' ∈ S, intPot f d h₀ (constrainedCrossing r s) h'.1 = 1 := fun h' _ =>
    intPot_of_subset f hdu h₀ (intervalCyl_subset_of_wit h'.2.1)
  set n := S.sup (fun h' => h'.1.length) with hn
  calc ∑ h' ∈ S, Pm f d h'.1
      = ∑ h' ∈ S, Pm f d h'.1 * intPot f d h₀ (constrainedCrossing r s) h'.1 :=
        Finset.sum_congr rfl (fun h' hh' => by rw [hpot1 h' hh', mul_one])
    _ = ∑ h' ∈ S.image Subtype.val, Pm f d h' * intPot f d h₀ (constrainedCrossing r s) h' :=
        (Finset.sum_image (f := fun h' => Pm f d h' * intPot f d h₀ (constrainedCrossing r s) h')
          (fun _ _ _ _ h => Subtype.ext h)).symm
    _ ≤ _ := by
        refine intPot_sum_le f hd _ hA hinc h₀ n (S.image Subtype.val) ?_ ?_
        · intro h' hh'
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh'
          exact ⟨x.2.1.1, le_add_left (Finset.le_sup (f := fun h' => h'.1.length) hx)⟩
        · intro u hu v hv huv
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hv
          exact minWit_prefix_free x.2 y.2 huv

end Rotor
