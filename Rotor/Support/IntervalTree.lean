import Rotor.Support.IntervalDomination
import Rotor.Support.ForcedCascade
import Rotor.Support.PatternFree
import Rotor.Support.ExplCover
import Rotor.Support.FrameSector

/-!
Proposition 5.1 (`prop:square-passage`), part 4: the first-visit tree inside an interval.  After
the start `h₀` of an interval (the initial state, or the state after a forced test of the sole
active edge) every active edge leaves the root `r` or a face first visited in the interval, and
every face first visited in the interval is joined to `r` by a chain of edges tested open in the
interval.  For a realized history the chain is a directed path of open dual edges, hence
pattern-free, and cutting it at the sphere of radius `s` gives a witness; the shortest prefix
carrying a witness is a minimal witness.
-/

open Finset MeasureTheory ENNReal Classical

namespace Rotor

/-! ### The start of an interval -/

/-- `r` is the root of the interval starting at `h₀`: every active edge leaves `r`. -/
def IntervalStart (f d : Site) (h₀ : List Bool) (r : Site) : Prop :=
  r ∈ (replay f d h₀).visited ∧ ∀ e ∈ (replay f d h₀).active, e.1 = r

theorem intervalStart_nil (f d : Site) : IntervalStart f d [] f := by
  refine ⟨by simp [replay, explInit], fun e he => ?_⟩
  simp only [replay, List.foldl_nil, explInit, edgesFrom, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> rfl

theorem intervalStart_forced (f d : Site) (h₁ : List Bool) {t r : Site}
    (he : (replay f d h₁).active = [(t, r)]) : IntervalStart f d (h₁ ++ [true]) r := by
  unfold IntervalStart
  rw [replay_append, explStepWith_cons he]
  refine ⟨by simp, fun e he' => ?_⟩
  simp only [if_true, List.append_nil, List.mem_filter, continuations_eq, List.mem_cons,
    List.not_mem_nil, or_false] at he'
  rcases he'.1 with rfl | rfl | rfl <;> rfl

/-! ### The invariant along an interval -/

theorem visited_mono_prefix (f d : Site) {h₀ h' : List Bool} (hp : h₀ <+: h') :
    (replay f d h₀).visited ⊆ (replay f d h').visited := by
  obtain ⟨t, rfl⟩ := hp
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t o ih =>
    rw [← List.append_assoc]
    exact ih.trans (visited_mono_replay f d _ o)

/-- The invariant: active tails are the root or new faces; new faces are joined to the root by
chains of edges tested open in the interval. -/
structure IntInv (f d : Site) (h₀ : List Bool) (r : Site) (h' : List Bool) : Prop where
  hpre : h₀ <+: h'
  tails : ∀ e ∈ (replay f d h').active,
    e.1 = r ∨ (e.1 ∈ (replay f d h').visited ∧ e.1 ∉ (replay f d h₀).visited)
  chains : ∀ g ∈ (replay f d h').visited, g ∉ (replay f d h₀).visited →
    ∃ l : List Site, l.head? = some r ∧ l.getLast? = some g ∧ l.Nodup ∧
      l.IsChain (fun a b => (a, b, true) ∈ intervalTests f d h₀ h') ∧
      (∀ y ∈ l, y ∈ (replay f d h').visited) ∧ (∀ y ∈ l.tail, y ∉ (replay f d h₀).visited)

theorem intInv_self (f d : Site) {h₀ : List Bool} {r : Site} (hs : IntervalStart f d h₀ r) :
    IntInv f d h₀ r h₀ where
  hpre := List.prefix_refl _
  tails := fun e he => Or.inl (hs.2 e he)
  chains := fun _ hg hg0 => absurd hg hg0

theorem intInv_step (f : Site) {d : Site} (hd : IsUnit d) {h₀ : List Bool} {r : Site}
    (hs : IntervalStart f d h₀ r) {h' : List Bool} (hI : IntInv f d h₀ r h') (o : Bool) :
    IntInv f d h₀ r (h' ++ [o]) := by
  have hinv := explInv_replay f hd h'
  have hmono := visited_mono_prefix f d hI.hpre
  have hp' : h₀ <+: h' ++ [o] := hI.hpre.trans (List.prefix_append _ _)
  rcases he : (replay f d h').active with _ | ⟨e, rest⟩
  · -- nothing happens
    have hrep : replay f d (h' ++ [o]) = replay f d h' := by rw [replay_append, explStepWith_nil he]
    refine ⟨hp', ?_, ?_⟩
    · rw [hrep]; exact hI.tails
    · rw [hrep, intervalTests_append_nil f d h₀ h' he]; exact hI.chains
  · obtain ⟨a, g⟩ := e
    have hmem : (a, g) ∈ (replay f d h').active := by rw [he]; exact List.mem_cons_self
    have hgV : g ∉ (replay f d h').visited := hinv.active_head _ hmem
    have hgV0 : g ∉ (replay f d h₀).visited := fun h => hgV (hmono h)
    have hIT := intervalTests_append_cons f d hI.hpre he o
    have hvis : (replay f d (h' ++ [o])).visited =
        if o then insert g (replay f d h').visited else (replay f d h').visited := by
      rw [replay_append, explStepWith_cons he]
    have hact : ∀ e' ∈ (replay f d (h' ++ [o])).active,
        e' ∈ (if o then continuations a g else []) ∨ e' ∈ rest := by
      intro e' he'
      rw [replay_append, explStepWith_cons he] at he'
      simp only [List.mem_filter, List.mem_append] at he'
      exact he'.1
    refine ⟨hp', ?_, ?_⟩
    · intro e' he'
      rcases hact e' he' with h1 | h1
      · rcases o with _ | _
        · simp at h1
        · right
          simp only [continuations_eq, if_true, List.mem_cons, List.not_mem_nil, or_false] at h1
          have : e'.1 = g := by rcases h1 with rfl | rfl | rfl <;> rfl
          rw [this, hvis]
          exact ⟨Finset.mem_insert_self _ _, hgV0⟩
      · rcases hI.tails e' (by rw [he]; exact List.mem_cons_of_mem _ h1) with h2 | ⟨h2, h3⟩
        · exact Or.inl h2
        · right
          refine ⟨?_, h3⟩
          rw [hvis]
          split_ifs
          · exact Finset.mem_insert_of_mem h2
          · exact h2
    · intro g' hg' hg'0
      rw [hvis] at hg'
      by_cases hold : g' ∈ (replay f d h').visited
      · obtain ⟨l, h1, h2, h3, h4, h5, h6⟩ := hI.chains g' hold hg'0
        refine ⟨l, h1, h2, h3, h4.imp (fun {x y} hxy => by rw [hIT]; exact List.mem_append_left _ hxy),
          fun y hy => ?_, h6⟩
        rw [hvis]
        split_ifs
        · exact Finset.mem_insert_of_mem (h5 y hy)
        · exact h5 y hy
      · -- the new face `g`
        rcases o with _ | _
        · exact absurd hg' hold
        simp only [if_true, Finset.mem_insert] at hg'
        rcases hg' with rfl | hg'
        · rcases hI.tails (a, g') hmem with ha | ⟨haV, haV0⟩
          · -- chain `[r, g']`
            simp only at ha
            subst ha
            refine ⟨[a, g'], rfl, rfl, ?_, ?_, ?_, ?_⟩
            · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
                List.nodup_nil, and_true, and_self]
              intro h; subst h; exact hgV (hmono hs.1)
            · rw [List.isChain_cons_cons, hIT]
              exact ⟨List.mem_append_right _ (List.mem_singleton_self _), List.isChain_singleton _⟩
            · intro y hy
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
              rw [hvis]
              rcases hy with rfl | rfl
              · exact Finset.mem_insert_of_mem (hmono hs.1)
              · exact Finset.mem_insert_self _ _
            · intro y hy
              simp only [List.tail_cons, List.mem_singleton] at hy
              subst hy; exact hgV0
          · obtain ⟨l, h1, h2, h3, h4, h5, h6⟩ := hI.chains a haV haV0
            have hne : l ≠ [] := by intro h; rw [h] at h1; simp at h1
            have hgl : g' ∉ l := fun h => hgV (h5 _ h)
            refine ⟨l ++ [g'], ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [List.head?_append_of_ne_nil _ hne]; exact h1
            · rw [List.getLast?_append_of_ne_nil _ (by simp)]; rfl
            · rw [List.nodup_append]
              exact ⟨h3, List.nodup_singleton _, fun y hy z hz => by
                rw [List.mem_singleton] at hz; subst hz; exact fun h => hgl (h ▸ hy)⟩
            · rw [List.isChain_append]
              refine ⟨h4.imp (fun {x y} hxy => by rw [hIT]; exact List.mem_append_left _ hxy),
                List.isChain_singleton _, ?_⟩
              intro x hx y hy
              rw [h2] at hx
              simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
              subst hx; subst hy
              rw [hIT]
              exact List.mem_append_right _ (List.mem_singleton_self _)
            · intro y hy
              rw [hvis]
              simp only [if_true]
              rw [List.mem_append, List.mem_singleton] at hy
              rcases hy with hy | rfl
              · exact Finset.mem_insert_of_mem (h5 y hy)
              · exact Finset.mem_insert_self _ _
            · intro y hy
              rw [List.tail_append_of_ne_nil hne, List.mem_append, List.mem_singleton] at hy
              rcases hy with hy | rfl
              · exact h6 y hy
              · exact hgV0
        · exact absurd hg' hold

theorem intInv_of_prefix (f : Site) {d : Site} (hd : IsUnit d) {h₀ : List Bool} {r : Site}
    (hs : IntervalStart f d h₀ r) {h' : List Bool} (hp : h₀ <+: h') : IntInv f d h₀ r h' := by
  obtain ⟨t, rfl⟩ := hp
  induction t using List.reverseRecOn with
  | nil => simpa using intInv_self f d hs
  | append_singleton t o ih =>
    rw [← List.append_assoc]
    exact intInv_step f hd hs ih o

/-! ### From a far face to a minimal witness -/

theorem linfDist_adj_le {a b r : Site} (h : squareGraph.Adj a b) :
    linfDist b r ≤ linfDist a r + 1 := by
  have hu := isUnit_of_adj h
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨r1, r2⟩ := r
  rcases hu with h | h | h | h <;> simp only [Prod.mk_sub_mk, Prod.mk.injEq] at h <;>
    simp only [linfDist, abs_eq_max_neg] <;> omega

theorem linfDist_self (r : Site) : linfDist r r = 0 := by
  obtain ⟨r1, r2⟩ := r; simp [linfDist]

theorem isChain_getElem? {α : Type*} {R : α → α → Prop} {l : List α} (h : l.IsChain R) {i : ℕ}
    {a b : α} (ha : l[i]? = some a) (hb : l[i + 1]? = some b) : R a b := by
  rw [List.isChain_iff_getElem] at h
  have hi := (List.getElem?_eq_some_iff.1 hb).1
  have := h i hi
  rw [List.getElem?_eq_getElem (by omega)] at ha
  rw [List.getElem?_eq_getElem hi] at hb
  simp only [Option.some.injEq] at ha hb
  rw [← ha, ← hb]; exact this

/-- Cutting a chain from `r` at the first face at distance `s`. -/
theorem exists_cut {l : List Site} {r : Site} (hhead : l.head? = some r)
    (hch : l.IsChain squareGraph.Adj) {s : ℕ} (hs : 1 ≤ s)
    (hfar : ∃ y ∈ l, (s : ℤ) ≤ linfDist y r) :
    ∃ m, m + 1 ≤ l.length ∧ (∀ y ∈ l.take (m + 1), linfDist y r ≤ s) ∧
      (∃ y ∈ (l.take (m + 1)).getLast?, linfDist y r = s) := by
  classical
  obtain ⟨y, hy, hys⟩ := hfar
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have hex : ∃ i, ∃ y, l[i]? = some y ∧ (s : ℤ) ≤ linfDist y r :=
    ⟨i, l[i], List.getElem?_eq_getElem hi, hys⟩
  obtain ⟨b, hb, hbs⟩ := Nat.find_spec hex
  have hmin : ∀ j y, j < Nat.find hex → l[j]? = some y → linfDist y r < s := by
    intro j y hj hjy
    have := Nat.find_min hex hj
    push Not at this
    exact this y hjy
  generalize hm : Nat.find hex = m at hb hbs hmin
  have hml : m < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have hl0 : l[0]? = some r := by rwa [List.head?_eq_getElem?] at hhead
  have hmpos : 0 < m := by
    by_contra h0
    have h00 : m = 0 := by omega
    subst h00
    rw [hl0] at hb
    simp only [Option.some.injEq] at hb
    subst hb
    rw [linfDist_self] at hbs
    omega
  obtain ⟨a, ha⟩ : ∃ a, l[m - 1]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hprev := hmin (m - 1) a (by omega) ha
  have hadj : squareGraph.Adj a b :=
    isChain_getElem? hch ha (by rw [show m - 1 + 1 = m by omega]; exact hb)
  have hstep := linfDist_adj_le (r := r) hadj
  have hmeq : linfDist b r = s := by omega
  refine ⟨m, by omega, ?_, ?_⟩
  · intro y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [List.getElem_take]
    simp only [List.length_take] at hj
    have hjl : j < l.length := by omega
    rcases Nat.lt_or_ge j m with hjm | hjm
    · exact (hmin j _ hjm (List.getElem?_eq_getElem hjl)).le
    · have hjm' : j = m := by omega
      have hjb : l[j]'hjl = b := by
        have h1 : l[j]? = l[m]? := by rw [hjm']
        rw [hb] at h1
        have h2 := List.getElem?_eq_getElem hjl
        rw [h1] at h2
        simpa using h2.symm
      rw [hjb]; exact hmeq.le
  · refine ⟨b, ?_, hmeq⟩
    rw [List.getLast?_eq_getElem?, List.length_take, min_eq_left (by omega), Nat.add_sub_cancel,
      List.getElem?_take_of_lt (by omega)]
    exact hb

theorem containsPattern_of_take {l : List Site} {n : ℕ} (h : ContainsPattern (l.take n)) :
    ContainsPattern l := by
  obtain ⟨i, z, hP⟩ := h
  refine ⟨i, z, ?_⟩
  have hkey : ∀ P : List Site, P.length = 6 → ((l.take n).drop i).take 6 = P → (l.drop i).take 6 = P := by
    intro P hP6 hPe
    rw [List.drop_take, List.take_take] at hPe
    have hlen := congrArg List.length hPe
    simp only [List.length_take, List.length_drop, hP6] at hlen
    have h6 : min 6 (n - i) = 6 := by omega
    rw [h6] at hPe
    exact hPe
  rcases hP with hP | hP
  · exact Or.inl (hkey _ (by simp [pstar]) hP)
  · exact Or.inr (hkey _ (by simp [pstar]) hP)

/-- A face first visited in the interval at distance at least `s` yields a witness. -/
theorem exists_intervalWit (f : Site) {d : Site} (hd : IsUnit d) {h₀ : List Bool} {r : Site}
    (hs0 : IntervalStart f d h₀ r) {h' : List Bool} (hI : IntervalHist f d h₀ h')
    {ρ : Config squareGraph} (hρ : explore ρ f d h'.length = replay f d h') {g : Site}
    (hg : g ∈ (replay f d h').visited) (hg0 : g ∉ (replay f d h₀).visited) {s : ℕ} (hs : 1 ≤ s)
    (hdist : (s : ℤ) ≤ linfDist g r) : IntervalWit f d h₀ r s h' := by
  have hinv := explInv_replay f hd h'
  have hIn := intInv_of_prefix f hd hs0 hI.1
  obtain ⟨l, h1, h2, h3, h4, -, -⟩ := hIn.chains g hg hg0
  have hsub : ∀ t ∈ intervalTests f d h₀ h', t ∈ (replay f d h').tested :=
    fun t ht => (intervalTests_sublist f d h₀ h').subset ht
  have hadj : l.IsChain squareGraph.Adj := h4.imp (fun {a b} hab => by
    have := hinv.tested_adj _ (hsub _ hab); simpa using this)
  have hcov := (explCov_explore ρ f hd h'.length).outcomes
  rw [hρ] at hcov
  have hopen : l.IsChain (DualOpen ρ) := h4.imp (fun {a b} hab => by
    have := hcov _ (hsub _ hab)
    exact of_decide_eq_true this.symm)
  have hpat : ¬ ContainsPattern l := openDualPath_no_pattern ρ ⟨⟨h3, hadj⟩, hopen⟩
  obtain ⟨m, hm, hin, hlast⟩ := exists_cut h1 hadj hs ⟨g, List.mem_of_mem_getLast? h2, hdist⟩
  refine ⟨hI, l.take (m + 1), ⟨h3.sublist (List.take_sublist _ _), hadj.take _⟩, ?_, hin, hlast,
    fun hc => hpat (containsPattern_of_take hc), h4.take _⟩
  rcases l with _ | ⟨a, l'⟩
  · simp at h1
  · simp only [List.take_succ_cons, List.head?_cons]
    simpa using h1

/-- The shortest witnessing prefix is a minimal witness. -/
theorem exists_minWit (f : Site) {d : Site} (hd : IsUnit d) {h₀ : List Bool} {r : Site}
    (hs0 : IntervalStart f d h₀ r) {h' : List Bool} (hI : IntervalHist f d h₀ h')
    {ρ : Config squareGraph} (hρ : explore ρ f d h'.length = replay f d h') {g : Site}
    (hg : g ∈ (replay f d h').visited) (hg0 : g ∉ (replay f d h₀).visited) {s : ℕ} (hs : 1 ≤ s)
    (hdist : (s : ℤ) ≤ linfDist g r) :
    ∃ h'', h₀ <+: h'' ∧ h'' <+: h' ∧ MinWit f d h₀ r s h'' := by
  classical
  have hw := exists_intervalWit f hd hs0 hI hρ hg hg0 hs hdist
  have hex : ∃ m, h₀.length ≤ m ∧ m ≤ h'.length ∧ IntervalWit f d h₀ r s (h'.take m) :=
    ⟨h'.length, hI.1.length_le, le_rfl, by rw [List.take_length]; exact hw⟩
  set m₀ := Nat.find hex with hm₀
  obtain ⟨hm1, hm2, hwit⟩ := Nat.find_spec hex
  refine ⟨h'.take m₀, ?_, List.take_prefix _ _, hwit, ?_⟩
  · exact List.prefix_of_prefix_length_le hI.1 (List.take_prefix _ _) (by
      rw [List.length_take]; omega)
  · intro h''' hp0 hp hne hw'
    have hlen : h'''.length < m₀ := by
      have := hp.length_le
      rw [List.length_take] at this
      rcases Nat.lt_or_ge h'''.length m₀ with h | h
      · exact h
      · exfalso
        apply hne
        exact hp.eq_of_length (by rw [List.length_take]; omega)
    have hp' : h''' = h'.take h'''.length := by
      have := hp.trans (List.take_prefix m₀ h')
      rwa [List.prefix_iff_eq_take] at this
    have := Nat.find_min hex hlen
    push Not at this
    exact this hp0.length_le (by have := hp.length_le; rw [List.length_take] at this; omega)
      (hp' ▸ hw')

end Rotor

