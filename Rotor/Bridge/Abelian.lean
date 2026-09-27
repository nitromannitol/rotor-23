import Rotor.External.Abelian
import Rotor.Support.RoutingBasics

/-!
# The abelian property of rotor-routing

HLMPPW Lemma 3.9: if a legal routing `vs` of a chip configuration stabilizes a finite set `S`,
every legal routing `ws` of the same configuration is no longer than `vs` and fires each vertex
no more often, and if both stabilize `S` they have the same length, fire every vertex equally
often, and reach the same final state. Proved unconditionally by induction on legal routings; the
least action, exchange and commutation lemmas below build up to that induction.
-/

namespace Rotor.Bridge

open Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- Two single-site actuations at distinct vertices `v` and `w`, each holding a positive number
of chips, commute: actuating `v` then `w` gives the same result as actuating `w` then `v`. -/
theorem actuate_comm (π : Mechanism G) (S : Finset V) (ξ : RState G)
    (v w : V) (hvw : v ≠ w) (hv : 0 < ξ.σ v) (hw : 0 < ξ.σ w) :
    actuate π S (actuate π S ξ v) w = actuate π S (actuate π S ξ w) v := by
  have hsigma :
      (actuate π S (actuate π S ξ v) w).σ =
        (actuate π S (actuate π S ξ w) v).σ := by
    funext x
    by_cases hxv : x = v
    · subst x
      rw [actuate_σ π S (actuate π S ξ v) w v,
        actuate_σ π S (actuate π S ξ w) v v,
        actuate_σ π S ξ v v, actuate_σ π S ξ w v,
        actuate_ρ_of_ne π S ξ v w (Ne.symm hvw),
        actuate_ρ_of_ne π S ξ w v hvw]
      simp [hvw]
      omega
    · by_cases hxw : x = w
      · subst x
        rw [actuate_σ π S (actuate π S ξ v) w w,
          actuate_σ π S (actuate π S ξ w) v w,
          actuate_σ π S ξ v w, actuate_σ π S ξ w w,
          actuate_ρ_of_ne π S ξ v w (Ne.symm hvw),
          actuate_ρ_of_ne π S ξ w v hvw]
        simp [Ne.symm hvw]
        omega
      · rw [actuate_σ π S (actuate π S ξ v) w x,
          actuate_σ π S (actuate π S ξ w) v x,
          actuate_σ π S ξ v x, actuate_σ π S ξ w x,
          actuate_ρ_of_ne π S ξ v w (Ne.symm hvw),
          actuate_ρ_of_ne π S ξ w v hvw]
        simp [hxv, hxw]
        omega
  have hrho :
      (actuate π S (actuate π S ξ v) w).ρ =
        (actuate π S (actuate π S ξ w) v).ρ := by
    funext x
    by_cases hxv : x = v
    · subst x
      rw [actuate_ρ_of_ne π S (actuate π S ξ v) w v hvw,
        actuate_ρ_self, actuate_ρ_self,
        actuate_ρ_of_ne π S ξ w v hvw]
    · by_cases hxw : x = w
      · subst x
        rw [actuate_ρ_self,
          actuate_ρ_of_ne π S ξ v w (Ne.symm hvw),
          actuate_ρ_of_ne π S (actuate π S ξ w) v w (Ne.symm hvw),
          actuate_ρ_self]
      · rw [actuate_ρ_of_ne π S (actuate π S ξ v) w x hxw,
          actuate_ρ_of_ne π S ξ v x hxv,
          actuate_ρ_of_ne π S (actuate π S ξ w) v x hxv,
          actuate_ρ_of_ne π S ξ w x hxw]
  cases hleft : actuate π S (actuate π S ξ v) w with
  | mk σ₁ ρ₁ =>
    cases hright : actuate π S (actuate π S ξ w) v with
    | mk σ₂ ρ₂ =>
      have hsigma' : σ₁ = σ₂ := by
        simpa only [hleft, hright] using hsigma
      have hrho' : ρ₁ = ρ₂ := by
        simpa only [hleft, hright] using hrho
      rw [RState.mk.injEq]
      exact ⟨hsigma', hrho'⟩

omit [G.LocallyFinite] in
/-- Running a legal routing list `l` that never mentions `w` cannot decrease a positive chip
count at `w`. -/
theorem run_pos_of_not_mem (π : Mechanism G) (S : Finset V) (ξ : RState G)
    (l : List V) (w : V) (hw : 0 < ξ.σ w) (hnot : w ∉ l)
    (hl : IsLegal π S ξ l) :
    0 < (run π S ξ l).σ w := by
  induction l generalizing ξ with
  | nil => simpa using hw
  | cons v l ih =>
    rw [isLegal_cons] at hl
    obtain ⟨hvS, hv, hl⟩ := hl
    have hwv : w ≠ v := by
      intro h
      apply hnot
      simp [h]
    have hstep : 0 < (actuate π S ξ v).σ w := by
      rw [actuate_σ]
      simp only [if_false, hwv]
      omega
    apply ih (actuate π S ξ v) hstep
    · intro hwl
      exact hnot (by simp [hwv, hwl])
    · exact hl

/-- Every element of a list occurs as the head of a split at its first occurrence: if `w ∈ l`
then `l = p ++ w :: q` for some `p` not containing `w`. -/
theorem exists_append_cons_not_mem_of_mem (l : List V) (w : V) (hw : w ∈ l) :
    ∃ p q, l = p ++ w :: q ∧ w ∉ p := by
  induction l with
  | nil => simp at hw
  | cons v l ih =>
    by_cases hvw : v = w
    · subst v
      exact ⟨[], l, rfl, by simp⟩
    · by_cases hw' : w ∈ l
      · obtain ⟨p, q, h, hp⟩ := ih hw'
        refine ⟨v :: p, q, ?_, ?_⟩
        · simp [h]
        · intro hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · exact hvw hmem.symm
          · exact hp hmem
      · simp at hw
        rcases hw with hmem | hmem
        · exact False.elim (hvw hmem.symm)
        · exact False.elim (hw' hmem)

omit [G.LocallyFinite] in
/-- A vertex `w` that is legal to fire and does not occur in `l` can be moved to the front of the
routing list `l ++ w :: r` without changing legality or the resulting state. -/
theorem isLegal_cons_run_eq_of_not_mem (π : Mechanism G) (S : Finset V) (ξ : RState G)
    (l : List V) (w : V) (r : List V) (hwS : w ∉ S) (hw : 0 < ξ.σ w)
    (hnot : w ∉ l) (hleg : IsLegal π S ξ (l ++ w :: r)) :
    IsLegal π S ξ (w :: l ++ r) ∧
      run π S ξ (w :: l ++ r) = run π S ξ (l ++ w :: r) := by
  induction l generalizing ξ with
  | nil =>
    constructor
    · simpa using hleg
    · rfl
  | cons v l ih =>
    change IsLegal π S ξ (v :: (l ++ w :: r)) at hleg
    change IsLegal π S ξ (w :: (v :: l ++ r)) ∧
      run π S ξ (w :: (v :: l ++ r)) = run π S ξ (v :: (l ++ w :: r))
    obtain ⟨hvS, hv, hleg⟩ := hleg
    have hwv : w ≠ v := by
      intro h
      apply hnot
      simp [h]
    have hw' : 0 < (actuate π S ξ v).σ w := by
      rw [actuate_σ]
      simp only [if_false, hwv]
      omega
    have hnot' : w ∉ l := by
      intro hwl
      exact hnot (by simp [hwv, hwl])
    obtain ⟨hleg', heq'⟩ := ih (actuate π S ξ v) hw' hnot' hleg
    have hv' : 0 < (actuate π S ξ w).σ v := by
      rw [actuate_σ]
      simp only [if_false, Ne.symm hwv]
      omega
    have hpair :
        actuate π S (actuate π S ξ w) v = actuate π S (actuate π S ξ v) w :=
      (actuate_comm π S ξ v w (Ne.symm hwv) hv hw).symm
    constructor
    · rw [isLegal_cons]
      refine ⟨hwS, hw, ?_⟩
      change IsLegal π S (actuate π S ξ w) (v :: (l ++ r))
      rw [isLegal_cons]
      refine ⟨hvS, hv', ?_⟩
      obtain ⟨-, -, hleg''⟩ :=
        (isLegal_cons π S (actuate π S ξ v) w (l ++ r)).1 hleg'
      rw [hpair]
      exact hleg''
    · calc
        run π S ξ (w :: (v :: l ++ r)) =
            run π S (actuate π S ξ w) (v :: (l ++ r)) := rfl
        _ = run π S (actuate π S (actuate π S ξ w) v) (l ++ r) := rfl
        _ = run π S (actuate π S (actuate π S ξ v) w) (l ++ r) := by rw [hpair]
        _ = run π S (actuate π S ξ v) (l ++ w :: r) := heq'
        _ = run π S ξ (v :: (l ++ w :: r)) := rfl

omit [G.LocallyFinite] in
/-- Least action principle: if a legal routing `vs` stabilizes `S`, every other legal routing
`ws` of the same configuration is no longer than `vs` and fires each vertex no more often
than `vs` does. -/
theorem length_le_count_le_of_stable (π : Mechanism G) (S : Finset V) (ξ : RState G)
    (vs : List V) (hvs : IsLegal π S ξ vs) (hstable : Stable S (run π S ξ vs))
    (ws : List V) (hws : IsLegal π S ξ ws) :
    ws.length ≤ vs.length ∧ ∀ v, ws.count v ≤ vs.count v := by
  have H : ∀ n : ℕ, ∀ (vs : List V), vs.length = n →
      ∀ (ξ : RState G), IsLegal π S ξ vs → Stable S (run π S ξ vs) →
      ∀ (ws : List V), IsLegal π S ξ ws →
        ws.length ≤ vs.length ∧ ∀ v, ws.count v ≤ vs.count v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro vs hn ξ hvs hstable ws hws
      cases vs with
      | nil =>
        constructor
        · cases ws with
          | nil => simp
          | cons w ws =>
            rw [isLegal_cons] at hws
            obtain ⟨hwS, hw, -⟩ := hws
            have hz := hstable w hwS
            simp at hz
            omega
        · intro x
          cases ws with
          | nil => simp
          | cons w ws =>
            rw [isLegal_cons] at hws
            obtain ⟨hwS, hw, -⟩ := hws
            have hz := hstable w hwS
            simp at hz
            omega
      | cons v vs =>
        cases ws with
        | nil => simp
        | cons w ws =>
          rw [isLegal_cons] at hvs hws
          obtain ⟨hvS, hv, hvs⟩ := hvs
          obtain ⟨hwS, hw, hws⟩ := hws
          have hmem : w ∈ v :: vs := by
            by_contra hmem
            have hpos := run_pos_of_not_mem π S ξ (v :: vs) w hw hmem
              (by rw [isLegal_cons]; exact ⟨hvS, hv, hvs⟩)
            have hz := hstable w hwS
            omega
          obtain ⟨l, r, hsplit, hnot⟩ := exists_append_cons_not_mem_of_mem (v :: vs) w hmem
          have hleg_split : IsLegal π S ξ (l ++ w :: r) := by
            rw [← hsplit]
            exact ⟨hvS, hv, hvs⟩
          have hroute : IsLegal π S ξ (w :: (l ++ r)) ∧
              run π S ξ (w :: (l ++ r)) = run π S ξ (l ++ w :: r) :=
            isLegal_cons_run_eq_of_not_mem π S ξ l w r hwS hw hnot hleg_split
          have htail : IsLegal π S (actuate π S ξ w) (l ++ r) := by
            obtain ⟨-, -, htail⟩ :=
              (isLegal_cons π S ξ w (l ++ r)).1 hroute.1
            exact htail
          have hstable' : Stable S (run π S (actuate π S ξ w) (l ++ r)) := by
            change Stable S (run π S ξ (w :: (l ++ r)))
            rw [hroute.2, ← hsplit]
            exact hstable
          have hlt : (l ++ r).length < n := by
            rw [hsplit] at hn
            simp only [List.length_cons, List.length_append] at hn ⊢
            omega
          have hih := ih (l ++ r).length hlt (l ++ r) rfl
            (actuate π S ξ w) htail hstable' ws hws
          constructor
          · rw [hsplit]
            have hlen_le := hih.1
            simp only [List.length_cons, List.length_append] at hlen_le ⊢
            omega
          · intro x
            rw [hsplit]
            have hx := hih.2 x
            by_cases hxw : x = w
            · subst x
              have hzero : l.count w = 0 := List.count_eq_zero_of_not_mem hnot
              simp only [List.count_append, List.count_cons_self] at hx ⊢
              omega
            · simp only [List.count_append,
                List.count_cons_of_ne (Ne.symm hxw)] at hx ⊢
              exact hx
  exact H vs.length vs rfl ξ hvs hstable ws hws

omit [G.LocallyFinite] in
/-- Two legal routings of the same length that fire every vertex the same number of times produce
the same final state. -/
theorem run_eq_of_count_eq (π : Mechanism G) (S : Finset V) (ξ : RState G)
    (vs ws : List V) (hvs : IsLegal π S ξ vs) (hws : IsLegal π S ξ ws)
    (hlen : vs.length = ws.length) (hcount : ∀ v, vs.count v = ws.count v) :
    run π S ξ vs = run π S ξ ws := by
  have H : ∀ n : ℕ, ∀ (vs ws : List V), vs.length = n →
      ∀ (ξ : RState G), IsLegal π S ξ vs → IsLegal π S ξ ws →
      vs.length = ws.length → (∀ v, vs.count v = ws.count v) →
      run π S ξ vs = run π S ξ ws := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro vs ws hn ξ hvs hws hlen hcount
      cases vs with
      | nil =>
        cases ws with
        | nil => rfl
        | cons w ws => simp at hlen
      | cons v vs =>
        cases ws with
        | nil => simp at hlen
        | cons w ws =>
          rw [isLegal_cons] at hvs hws
          obtain ⟨hvS, hv, hvs⟩ := hvs
          obtain ⟨hwS, hw, hws⟩ := hws
          have hwmem : v ∈ w :: ws := by
            rw [← List.count_pos_iff, ← hcount v]
            simp
          obtain ⟨l, r, hsplit, hnot⟩ := exists_append_cons_not_mem_of_mem (w :: ws) v hwmem
          have hex : IsLegal π S ξ (v :: (l ++ r)) ∧
              run π S ξ (v :: (l ++ r)) = run π S ξ (l ++ v :: r) :=
            isLegal_cons_run_eq_of_not_mem π S ξ l v r hvS hv hnot (by
              rw [← hsplit]
              exact ⟨hwS, hw, hws⟩)
          have hleg' : IsLegal π S (actuate π S ξ v) (l ++ r) := by
            obtain ⟨-, -, hleg'⟩ :=
              (isLegal_cons π S ξ v (l ++ r)).1 hex.1
            exact hleg'
          have hlen' : vs.length = (l ++ r).length := by
            rw [hsplit] at hlen
            simp only [List.length_cons, List.length_append] at hlen ⊢
            omega
          have hcount' : ∀ x, vs.count x = (l ++ r).count x := by
            intro x
            have hx := hcount x
            rw [hsplit, List.count_append] at hx
            by_cases hxv : x = v
            · subst x
              simp only [List.count_cons_self, List.count_append] at hx ⊢
              omega
            · simp only [List.count_cons_of_ne (Ne.symm hxv), List.count_append] at hx ⊢
              exact hx
          have hlt : vs.length < n := by
            simp only [List.length_cons] at hn
            simp only [List.length_append] at hlen' ⊢
            omega
          have hi := ih vs.length hlt vs (l ++ r) rfl
            (actuate π S ξ v) hvs hleg' hlen' hcount'
          calc
            run π S ξ (v :: vs) = run π S (actuate π S ξ v) vs := rfl
            _ = run π S (actuate π S ξ v) (l ++ r) := hi
            _ = run π S ξ (v :: (l ++ r)) := rfl
            _ = run π S ξ (l ++ v :: r) := hex.2
            _ = run π S ξ (w :: ws) := by rw [hsplit]
  exact H vs.length vs ws rfl ξ hvs hws hlen hcount

variable (G : SimpleGraph V) [G.LocallyFinite]

omit [G.LocallyFinite] in
-- FROZEN-STATEMENT-BEGIN
/-- HLMPPW Lemma 3.9 (`lem:least-action`, `external input, HLMPPW Lemma 3.9,
the statement of lem:least-action`), proved rather than assumed. -/
theorem abelian_holds : Rotor.External.Abelian G
-- FROZEN-STATEMENT-END
:= by
  intro π hInfinite hConnected S hS ξ vs ws hvs hws
  constructor
  · intro hvsStable
    exact length_le_count_le_of_stable π S ξ vs hvs hvsStable ws hws
  · intro hvsStable hwsStable
    have h₁ := length_le_count_le_of_stable π S ξ vs hvs hvsStable ws hws
    have h₂ := length_le_count_le_of_stable π S ξ ws hws hwsStable vs hvs
    have hlen : ws.length = vs.length := Nat.le_antisymm h₁.1 h₂.1
    have hcount : ∀ v, vs.count v = ws.count v := by
      intro v
      exact Nat.le_antisymm (h₂.2 v) (h₁.2 v)
    refine ⟨hlen, ?_, ?_⟩
    · exact (run_eq_of_count_eq π S ξ vs ws hvs hws hlen.symm hcount).symm
    · intro v
      exact (hcount v).symm

end Rotor.Bridge
