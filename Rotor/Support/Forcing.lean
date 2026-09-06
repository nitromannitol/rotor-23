import Rotor.Support.IntervalTree
import Rotor.Support.BlockRoute

namespace Rotor

/-! ### Degree-two forcing

If every internal vertex of the path `q` has only its two `q`-bonds open, and neither endpoint of
the open path `p` is an internal vertex of `q`, then `p` contains `q` consecutively as soon as it
uses one bond of `q`. -/

/-- Every bond open in `ω` at an internal vertex of `q` is one of the two `q`-bonds there. -/
def ForcedPath (ω : BondConfig) (q : List Site) : Prop :=
  ∀ i, 0 < i → i + 1 < q.length → ∀ u w, q[i]? = some u → squareGraph.Adj u w →
    ω s(u, w) = true → q[i - 1]? = some w ∨ q[i + 1]? = some w

/-- Neither endpoint of `p` is an internal vertex of `q`. -/
def EndsOff (q p : List Site) : Prop :=
  ∀ i, 0 < i → i + 1 < q.length → p.head? ≠ q[i]? ∧ p.getLast? ≠ q[i]?

section Forcing

variable (ω : BondConfig) {q p : List Site}

theorem forced_forward (hq : ForcedPath ω q) (hp : IsOpenPath ω p) (he : EndsOff q p)
    {i j : ℕ} (hi : i + 1 < p.length) (hj : j + 1 < q.length)
    (h0 : p[i]? = q[j]?) (h1 : p[i + 1]? = q[j + 1]?) :
    ∀ m, j + m + 1 < q.length → i + m + 1 < p.length ∧ p[i + m]? = q[j + m]? ∧
      p[i + m + 1]? = q[j + m + 1]? := by
  intro m
  induction m with
  | zero => intro _; exact ⟨hi, h0, h1⟩
  | succ m ih =>
    intro hm
    obtain ⟨hlen, e0, e1⟩ := ih (by omega)
    show i + m + 1 + 1 < p.length ∧ p[i + m + 1]? = q[j + m + 1]? ∧
      p[i + m + 1 + 1]? = q[j + m + 1 + 1]?
    have hu : q[j + m + 1]? = some (q[j + m + 1]'(by omega)) := List.getElem?_eq_getElem _
    generalize hu' : q[j + m + 1]'(by omega) = u at hu
    have hpu : p[i + m + 1]? = some u := e1.trans hu
    have hlt : i + m + 1 + 1 < p.length := by
      by_contra hcon
      have hlast : p.getLast? = some u := by
        rw [List.getLast?_eq_getElem?, show p.length - 1 = i + m + 1 by omega]; exact hpu
      exact (he (j + m + 1) (by omega) (by omega)).2 (hlast.trans hu.symm)
    have hw : p[i + m + 1 + 1]? = some (p[i + m + 1 + 1]'hlt) := List.getElem?_eq_getElem _
    generalize hw' : p[i + m + 1 + 1]'hlt = w at hw
    have hadj : squareGraph.Adj u w := isChain_getElem? hp.1.2 hpu hw
    have hopen : ω s(u, w) = true := isChain_getElem? hp.2 hpu hw
    rcases hq (j + m + 1) (by omega) (by omega) u w hu hadj hopen with h | h
    · exfalso
      rw [show j + m + 1 - 1 = j + m by omega] at h
      have : i + m = i + m + 1 + 1 :=
        List.getElem?_inj (by omega) hp.1.1 (e0.trans (h.trans hw.symm))
      omega
    · exact ⟨hlt, e1, hw.trans h.symm⟩

theorem forced_backward (hq : ForcedPath ω q) (hp : IsOpenPath ω p) (he : EndsOff q p)
    {i j : ℕ} (hi : i + 1 < p.length) (hj : j + 1 < q.length)
    (h0 : p[i]? = q[j]?) (h1 : p[i + 1]? = q[j + 1]?) :
    ∀ m, m ≤ j → m ≤ i ∧ p[i - m]? = q[j - m]? ∧ p[i - m + 1]? = q[j - m + 1]? := by
  intro m
  induction m with
  | zero => intro _; exact ⟨Nat.zero_le _, h0, h1⟩
  | succ m ih =>
    intro hm
    obtain ⟨hmi, e0, e1⟩ := ih (by omega)
    have hu : q[j - m]? = some (q[j - m]'(by omega)) := List.getElem?_eq_getElem _
    generalize hu' : q[j - m]'(by omega) = u at hu
    have hpu : p[i - m]? = some u := e0.trans hu
    have hpos : 0 < i - m := by
      by_contra hcon
      have hhead : p.head? = some u := by
        rw [List.head?_eq_getElem?, show 0 = i - m by omega]; exact hpu
      exact (he (j - m) (by omega) (by omega)).1 (hhead.trans hu.symm)
    have hw : p[i - m - 1]? = some (p[i - m - 1]'(by omega)) := List.getElem?_eq_getElem _
    generalize hw' : p[i - m - 1]'(by omega) = w at hw
    have hpu' : p[i - m - 1 + 1]? = some u := by
      rw [show i - m - 1 + 1 = i - m by omega]; exact hpu
    have hadj : squareGraph.Adj w u := isChain_getElem? hp.1.2 hw hpu'
    have hopen : ω s(w, u) = true := isChain_getElem? hp.2 hw hpu'
    rcases hq (j - m) (by omega) (by omega) u w hu hadj.symm (by rwa [Sym2.eq_swap]) with h | h
    · refine ⟨by omega, ?_, ?_⟩
      · rw [show i - (m + 1) = i - m - 1 by omega, show j - (m + 1) = j - m - 1 by omega]
        exact hw.trans h.symm
      · rw [show i - (m + 1) + 1 = i - m by omega, show j - (m + 1) + 1 = j - m by omega]
        exact e0
    · exfalso
      have : i - m - 1 = i - m + 1 :=
        List.getElem?_inj (by omega) hp.1.1 (hw.trans (h.symm.trans e1.symm))
      omega

theorem segment_of_forced (hq : ForcedPath ω q) (hp : IsOpenPath ω p) (he : EndsOff q p)
    {i j : ℕ} (hi : i + 1 < p.length) (hj : j + 1 < q.length)
    (h0 : p[i]? = q[j]?) (h1 : p[i + 1]? = q[j + 1]?) :
    ∃ i₀, (p.drop i₀).take q.length = q := by
  have hb := forced_backward ω hq hp he hi hj h0 h1 j le_rfl
  have hf := forced_forward ω hq hp he hi hj h0 h1 (q.length - 2 - j) (by omega)
  refine ⟨i - j, ?_⟩
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, List.getElem?_drop]
  split_ifs with hk
  · rcases lt_or_ge k j with hkj | hkj
    · have := forced_backward ω hq hp he hi hj h0 h1 (j - k) (by omega)
      rw [show j - (j - k) = k by omega, show i - (j - k) = i - j + k by omega] at this
      exact this.2.1
    · rcases lt_or_ge (k + 1) q.length with hk1 | hk1
      · have := forced_forward ω hq hp he hi hj h0 h1 (k - j) (by omega)
        rw [show j + (k - j) = k by omega, show i + (k - j) = i - j + k by omega] at this
        exact this.2.1
      · rw [show k = j + (q.length - 2 - j) + 1 by omega,
          show i - j + (j + (q.length - 2 - j) + 1) = i + (q.length - 2 - j) + 1 by omega]
        exact hf.2.2
  · rw [List.getElem?_eq_none (by omega)]

theorem forcedPath_reverse (h : ForcedPath ω q) : ForcedPath ω q.reverse := by
  intro i hi hi' u w hu hadj hopen
  rw [List.length_reverse] at hi'
  rw [List.getElem?_reverse (by omega)] at hu
  rcases h (q.length - 1 - i) (by omega) (by omega) u w hu hadj hopen with h' | h'
  · right
    rw [List.getElem?_reverse (by omega), show q.length - 1 - (i + 1) = q.length - 1 - i - 1 by omega]
    exact h'
  · left
    rw [List.getElem?_reverse (by omega), show q.length - 1 - (i - 1) = q.length - 1 - i + 1 by omega]
    exact h'

theorem endsOff_reverse (h : EndsOff q p) : EndsOff q.reverse p := by
  intro i hi hi'
  rw [List.length_reverse] at hi'
  rw [List.getElem?_reverse (by omega)]
  exact h (q.length - 1 - i) (by omega) (by omega)

/-- The forcing lemma. -/
theorem traverses_of_forced (hq : ForcedPath ω q) (hp : IsOpenPath ω p) (he : EndsOff q p)
    {i j : ℕ} (hi : i + 1 < p.length) (hj : j + 1 < q.length)
    (h : (p[i]? = q[j]? ∧ p[i + 1]? = q[j + 1]?) ∨ (p[i]? = q[j + 1]? ∧ p[i + 1]? = q[j]?)) :
    Traverses p q := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · obtain ⟨i₀, hi₀⟩ := segment_of_forced ω hq hp he hi hj h0 h1
    exact ⟨i₀, Or.inl hi₀⟩
  · have hj' : (q.length - 2 - j) + 1 < q.reverse.length := by rw [List.length_reverse]; omega
    have h0' : p[i]? = q.reverse[q.length - 2 - j]? := by
      rw [List.getElem?_reverse (by omega), show q.length - 1 - (q.length - 2 - j) = j + 1 by omega]
      exact h0
    have h1' : p[i + 1]? = q.reverse[q.length - 2 - j + 1]? := by
      rw [List.getElem?_reverse (by omega),
        show q.length - 1 - (q.length - 2 - j + 1) = j by omega]
      exact h1
    obtain ⟨i₀, hi₀⟩ := segment_of_forced ω (forcedPath_reverse ω hq) hp (endsOff_reverse he)
      hi hj' h0' h1'
    refine ⟨i₀, Or.inr ?_⟩
    rw [List.length_reverse] at hi₀; exact hi₀

end Forcing

end Rotor
