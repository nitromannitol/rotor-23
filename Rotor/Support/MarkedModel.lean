import Rotor.Support.GridBlocks
import Rotor.Support.Forcing

namespace Rotor

/-! ### Windows of a list -/

theorem window_iff {l w : List Site} {i n : ℕ} (hw : w.length = n) :
    (l.drop i).take n = w ↔ ∀ j < n, l[i + j]? = w[j]? := by
  constructor
  · intro h j hj
    rw [← h, List.getElem?_take, List.getElem?_drop, if_pos hj]
  · intro h
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_take, List.getElem?_drop]
    split_ifs with hk
    · exact h k hk
    · rw [List.getElem?_eq_none (by omega)]

theorem window_le {l w : List Site} {i n : ℕ} (h : (l.drop i).take n = w) (hw : w.length = n)
    (hn : 0 < n) : i + n ≤ l.length := by
  have h1 := (window_iff hw).1 h (n - 1) (by omega)
  have h2 : w[n - 1]? = some (w[n - 1]'(by omega)) := List.getElem?_eq_getElem _
  rw [h2] at h1
  have := (List.getElem?_eq_some_iff.1 h1).1
  omega

theorem traverses_nil (l : List Site) : Traverses l [] := ⟨0, Or.inl (by simp)⟩

theorem traverses_reverse {l w : List Site} (h : Traverses l w) : Traverses l.reverse w := by
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · rw [List.eq_nil_of_length_eq_zero h0]; exact traverses_nil _
  obtain ⟨i, h⟩ := h
  have key : ∀ w' : List Site, w'.length = w.length → (l.drop i).take w.length = w' →
      (l.reverse.drop (l.length - i - w.length)).take w.length = w'.reverse := by
    intro w' hw' hwin
    have hle := window_le hwin hw' hpos
    rw [window_iff hw'] at hwin
    rw [window_iff (by rw [List.length_reverse, hw'])]
    intro j hj
    rw [List.getElem?_reverse (by omega), List.getElem?_reverse (by omega),
      show l.length - 1 - (l.length - i - w.length + j) = i + (w.length - 1 - j) by omega, hw']
    exact hwin _ (by omega)
  rcases h with h | h
  · exact ⟨l.length - i - w.length, Or.inr (key w rfl h)⟩
  · refine ⟨l.length - i - w.length, Or.inl ?_⟩
    have := key w.reverse List.length_reverse h
    rwa [List.reverse_reverse] at this

theorem traverses_of_window {p q w : List Site} {i : ℕ} (h : (p.drop i).take q.length = q)
    (hq : Traverses q w) : Traverses p w := by
  obtain ⟨j, hj⟩ := hq
  rw [window_iff rfl] at h
  have key : ∀ w' : List Site, w'.length = w.length → (q.drop j).take w.length = w' →
      (p.drop (i + j)).take w.length = w' := by
    intro w' hw' hwin
    rw [window_iff hw'] at hwin ⊢
    intro k hk
    have hwk := hwin k hk
    have hk' : j + k < q.length := by
      have h2 : w'[k]? = some (w'[k]'(by omega)) := List.getElem?_eq_getElem _
      rw [h2] at hwk
      exact (List.getElem?_eq_some_iff.1 hwk).1
    rw [show i + j + k = i + (j + k) by omega, h (j + k) hk']
    exact hwk
  rcases hj with hj | hj
  · exact ⟨i + j, Or.inl (key w rfl hj)⟩
  · exact ⟨i + j, Or.inr (key w.reverse List.length_reverse hj)⟩

theorem traverses_trans {p q w : List Site} (h₁ : Traverses p q) (h₂ : Traverses q w) :
    Traverses p w := by
  obtain ⟨i, h₁⟩ := h₁
  rcases h₁ with h | h
  · exact traverses_of_window h h₂
  · rw [← List.length_reverse] at h
    exact traverses_of_window h (traverses_reverse h₂)

theorem traverses_pair {p w : List Site} (h : Traverses p w) {i : ℕ} (hi : i + 1 < w.length) :
    ∃ k, k + 1 < p.length ∧ ((p[k]? = w[i]? ∧ p[k + 1]? = w[i + 1]?) ∨
      (p[k]? = w[i + 1]? ∧ p[k + 1]? = w[i]?)) := by
  obtain ⟨j, h⟩ := h
  rcases h with h | h
  · rw [window_iff rfl] at h
    have h1 : p[j + (i + 1)]? = w[i + 1]? := h (i + 1) hi
    have hlt : j + i + 1 < p.length := by
      have h2 : w[i + 1]? = some (w[i + 1]'hi) := List.getElem?_eq_getElem _
      rw [h2] at h1
      have := (List.getElem?_eq_some_iff.1 h1).1; omega
    exact ⟨j + i, hlt, Or.inl ⟨h i (by omega),
      by rw [show j + i + 1 = j + (i + 1) by omega]; exact h1⟩⟩
  · rw [window_iff List.length_reverse] at h
    have h0 : p[j + (w.length - 2 - i)]? = w[i + 1]? := by
      rw [h _ (by omega), List.getElem?_reverse (by omega),
        show w.length - 1 - (w.length - 2 - i) = i + 1 by omega]
    have h1 : p[j + (w.length - 2 - i) + 1]? = w[i]? := by
      rw [show j + (w.length - 2 - i) + 1 = j + (w.length - 2 - i + 1) by omega, h _ (by omega),
        List.getElem?_reverse (by omega), show w.length - 1 - (w.length - 2 - i + 1) = i by omega]
    have hlt : j + (w.length - 2 - i) + 1 < p.length := by
      have h2 : w[i]? = some (w[i]'(by omega)) := List.getElem?_eq_getElem _
      rw [h2] at h1
      have := (List.getElem?_eq_some_iff.1 h1).1; omega
    exact ⟨_, hlt, Or.inr ⟨h0, h1⟩⟩

theorem mem_of_traverses {p w : List Site} (h : Traverses p w) {v : Site} (hv : v ∈ w) :
    v ∈ p := by
  obtain ⟨i, h⟩ := h
  rcases h with h | h
  · rw [← h] at hv; exact List.mem_of_mem_drop (List.mem_of_mem_take hv)
  · rw [← List.mem_reverse, ← h] at hv; exact List.mem_of_mem_drop (List.mem_of_mem_take hv)

/-- A window avoiding the middle piece of a concatenation lies in the first or the last piece. -/
theorem traverses_append_of_disjoint {l₁ l₂ l₃ w : List Site} (h : Traverses (l₁ ++ l₂ ++ l₃) w)
    (hw : ∀ v ∈ w, v ∉ l₂) (h₂ : l₂ ≠ []) : Traverses l₁ w ∨ Traverses l₃ w := by
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · rw [List.eq_nil_of_length_eq_zero h0]; exact Or.inl (traverses_nil _)
  obtain ⟨i, h⟩ := h
  have hl2 : 0 < l₂.length := List.length_pos_iff.2 h₂
  have key : ∀ w' : List Site, w'.length = w.length → (∀ v ∈ w', v ∉ l₂) →
      ((l₁ ++ l₂ ++ l₃).drop i).take w.length = w' →
      (l₁.drop i).take w.length = w' ∨
        (l₃.drop (i - l₁.length - l₂.length)).take w.length = w' := by
    intro w' hw' hw'2 hwin
    have hle := window_le hwin hw' hpos
    simp only [List.length_append] at hle
    rw [window_iff hw'] at hwin
    by_cases hcase : i + w.length ≤ l₁.length
    · left
      rw [window_iff hw']
      intro j hj
      rw [← hwin j hj, List.getElem?_append_left (by rw [List.length_append]; omega),
        List.getElem?_append_left (by omega)]
    by_cases hcase2 : l₁.length + l₂.length ≤ i
    · right
      rw [window_iff hw']
      intro j hj
      rw [← hwin j hj, List.getElem?_append_right (by rw [List.length_append]; omega),
        List.length_append,
        show i + j - (l₁.length + l₂.length) = i - l₁.length - l₂.length + j by omega]
    exfalso
    obtain ⟨m, hm1, hm2, hm3, hm4⟩ : ∃ m, i ≤ m ∧ m < i + w.length ∧ l₁.length ≤ m ∧
        m < l₁.length + l₂.length := by
      rcases le_or_lt i l₁.length with hil | hil
      · exact ⟨l₁.length, hil, by omega, le_rfl, by omega⟩
      · exact ⟨i, le_rfl, by omega, hil.le, by omega⟩
    have hv := hwin (m - i) (by omega)
    rw [show i + (m - i) = m by omega,
      List.getElem?_append_left (by rw [List.length_append]; omega),
      List.getElem?_append_right hm3] at hv
    obtain ⟨v, hv'⟩ : ∃ v, l₂[m - l₁.length]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [hv'] at hv
    exact hw'2 v (List.mem_of_getElem? hv.symm) (List.mem_of_getElem? hv')
  rcases h with h | h
  · rcases key w rfl hw h with h' | h'
    · exact Or.inl ⟨_, Or.inl h'⟩
    · exact Or.inr ⟨_, Or.inl h'⟩
  · rcases key w.reverse List.length_reverse (fun v hv => hw v (List.mem_reverse.1 hv)) h
      with h' | h'
    · exact Or.inl ⟨_, Or.inr h'⟩
    · exact Or.inr ⟨_, Or.inr h'⟩

/-! ### Open paths under changed configurations -/

theorem isOpenPath_mono {ω ω' : BondConfig} {l : List Site} (h : IsOpenPath ω l)
    (h' : ∀ i (hi : i + 1 < l.length), ω s(l[i], l[i + 1]) = true →
      ω' s(l[i], l[i + 1]) = true) : IsOpenPath ω' l := by
  have h2 := h.2
  rw [List.isChain_iff_getElem] at h2
  exact ⟨h.1, List.isChain_iff_getElem.2 (fun i hi => h' i hi (h2 i hi))⟩

theorem isOpenPath_of_agree {ω ω' : BondConfig} {l : List Site} (h : IsOpenPath ω l)
    (h' : ∀ i (hi : i + 1 < l.length), ω' s(l[i], l[i + 1]) = ω s(l[i], l[i + 1])) :
    IsOpenPath ω' l :=
  isOpenPath_mono h (fun i hi hop => (h' i hi).trans hop)

/-- A path open after opening `e` but not after closing `e` uses `e`. -/
theorem exists_used_of_update {ω : BondConfig} {e : Sym2 Site} {l : List Site}
    (h : IsOpenPath (Function.update ω e true) l)
    (hno : ¬ IsOpenPath (Function.update ω e false) l) :
    ∃ i, ∃ hi : i + 1 < l.length, s(l[i], l[i + 1]) = e := by
  by_contra hcon
  push_neg at hcon
  apply hno
  refine isOpenPath_of_agree h (fun i hi => ?_)
  rw [Function.update_of_ne (hcon i hi), Function.update_of_ne (hcon i hi)]

theorem isOpenPath_update_of_not_used {ω : BondConfig} {e : Sym2 Site} {l : List Site} {b : Bool}
    (h : IsOpenPath ω l) (hno : ∀ i (hi : i + 1 < l.length), s(l[i], l[i + 1]) ≠ e) :
    IsOpenPath (Function.update ω e b) l :=
  isOpenPath_of_agree h (fun i hi => Function.update_of_ne (hno i hi) _ _)

/-! ### The marked model -/

/-- Valid paths of the marked model: open simple paths from `x` to `y` inside `D` such that every
copy `cp z`, `z ∈ Z`, traversed consecutively has mark `σ z = true`. -/
def ValidPath (x y : Site) (D : Finset Site) (Z : Finset (ℤ × ℤ)) (cp : ℤ × ℤ → List Site)
    (ω : BondConfig) (σ : ℤ × ℤ → Bool) (l : List Site) : Prop :=
  IsOpenPath ω l ∧ l.head? = some x ∧ l.getLast? = some y ∧ (∀ v ∈ l, v ∈ D) ∧
    ∀ z ∈ Z, Traverses l (cp z) → σ z = true

/-- The copies of `P⋆` in the grid through `x` and `y`. -/
def gridCopy (x y : Site) (z : ℤ × ℤ) : List Site := copyAt (blockCorner x y z)

/-- The bonds of the path `q`. -/
def QBond (q : List Site) (b : Sym2 Site) : Prop :=
  ∃ i u v, q[i]? = some u ∧ q[i + 1]? = some v ∧ b = s(u, v)

/-- `b` touches an internal vertex of `q`. -/
def TouchesInternal (q : List Site) (b : Sym2 Site) : Prop :=
  ∃ i, 0 < i ∧ i + 1 < q.length ∧ ∃ u, q[i]? = some u ∧ u ∈ b

open Classical in
/-- The surgery configuration: open the route `q`, close every other bond at its internal
vertices and the bond `e`, keep the rest. -/
noncomputable def surgeryConfig (ω : BondConfig) (q : List Site) (e : Sym2 Site) : BondConfig :=
  fun b => if QBond q b then true else if TouchesInternal q b ∨ b = e then false else ω b

theorem surgeryConfig_of_qbond {ω : BondConfig} {q : List Site} {e b : Sym2 Site}
    (h : QBond q b) : surgeryConfig ω q e b = true := by
  unfold surgeryConfig; rw [if_pos h]

theorem surgeryConfig_eq_of_not {ω : BondConfig} {q : List Site} {e b : Sym2 Site}
    (h1 : ¬ QBond q b) (h2 : ¬ TouchesInternal q b) (h3 : b ≠ e) :
    surgeryConfig ω q e b = ω b := by
  unfold surgeryConfig; rw [if_neg h1, if_neg (by tauto)]

theorem surgeryConfig_true_iff {ω : BondConfig} {q : List Site} {e b : Sym2 Site} :
    surgeryConfig ω q e b = true ↔
      QBond q b ∨ (¬ TouchesInternal q b ∧ b ≠ e ∧ ω b = true) := by
  unfold surgeryConfig
  split_ifs with h1 h2
  · simp [h1]
  · simp only [Bool.false_eq_true, false_iff]; tauto
  · push_neg at h2; simp [h1, h2]

theorem qbond_mem {q : List Site} {b : Sym2 Site} (h : QBond q b) {v : Site} (hv : v ∈ b) :
    v ∈ q := by
  obtain ⟨i, u, u', hu, hu', rfl⟩ := h
  rcases Sym2.mem_iff.1 hv with rfl | rfl
  · exact List.mem_of_getElem? hu
  · exact List.mem_of_getElem? hu'

theorem touchesInternal_mem {q : List Site} {b : Sym2 Site} (h : TouchesInternal q b) :
    ∃ v ∈ b, v ∈ q := by
  obtain ⟨i, -, -, u, hu, hub⟩ := h
  exact ⟨u, hub, List.mem_of_getElem? hu⟩

/-- On the route, the surgery configuration forces the route. -/
theorem forcedPath_surgery (ω : BondConfig) {q : List Site} (hq : q.Nodup) (e : Sym2 Site) :
    ForcedPath (surgeryConfig ω q e) q := by
  intro i hi hi' u w hu hadj hop
  rw [surgeryConfig_true_iff] at hop
  rcases hop with ⟨j, u', v', hj, hj', hb⟩ | ⟨hnt, -, -⟩
  · rcases Sym2.eq_iff.1 hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : i = j := List.getElem?_inj (by omega) hq (hu.trans hj.symm)
      subst this
      exact Or.inr hj'
    · have : i = j + 1 := List.getElem?_inj (by omega) hq (hu.trans hj'.symm)
      subst this
      exact Or.inl (by simpa using hj)
  · exact absurd ⟨i, hi, hi', u, hu, Sym2.mem_mk_left _ _⟩ hnt

/-- Consecutive pairs of a traversed list are bonds of the container. -/
theorem qbond_of_traverses {q w : List Site} (h : Traverses q w) {i : ℕ} (hi : i + 1 < w.length)
    {u v : Site} (hu : w[i]? = some u) (hv : w[i + 1]? = some v) : QBond q s(u, v) := by
  obtain ⟨k, hk, hk'⟩ := traverses_pair h hi
  rcases hk' with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨k, u, v, h0.trans hu, h1.trans hv, rfl⟩
  · exact ⟨k, v, u, h0.trans hv, h1.trans hu, Sym2.eq_swap⟩

/-- A vertex of a block that is interior to a grid block lies in that block. -/
theorem eq_of_inBlock_interiorB (x y : Site) {z z' : ℤ × ℤ} {v : Site}
    (h : InBlock (blockCorner x y z) v) (h' : InteriorB (blockCorner x y z') v) : z = z' := by
  unfold InBlock blockCorner at h
  unfold InteriorB blockCorner at h'
  exact Prod.ext (by omega) (by omega)

end Rotor
