/-
The sub-path of a live path that crosses one enlarged block: a path that visits `Q_z` and
later leaves `Q_z⁺` witnesses the marked block event `E_z` (`rotor.tex:1265-1268`: "forces
`E_z` along `cR` blocks").
-/
import Rotor.Support.BlockField
import Rotor.Support.KingPaths

open MeasureTheory

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)
  (P : DoublyPeriodic G)

/-! ### Infixes of a path -/

/-- The infix of `l` starting at index `a` with `k` elements. -/
def infixAt (l : List V) (a k : ℕ) : List V := (l.drop a).take k

omit [DecidableEq V] [G.LocallyFinite] in
theorem length_infixAt (l : List V) (a k : ℕ) (h : a + k ≤ l.length) :
    (infixAt l a k).length = k := by
  simp only [infixAt, List.length_take, List.length_drop]
  omega

omit [DecidableEq V] [G.LocallyFinite] in
theorem getElem_infixAt (l : List V) (a k i : ℕ) (hi : i < (infixAt l a k).length) :
    (infixAt l a k)[i] = l[a + i]'(by simp only [infixAt, List.length_take, List.length_drop] at hi; omega) := by
  simp only [infixAt]
  rw [List.getElem_take, List.getElem_drop]

omit [DecidableEq V] [G.LocallyFinite] in
theorem get_infixAt (l : List V) (a k i : ℕ) (hi : i < (infixAt l a k).length) :
    (infixAt l a k).get ⟨i, hi⟩ =
      l.get ⟨a + i, by simp only [infixAt, List.length_take, List.length_drop] at hi; omega⟩ := by
  simp only [List.get_eq_getElem]
  exact getElem_infixAt l a k i hi

omit [DecidableEq V] [G.LocallyFinite] in
theorem infixAt_isInfix (l : List V) (a k : ℕ) : infixAt l a k <:+: l :=
  (List.take_prefix k _).isInfix.trans (List.drop_suffix a l).isInfix

omit [DecidableEq V] [G.LocallyFinite] in
theorem isPath_infixAt {l : List V} (hl : IsPath G l) (a k : ℕ) : IsPath G (infixAt l a k) :=
  ⟨hl.1.sublist (infixAt_isInfix l a k).sublist, hl.2.infix (infixAt_isInfix l a k)⟩

omit [G.LocallyFinite] in
theorem liveAtIndex_infixAt (ρ : Config G) (l : List V) (a k i : ℕ) (hk : a + k ≤ l.length)
    (hi : i + 2 < k) :
    LiveAtIndex π ρ (infixAt l a k) (i + 1) ↔ LiveAtIndex π ρ l (a + i + 1) := by
  have hlen := length_infixAt l a k hk
  have e0 : (infixAt l a k).get ⟨i, by omega⟩ = l.get ⟨a + i, by omega⟩ := get_infixAt l a k i _
  have e1 : (infixAt l a k).get ⟨i + 1, by omega⟩ = l.get ⟨a + i + 1, by omega⟩ :=
    get_infixAt l a k (i + 1) _
  have e2 : (infixAt l a k).get ⟨i + 2, by omega⟩ = l.get ⟨a + i + 2, by omega⟩ :=
    get_infixAt l a k (i + 2) _
  unfold LiveAtIndex
  constructor
  · rintro ⟨hh, hl⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h : LiveAt π ρ ((infixAt l a k).get ⟨i, by omega⟩) ((infixAt l a k).get ⟨i + 1, by omega⟩)
      ((infixAt l a k).get ⟨i + 2, by omega⟩) := hl
    rw [e0, e1, e2] at h
    exact h
  · rintro ⟨hh, hl⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h : LiveAt π ρ (l.get ⟨a + i, by omega⟩) (l.get ⟨a + i + 1, by omega⟩)
      (l.get ⟨a + i + 2, by omega⟩) := hl
    rw [← e0, ← e1, ← e2] at h
    exact h

omit [G.LocallyFinite] in
theorem isLiveUnmarked_infixAt (p : MPair G) (l : List V) (a k : ℕ) (hk : a + k ≤ l.length)
    (hl : IsLiveUnmarked π p l) : IsLiveUnmarked π p (infixAt l a k) := by
  intro i hi hi0
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hlen := length_infixAt l a k hk
  have hlt : j + 2 < k := by rw [hlen] at hi; omega
  rcases hl (a + j + 1) (by omega) (by omega) with hm | hlv
  · left
    rw [get_infixAt]
    exact hm
  · right
    exact (liveAtIndex_infixAt π p.1 l a k j hk hlt).2 hlv

/-! ### A visit followed by an exit witnesses the block event -/

omit [DecidableEq V] [G.LocallyFinite] in
theorem block_subset_blockPlus {L : ℕ} (hL : 0 < L) (z : ℤ × ℤ) :
    P.block L z ⊆ P.blockPlus L z := by
  intro v hv
  rw [P.mem_block_iff hL] at hv
  rw [P.mem_blockPlus_iff hL, hv, sub_self]
  simp [linf]

omit [G.LocallyFinite] in
/-- A live-at-unmarked path that visits `Q_z` and later leaves `Q_z⁺` witnesses `E_z`. -/
theorem markedBlockEvent_of_visit {L : ℕ} (hL : 0 < L) (z : ℤ × ℤ) (p : MPair G) (l : List V)
    (hpath : IsPath G l) (hlive : IsLiveUnmarked π p l) (a : ℕ) (ha : a < l.length)
    (haz : l[a] ∈ P.block L z) (b : ℕ) (hb : b < l.length) (hab : a < b)
    (hbz : l[b] ∉ P.blockPlus L z) : p ∈ markedBlockEvent π P L z := by
  classical
  have hex : ∃ b', a < b' ∧ ∃ hb' : b' < l.length, l[b'] ∉ P.blockPlus L z := ⟨b, hab, hb, hbz⟩
  obtain ⟨hab₀, hb₀, hb₀z⟩ := Nat.find_spec hex
  have hmin : ∀ c, a < c → c < Nat.find hex → ∀ hc : c < l.length, l[c] ∈ P.blockPlus L z := by
    intro c hac hcb hc
    by_contra hno
    exact Nat.find_min hex hcb ⟨hac, hc, hno⟩
  have hk : a + (Nat.find hex - a + 1) ≤ l.length := by omega
  have hlen := length_infixAt l a (Nat.find hex - a + 1) hk
  refine ⟨infixAt l a (Nat.find hex - a + 1), isPath_infixAt hpath _ _,
    isLiveUnmarked_infixAt π p l a _ hk hlive, ⟨by omega, ?_⟩, ?_, ?_⟩
  · rw [get_infixAt]
    simpa using haz
  · intro i hi
    rw [get_infixAt]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact block_subset_blockPlus P hL z (by simpa using haz)
    · exact hmin (a + i) (by omega) (by omega) _
  · intro y hy
    rw [List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel, List.getElem?_eq_getElem (by omega),
      Option.mem_def, Option.some.injEq] at hy
    rw [← hy, getElem_infixAt]
    have : a + (Nat.find hex - a) = Nat.find hex := by omega
    simp only [this]
    exact hb₀z

end Rotor
