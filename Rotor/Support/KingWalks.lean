import Rotor.Support.KingPaths

/-!
Lattice animals for the pendant counterexample (`rotor.tex:2240-2247`): the number of
`ℓ^∞`-connected sets of `n + 1` sites containing a fixed site `o` is at most `64 ^ n`.  Every
such set is the set of sites of a closed king walk of `2n` steps from `o` (walk around a
spanning tree: remove a site farthest from `o`, cover the rest, and insert a detour), and
there are at most `8 ^ (2n)` such walks.
-/

open Finset

namespace Rotor

/-- King walks of `m` steps from `o`, stored most recent first: lists of length `m + 1` ending
in `o` whose consecutive entries are king steps. -/
def kingWalks (o : ℤ × ℤ) : ℕ → Finset (List (ℤ × ℤ))
  | 0 => {[o]}
  | m + 1 => (kingWalks o m).biUnion (fun p => (kingNbrs (p.headD o)).image (fun b => b :: p))

theorem card_kingWalks (o : ℤ × ℤ) (m : ℕ) : (kingWalks o m).card ≤ 8 ^ m := by
  induction m with
  | zero => simp [kingWalks]
  | succ m ih =>
    calc (kingWalks o (m + 1)).card
        ≤ ∑ p ∈ kingWalks o m, ((kingNbrs (p.headD o)).image (fun b => b :: p)).card :=
          card_biUnion_le
      _ ≤ ∑ p ∈ kingWalks o m, 8 :=
          sum_le_sum (fun p _ => card_image_le.trans (card_kingNbrs _).le)
      _ = (kingWalks o m).card * 8 := by rw [sum_const, smul_eq_mul]
      _ ≤ 8 ^ m * 8 := Nat.mul_le_mul_right _ ih
      _ = 8 ^ (m + 1) := by ring

theorem mem_kingWalks_iff (o : ℤ × ℤ) : ∀ (m : ℕ) (p : List (ℤ × ℤ)),
    p ∈ kingWalks o m ↔ p.length = m + 1 ∧ p.getLast? = some o ∧ p.IsChain KingStep
  | 0, p => by
    simp only [kingWalks, mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, rfl, List.isChain_singleton _⟩
    · rintro ⟨hl, hlast, -⟩
      rcases p with _ | ⟨a, _ | ⟨b, q⟩⟩
      · simp at hl
      · simpa using hlast
      · simp at hl
  | m + 1, p => by
    simp only [kingWalks, mem_biUnion, mem_image]
    constructor
    · rintro ⟨q, hq, b, hb, rfl⟩
      obtain ⟨hlen, hlast, hchain⟩ := (mem_kingWalks_iff o m q).1 hq
      rcases q with _ | ⟨c, q'⟩
      · simp at hlen
      · rw [List.headD_cons] at hb
        refine ⟨by simp [hlen], by rw [List.getLast?_cons_cons]; exact hlast, ?_⟩
        exact List.isChain_cons_cons.2 ⟨(mem_kingNbrs.1 hb).symm, hchain⟩
    · rintro ⟨hlen, hlast, hchain⟩
      rcases p with _ | ⟨b, _ | ⟨c, q'⟩⟩
      · simp at hlen
      · simp at hlen
      · refine ⟨c :: q', (mem_kingWalks_iff o m _).2 ⟨by simpa using hlen, ?_, ?_⟩, b, ?_, rfl⟩
        · rw [List.getLast?_cons_cons] at hlast; exact hlast
        · exact (List.isChain_cons_cons.1 hchain).2
        · rw [List.headD_cons]
          exact mem_kingNbrs.2 (List.isChain_cons_cons.1 hchain).1.symm

theorem length_of_mem_kingWalks {o : ℤ × ℤ} {m : ℕ} {p : List (ℤ × ℤ)} (hp : p ∈ kingWalks o m) :
    p.length = m + 1 :=
  ((mem_kingWalks_iff o m p).1 hp).1

/-- A nonempty suffix of a king walk is a king walk. -/
theorem suffix_mem_kingWalks {o : ℤ × ℤ} {m : ℕ} {p s q : List (ℤ × ℤ)} (hp : p ∈ kingWalks o m)
    (hpq : p = s ++ q) (hq : q ≠ []) : q ∈ kingWalks o (q.length - 1) := by
  obtain ⟨hlen, hlast, hchain⟩ := (mem_kingWalks_iff o m p).1 hp
  subst hpq
  refine (mem_kingWalks_iff o _ q).2 ⟨?_, ?_, ?_⟩
  · have : 0 < q.length := List.length_pos_iff.2 hq
    omega
  · rw [List.getLast?_append_of_ne_nil s hq] at hlast
    exact hlast
  · exact (List.isChain_append.1 hchain).2.1

/-- Inserting a detour `y → x → y` into a chain keeps it a chain. -/
theorem isChain_insert_detour {α : Type*} (R : α → α → Prop) (p₁ p₂ : List α) (y x : α)
    (h : List.IsChain R (p₁ ++ y :: p₂)) (hyx : R y x) (hxy : R x y) :
    List.IsChain R (p₁ ++ y :: x :: y :: p₂) := by
  rw [List.isChain_append] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [List.isChain_cons_cons, List.isChain_cons_cons]
    exact ⟨hyx, hxy, h2⟩
  · simpa using h3

/-- Inserting the detour `y → x → y` at a visit of `y` in a king walk. -/
theorem detour_mem_kingWalks {o : ℤ × ℤ} {m : ℕ} {p₁ p₂ : List (ℤ × ℤ)} {y x : ℤ × ℤ}
    (hp : p₁ ++ y :: p₂ ∈ kingWalks o m) (hyx : KingStep y x) :
    p₁ ++ y :: x :: y :: p₂ ∈ kingWalks o (m + 2) := by
  obtain ⟨hlen, hlast, hchain⟩ := (mem_kingWalks_iff o m _).1 hp
  refine (mem_kingWalks_iff o _ _).2 ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  · rw [List.getLast?_append_of_ne_nil p₁ (List.cons_ne_nil _ _)] at hlast ⊢
    rw [List.getLast?_cons_cons, List.getLast?_cons_cons]
    exact hlast
  · exact isChain_insert_detour _ _ _ _ _ hchain hyx hyx.symm

/-- `U` is king-connected from `o`: `o ∈ U` and every site of `U` is the end of a king walk
from `o` inside `U`. -/
def KConn (o : ℤ × ℤ) (U : Finset (ℤ × ℤ)) : Prop :=
  o ∈ U ∧ ∀ v ∈ U, ∃ m, ∃ p ∈ kingWalks o m, (∀ q ∈ p, q ∈ U) ∧ p.headD o = v

theorem kconn_of_reflTransGen {o : ℤ × ℤ} {U : Finset (ℤ × ℤ)} (ho : o ∈ U)
    (h : ∀ v ∈ U, Relation.ReflTransGen (fun a b => b ∈ U ∧ KingStep a b) o v) : KConn o U := by
  refine ⟨ho, fun v hv => ?_⟩
  have hv' := h v hv
  clear hv
  induction hv' with
  | refl => exact ⟨0, [o], by simp [kingWalks], by simpa using ho, rfl⟩
  | @tail _ c _ hab ih =>
    obtain ⟨m, p, hp, hpU, hhead⟩ := ih
    refine ⟨m + 1, c :: p, ?_, ?_, rfl⟩
    · simp only [kingWalks, mem_biUnion, mem_image]
      exact ⟨p, hp, _, by rw [hhead]; exact mem_kingNbrs.2 hab.2, rfl⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hab.1
      · exact hpU q hq

/-- Every king-connected set of `n + 1` sites containing `o` is the set of sites of a king
walk of `2n` steps from `o`. -/
theorem exists_spanning_walk (o : ℤ × ℤ) : ∀ (n : ℕ) (U : Finset (ℤ × ℤ)), U.card = n + 1 →
    KConn o U → ∃ p ∈ kingWalks o (2 * n), p.toFinset = U := by
  intro n
  induction n with
  | zero =>
    intro U hU hK
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hU
    have : a = o := by
      have := hK.1
      rw [ha, mem_singleton] at this
      exact this.symm
    subst this
    exact ⟨[a], by simp [kingWalks], by simp [ha]⟩
  | succ n ih =>
    intro U hU hK
    classical
    -- the distance from `o` inside `U`
    let f : ℤ × ℤ → ℕ := fun v => if h : v ∈ U then Nat.find (hK.2 v h) else 0
    have hf : ∀ v (hv : v ∈ U), ∃ p ∈ kingWalks o (f v), (∀ q ∈ p, q ∈ U) ∧ p.headD o = v := by
      intro v hv
      simp only [f, dif_pos hv]
      exact Nat.find_spec (hK.2 v hv)
    have hf_le : ∀ v (hv : v ∈ U) (m : ℕ), (∃ p ∈ kingWalks o m, (∀ q ∈ p, q ∈ U) ∧ p.headD o = v) →
        f v ≤ m := by
      intro v hv m hm
      simp only [f, dif_pos hv]
      exact Nat.find_le hm
    have hne : (U.erase o).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hK.1, hU]
      omega
    obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image (U.erase o) f hne
    have hxo : x ≠ o := (Finset.mem_erase.1 hx).1
    have hxU : x ∈ U := (Finset.mem_erase.1 hx).2
    -- `x` is not on a shortest walk to any other site
    have hK' : KConn o (U.erase x) := by
      refine ⟨Finset.mem_erase.2 ⟨hxo.symm, hK.1⟩, fun v hv => ?_⟩
      have hvx : v ≠ x := (Finset.mem_erase.1 hv).1
      have hvU : v ∈ U := (Finset.mem_erase.1 hv).2
      obtain ⟨p, hp, hpU, hhead⟩ := hf v hvU
      refine ⟨f v, p, hp, fun q hq => Finset.mem_erase.2 ⟨?_, hpU q hq⟩, hhead⟩
      rintro rfl
      obtain ⟨s, t, hst⟩ := List.append_of_mem hq
      have hplen := length_of_mem_kingWalks hp
      by_cases hvo : v = o
      · subst hvo
        have : f v = 0 :=
          Nat.le_zero.1 (hf_le v hvU 0 ⟨[v], by simp [kingWalks], by simpa using hvU, rfl⟩)
        rw [this] at hplen
        rcases p with _ | ⟨a, _ | ⟨b, q'⟩⟩
        · simp at hplen
        · simp only [List.headD_cons] at hhead
          subst hhead
          simp at hq
          exact hvx hq.symm
        · simp at hplen
      · -- the suffix `q :: t` is a walk to `q` of fewer steps
        have hsuf := suffix_mem_kingWalks hp hst (List.cons_ne_nil _ _)
        have hfq : f q ≤ t.length := by
          have := hf_le q (hpU q hq) _ ⟨_, hsuf, fun z hz => hpU z (hst ▸ List.mem_append_right _ hz), rfl⟩
          simpa using this
        have hs : s ≠ [] := by
          rintro rfl
          simp only [List.nil_append] at hst
          subst hst
          simp only [List.headD_cons] at hhead
          exact hvx hhead.symm
        have hslen : 0 < s.length := List.length_pos_iff.2 hs
        have hfv : f v = s.length + t.length := by
          have := hplen
          rw [hst] at this
          simp only [List.length_append, List.length_cons] at this
          omega
        have := hxmax v (Finset.mem_erase.2 ⟨hvo, hvU⟩)
        omega
    have hcard : (U.erase x).card = n + 1 := by
      rw [Finset.card_erase_of_mem hxU, hU]
      rfl
    obtain ⟨p, hp, hpU⟩ := ih (U.erase x) hcard hK'
    -- a king neighbor `y` of `x` inside `U.erase x`
    obtain ⟨m, px, hpx, hpxU, hhead⟩ := hK.2 x hxU
    obtain ⟨hlen, -, hchain⟩ := (mem_kingWalks_iff o m px).1 hpx
    rcases px with _ | ⟨a, _ | ⟨y, rest⟩⟩
    · simp at hlen
    · exfalso
      simp only [List.headD_cons] at hhead
      subst hhead
      have := (mem_kingWalks_iff o m [a]).1 hpx
      simp only [List.length_singleton, List.getLast?_singleton, Option.some.injEq] at this
      exact hxo this.2.1
    · simp only [List.headD_cons] at hhead
      subst hhead
      have hyx : KingStep y a := (List.isChain_cons_cons.1 hchain).1.symm
      have hyU : y ∈ U.erase a :=
        Finset.mem_erase.2 ⟨hyx.1, hpxU y (by simp)⟩
      rw [← hpU, List.mem_toFinset] at hyU
      obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hyU
      refine ⟨p₁ ++ y :: a :: y :: p₂, ?_, ?_⟩
      · have := detour_mem_kingWalks hp hyx
        have h2 : 2 * (n + 1) = 2 * n + 2 := by ring
        rw [h2]
        exact this
      · rw [← Finset.insert_erase hxU, ← hpU]
        ext z
        simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
          List.mem_toFinset]
        tauto

/-- The family of king-connected sets of `n + 1` sites containing `o` has at most `64 ^ n`
members. -/
theorem exists_animal_family (o : ℤ × ℤ) (n : ℕ) :
    ∃ 𝒰 : Finset (Finset (ℤ × ℤ)), 𝒰.card ≤ 64 ^ n ∧
      ∀ U, KConn o U → U.card = n + 1 → U ∈ 𝒰 := by
  refine ⟨(kingWalks o (2 * n)).image List.toFinset, ?_, fun U hK hU => ?_⟩
  · calc ((kingWalks o (2 * n)).image List.toFinset).card ≤ (kingWalks o (2 * n)).card :=
          card_image_le
      _ ≤ 8 ^ (2 * n) := card_kingWalks o _
      _ = 64 ^ n := by rw [pow_mul]; norm_num
  · obtain ⟨p, hp, hpU⟩ := exists_spanning_walk o n U hU hK
    exact mem_image.2 ⟨p, hp, hpU⟩

end Rotor
