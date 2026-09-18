/-
King paths on `ℤ²`: the coarse paths of block indices in the proof of
`lem:block-live-paths` (`rotor.tex:1268-1273`): "A self-avoiding sequence of block indices
has at most seven continuations at each step."  Loop erasure of a chain, and the count of
non-backtracking king sequences.
-/
import Rotor.Support.BlockGeom

open Finset

namespace Rotor

/-! ### Loop erasure of a chain -/

/-- From a chain one extracts a duplicate-free chain with the same first and last element,
using only elements of the original. -/
theorem exists_nodup_chain {α : Type*} (R : α → α → Prop) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l.IsChain R → l ≠ [] →
      ∃ m : List α, m.IsChain R ∧ m.Nodup ∧ m.head? = l.head? ∧ m.getLast? = l.getLast? ∧
        m.Sublist l := by
  intro n
  induction n with
  | zero =>
    intro l hl _ hne
    exact absurd (List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)) hne
  | succ n ih =>
    intro l hl hchain hne
    rcases l with _ | ⟨x, rest⟩
    · exact absurd rfl hne
    by_cases hx : x ∈ rest
    · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hx
      have hl' : (x :: rest) = (x :: pre) ++ (x :: post) := by rw [hsplit]; rfl
      have hchain' : (x :: post).IsChain R := by
        rw [hl', List.isChain_append] at hchain
        exact hchain.2.1
      have hlen : (x :: post).length ≤ n := by
        have := congrArg List.length hl'
        simp only [List.length_cons, List.length_append] at this hl ⊢
        omega
      obtain ⟨m, hm, hnd, hh, hlast, hsub⟩ := ih (x :: post) hlen hchain' (List.cons_ne_nil _ _)
      refine ⟨m, hm, hnd, ?_, ?_, ?_⟩
      · rw [hh]; rfl
      · rw [hlast, hl', List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      · rw [hl']
        exact hsub.trans (List.sublist_append_right _ _)
    · rcases rest with _ | ⟨y, rest'⟩
      · exact ⟨[x], List.isChain_singleton _, List.nodup_singleton _, rfl, rfl, List.Sublist.refl _⟩
      have hchain' : (y :: rest').IsChain R := (List.isChain_cons_cons.1 hchain).2
      have hxy : R x y := (List.isChain_cons_cons.1 hchain).1
      have hlen : (y :: rest').length ≤ n := by
        simp only [List.length_cons] at hl ⊢; omega
      obtain ⟨m, hm, hnd, hh, hlast, hsub⟩ := ih (y :: rest') hlen hchain' (List.cons_ne_nil _ _)
      rcases m with _ | ⟨y', m'⟩
      · simp at hh
      have hyy : y' = y := by simpa using hh
      subst hyy
      refine ⟨x :: y' :: m', List.isChain_cons_cons.2 ⟨hxy, hm⟩, ?_, rfl, ?_, ?_⟩
      · exact List.nodup_cons.2 ⟨fun hmem => hx (hsub.subset hmem), hnd⟩
      · rw [List.getLast?_cons_cons, hlast]
        rfl
      · exact hsub.cons_cons x

/-! ### King steps and non-backtracking king sequences -/

/-- A king step: a move to a different point with each coordinate changing by at most one. -/
def KingStep (a b : ℤ × ℤ) : Prop := a ≠ b ∧ linf (b - a) ≤ 1

instance : DecidableRel KingStep := fun a b => by unfold KingStep; infer_instance

theorem KingStep.symm {a b : ℤ × ℤ} (h : KingStep a b) : KingStep b a :=
  ⟨h.1.symm, by rw [linf_sub_comm]; exact h.2⟩

/-- The eight king neighbors of a point. -/
noncomputable def kingNbrs (a : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-1 : ℤ) 1) ×ˢ (Finset.Icc (-1 : ℤ) 1)).image (fun d => a + d) \ {a}

theorem mem_kingNbrs {a b : ℤ × ℤ} : b ∈ kingNbrs a ↔ KingStep a b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [kingNbrs, Finset.mem_sdiff, Finset.mem_image, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_singleton, KingStep, linf_le_iff, abs_le, Prod.mk.injEq, Prod.mk_add_mk,
    Prod.mk_sub_mk, Prod.exists, ne_eq, not_and]
  constructor
  · rintro ⟨⟨d1, d2, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl, rfl⟩, hne⟩
    refine ⟨fun h1' h2' => hne ?_ ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
  · rintro ⟨hne, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
    refine ⟨⟨b1 - a1, b2 - a2, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩, fun h1' h2' => hne ?_ ?_⟩ <;> omega

theorem card_kingNbrs (a : ℤ × ℤ) : (kingNbrs a).card = 8 := by
  unfold kingNbrs
  have hmem : {a} ∩ ((Finset.Icc (-1 : ℤ) 1) ×ˢ (Finset.Icc (-1 : ℤ) 1)).image (fun d => a + d) = {a} := by
    refine Finset.inter_eq_left.2 (Finset.singleton_subset_iff.2 ?_)
    exact Finset.mem_image.2 ⟨0, by simp, by simp⟩
  rw [Finset.card_sdiff, hmem, Finset.card_image_of_injective _ (add_right_injective a)]
  simp

/-- The non-backtracking king sequences of `m` steps from `a`, stored most recent first: lists
of length `m + 1` ending in `a`, consecutive king steps, never returning to the point before
the last. -/
noncomputable def kingSeqs (a : ℤ × ℤ) : ℕ → Finset (List (ℤ × ℤ))
  | 0 => {[a]}
  | m + 1 => (kingSeqs a m).biUnion (fun p =>
      ((kingNbrs (p.headD a)).filter (fun b => ∀ c ∈ p.tail.head?, b ≠ c)).image
        (fun b => b :: p))

theorem mem_kingSeqs (a : ℤ × ℤ) (m : ℕ) {p : List (ℤ × ℤ)} (hp : p ∈ kingSeqs a m) :
    p.length = m + 1 ∧ p.IsChain KingStep := by
  induction m generalizing p with
  | zero =>
    simp only [kingSeqs, Finset.mem_singleton] at hp
    subst hp
    exact ⟨rfl, List.isChain_singleton _⟩
  | succ m ih =>
    simp only [kingSeqs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hp
    obtain ⟨q, hq, b, ⟨hb, -⟩, rfl⟩ := hp
    obtain ⟨hlen, hchain⟩ := ih hq
    refine ⟨by simp [hlen], ?_⟩
    rcases q with _ | ⟨c, q'⟩
    · simp at hlen
    · rw [List.headD_cons] at hb
      exact List.isChain_cons_cons.2 ⟨(mem_kingNbrs.1 hb).symm, hchain⟩

theorem card_kingSeqs (a : ℤ × ℤ) (m : ℕ) : (kingSeqs a m).card ≤ 8 * 7 ^ m := by
  induction m with
  | zero => simp [kingSeqs]
  | succ m ih =>
    rw [kingSeqs]
    refine (Finset.card_biUnion_le).trans ?_
    have hbound : ∀ p ∈ kingSeqs a m,
        (((kingNbrs (p.headD a)).filter (fun b => ∀ c ∈ p.tail.head?, b ≠ c)).image
          (fun b => b :: p)).card ≤ (if m = 0 then 8 else 7) := by
      intro p hp
      refine Finset.card_image_le.trans ?_
      obtain ⟨hlen, hchain⟩ := mem_kingSeqs a m hp
      rcases m with _ | m
      · simp only [if_true]
        exact Finset.card_filter_le _ _ |>.trans (card_kingNbrs _).le
      · simp only [Nat.succ_ne_zero, if_false]
        -- `p = ℓ :: c :: q` with `KingStep ℓ c`, and the filter excludes `c`
        rcases p with _ | ⟨ℓ, q⟩
        · simp at hlen
        rcases q with _ | ⟨c, q'⟩
        · simp at hlen
        have hlc : KingStep ℓ c := (List.isChain_cons_cons.1 hchain).1
        have hc : c ∈ kingNbrs ℓ := mem_kingNbrs.2 hlc
        have hsub : (kingNbrs ℓ).filter (fun b => ∀ c' ∈ (c :: q').head?, b ≠ c') ⊆
            (kingNbrs ℓ).erase c := by
          intro b hb
          rw [Finset.mem_filter] at hb
          rw [Finset.mem_erase]
          exact ⟨hb.2 c rfl, hb.1⟩
        calc ((kingNbrs ((ℓ :: c :: q').headD a)).filter
              (fun b => ∀ c' ∈ (ℓ :: c :: q').tail.head?, b ≠ c')).card
            = ((kingNbrs ℓ).filter (fun b => ∀ c' ∈ (c :: q').head?, b ≠ c')).card := rfl
          _ ≤ ((kingNbrs ℓ).erase c).card := Finset.card_le_card hsub
          _ = 7 := by rw [Finset.card_erase_of_mem hc, card_kingNbrs]
    calc ∑ p ∈ kingSeqs a m, (((kingNbrs (p.headD a)).filter
          (fun b => ∀ c ∈ p.tail.head?, b ≠ c)).image (fun b => b :: p)).card
        ≤ ∑ _p ∈ kingSeqs a m, (if m = 0 then 8 else 7) := Finset.sum_le_sum hbound
      _ = (kingSeqs a m).card * (if m = 0 then 8 else 7) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 8 * 7 ^ (m + 1) := by
          rcases m with _ | m
          · simp [kingSeqs]
          · simp only [Nat.succ_ne_zero, if_false]
            rw [pow_succ]
            nlinarith [ih]

/-- Every duplicate-free king path of `m` steps starting at `a`, read backwards, is a
non-backtracking king sequence. -/
theorem reverse_mem_kingSeqs (a : ℤ × ℤ) :
    ∀ (m : ℕ) (l : List (ℤ × ℤ)), l.length = m + 1 → l.head? = some a → l.IsChain KingStep →
      l.Nodup → l.reverse ∈ kingSeqs a m := by
  intro m
  induction m with
  | zero =>
    intro l hlen hhead _ _
    rcases l with _ | ⟨x, rest⟩
    · simp at hhead
    · have : rest = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hlen; omega)
      subst this
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      simp [kingSeqs]
  | succ m ih =>
    intro l hlen hhead hchain hnd
    -- split off the last element
    obtain ⟨l', b, rfl⟩ : ∃ l' b, l = l' ++ [b] :=
      ⟨l.dropLast, l.getLast (by rintro rfl; simp at hlen), (List.dropLast_append_getLast _).symm⟩
    have hlen' : l'.length = m + 1 := by simp at hlen; omega
    have hne : l' ≠ [] := by rintro rfl; simp at hlen'
    have hhead' : l'.head? = some a := by rwa [List.head?_append_of_ne_nil _ hne] at hhead
    rw [List.isChain_append] at hchain
    have hnd' := hnd.of_append_left
    have hmem := ih l' hlen' hhead' hchain.1 hnd'
    have hchain_step : ∀ x ∈ l'.getLast?, KingStep x b := by
      intro x hx
      exact hchain.2.2 x hx b rfl
    simp only [kingSeqs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    refine ⟨l'.reverse, hmem, b, ⟨?_, ?_⟩, rfl⟩
    · have hrev : l'.reverse.headD a = l'.getLast hne := by
        rw [List.headD_eq_head?, List.head?_reverse, List.getLast?_eq_some_getLast hne]
        rfl
      rw [hrev]
      exact mem_kingNbrs.2 (hchain_step _ (List.getLast?_eq_some_getLast hne))
    · have hbl : b ∉ l' := by
        have := (List.nodup_append.1 hnd).2.2
        exact fun hb => this b hb b (List.mem_singleton_self b) rfl
      intro c hc
      have hc' : c ∈ l' := List.mem_reverse.1 (List.mem_of_mem_tail (List.mem_of_mem_head? hc))
      exact fun h => hbl (h ▸ hc')

/-- The number of duplicate-free king paths of `m` steps from `a` is at most `8 · 7^m`. -/
theorem ncard_nodup_kingPaths_le (a : ℤ × ℤ) (m : ℕ) :
    {l : List (ℤ × ℤ) | l.length = m + 1 ∧ l.head? = some a ∧ l.IsChain KingStep ∧ l.Nodup}.ncard ≤
      8 * 7 ^ m := by
  have hsub : List.reverse '' {l : List (ℤ × ℤ) | l.length = m + 1 ∧ l.head? = some a ∧
      l.IsChain KingStep ∧ l.Nodup} ⊆ ↑(kingSeqs a m) := by
    rintro _ ⟨l, ⟨hlen, hhead, hchain, hnd⟩, rfl⟩
    exact reverse_mem_kingSeqs a m l hlen hhead hchain hnd
  rw [← Set.ncard_image_of_injective _ List.reverse_injective]
  exact (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
    (by rw [Set.ncard_coe_finset]; exact card_kingSeqs a m)

end Rotor
