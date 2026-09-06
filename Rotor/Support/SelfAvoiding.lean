import Rotor.Support.ChainWeight

/-!
The killed nonbacktracking chain as a weighted count of self-avoiding paths,
`rotor.tex:1400-1432`.  Paths are listed most recent first; `NodupExt G l n` is the set of
self-avoiding extensions of `l` by `n` vertices and `W π l n` the total weight of these
extensions, that is `P_e{the chain is not killed by step n, X_0, …, X_n distinct}` for the
chain started along `l`.  The chain is substochastic (`eq:mean-continuations`), so `W` is
antitone; a stuck extension (at most one self-avoiding continuation) within `m` steps loses a
fixed fraction of the weight, and iterating over blocks gives `eq:chain-survival`.
-/

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (π : Mechanism G)

variable (G) in
/-- The one-step self-avoiding extensions of a path listed most recent first. -/
def ext1 : List V → Finset (List V)
  | [] => ∅
  | b :: rest =>
    ((G.neighborFinset b).filter (fun c => c ∉ b :: rest)).image (fun c => c :: b :: rest)

variable (G) in
/-- The self-avoiding extensions by `n` vertices. -/
def NodupExt (l : List V) : ℕ → Finset (List V)
  | 0 => {l}
  | n + 1 => (NodupExt l n).biUnion (ext1 G)

variable (G) in
/-- A path with at least two vertices, listed most recent first. -/
def Adm (l : List V) : Prop := l.Nodup ∧ l.IsChain G.Adj ∧ 2 ≤ l.length

@[simp] theorem NodupExt_zero (l : List V) : NodupExt G l 0 = {l} := rfl
@[simp] theorem NodupExt_succ (l : List V) (n : ℕ) :
    NodupExt G l (n + 1) = (NodupExt G l n).biUnion (ext1 G) := rfl

theorem mem_ext1_cons {b c : V} {rest : List V} :
    c :: b :: rest ∈ ext1 G (b :: rest) ↔ G.Adj b c ∧ c ∉ b :: rest := by
  simp only [ext1, mem_image, mem_filter, SimpleGraph.mem_neighborFinset, List.cons.injEq,
    and_true]
  constructor
  · rintro ⟨c', ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨c, ⟨h1, h2⟩, rfl⟩

theorem exists_of_mem_ext1 {l q : List V} (h : q ∈ ext1 G l) :
    ∃ b rest c, l = b :: rest ∧ G.Adj b c ∧ c ∉ b :: rest ∧ q = c :: b :: rest := by
  match l with
  | [] => simp [ext1] at h
  | b :: rest =>
    simp only [ext1, mem_image, mem_filter, SimpleGraph.mem_neighborFinset] at h
    obtain ⟨c, ⟨h1, h2⟩, rfl⟩ := h
    exact ⟨b, rest, c, rfl, h1, h2, rfl⟩

theorem tail_of_mem_ext1 {l q : List V} (h : q ∈ ext1 G l) : q.tail = l := by
  obtain ⟨b, rest, c, rfl, -, -, rfl⟩ := exists_of_mem_ext1 h
  rfl

theorem ext1_disjoint {l l' : List V} (h : l ≠ l') : Disjoint (ext1 G l) (ext1 G l') := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  exact h ((tail_of_mem_ext1 hq).symm.trans (tail_of_mem_ext1 hq'))

theorem drop_of_mem_NodupExt {l : List V} : ∀ {n : ℕ} {q : List V}, q ∈ NodupExt G l n →
    q.drop n = l
  | 0, q, h => by simpa using h
  | n + 1, q, h => by
    rw [NodupExt_succ, mem_biUnion] at h
    obtain ⟨q', hq', hq⟩ := h
    obtain ⟨b, rest, c, rfl, -, -, rfl⟩ := exists_of_mem_ext1 hq
    rw [List.drop_succ_cons]
    exact drop_of_mem_NodupExt hq'

theorem length_of_mem_NodupExt {l : List V} : ∀ {n : ℕ} {q : List V}, q ∈ NodupExt G l n →
    q.length = l.length + n
  | 0, q, h => by simp at h; subst h; rfl
  | n + 1, q, h => by
    rw [NodupExt_succ, mem_biUnion] at h
    obtain ⟨q', hq', hq⟩ := h
    obtain ⟨b, rest, c, rfl, -, -, rfl⟩ := exists_of_mem_ext1 hq
    have := length_of_mem_NodupExt hq'
    simp only [List.length_cons] at this ⊢
    omega

theorem adm_of_mem_NodupExt {l : List V} (hl : Adm G l) : ∀ {n : ℕ} {q : List V},
    q ∈ NodupExt G l n → Adm G q
  | 0, q, h => by simp at h; subst h; exact hl
  | n + 1, q, h => by
    rw [NodupExt_succ, mem_biUnion] at h
    obtain ⟨q', hq', hq⟩ := h
    obtain ⟨hnd, hch, hlen⟩ := adm_of_mem_NodupExt hl hq'
    obtain ⟨b, rest, c, rfl, hadj, hc, rfl⟩ := exists_of_mem_ext1 hq
    refine ⟨List.nodup_cons.2 ⟨hc, hnd⟩, ?_, by simp only [List.length_cons] at hlen ⊢; omega⟩
    exact List.isChain_cons.2 ⟨fun y hy => by simp at hy; subst hy; exact hadj.symm, hch⟩

theorem NodupExt_add (l : List V) (j : ℕ) : ∀ n : ℕ,
    NodupExt G l (j + n) = (NodupExt G l j).biUnion (fun q => NodupExt G q n)
  | 0 => by simp
  | n + 1 => by
    rw [← add_assoc, NodupExt_succ, NodupExt_add l j n, biUnion_biUnion]
    rfl

theorem NodupExt_disjoint {q q' : List V} (hne : q ≠ q') (n : ℕ) :
    Disjoint (NodupExt G q n) (NodupExt G q' n) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact hne ((drop_of_mem_NodupExt hx).symm.trans (drop_of_mem_NodupExt hx'))

theorem pairwiseDisjoint_NodupExt (l : List V) (j n : ℕ) :
    ((NodupExt G l j : Set (List V))).PairwiseDisjoint (fun q => NodupExt G q n) :=
  fun _ _ _ _ hne => NodupExt_disjoint hne n

/-- The total weight of the self-avoiding extensions by `n` vertices. -/
noncomputable def W (l : List V) (n : ℕ) : ℝ := ∑ q ∈ NodupExt G l n, wt π q

@[simp] theorem W_zero (l : List V) : W π l 0 = wt π l := by simp [W]

theorem W_add (l : List V) (j n : ℕ) : W π l (j + n) = ∑ q ∈ NodupExt G l j, W π q n := by
  rw [W, NodupExt_add, sum_biUnion (pairwiseDisjoint_NodupExt l j n)]
  rfl

theorem W_one (b a : V) (rest : List V) : W π (b :: a :: rest) 1 =
    wt π (b :: a :: rest) *
      ∑ c ∈ (G.neighborFinset b).filter (fun c => c ∉ b :: a :: rest), pStep π a b c := by
  rw [W, NodupExt_succ, NodupExt_zero, singleton_biUnion, ext1, sum_image, mul_sum]
  · simp only [wt_cons₃, mul_comm]
  · intro x _ y _ hxy
    simpa using hxy

theorem sum_pStep_filter_le {a b : V} (h3 : G.degree b ≤ 3) (hab : G.Adj b a)
    (P : V → Prop) [DecidablePred P] :
    ∑ c ∈ (G.neighborFinset b).filter P, pStep π a b c ≤ 1 := by
  calc ∑ c ∈ (G.neighborFinset b).filter P, pStep π a b c
      ≤ ∑ c ∈ G.neighborFinset b, pStep π a b c :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun c _ _ => pStep_nonneg π a b c)
    _ = ((G.degree b : ℝ) - 1) / 2 := sum_pStep π hab
    _ ≤ 1 := by
        have : (G.degree b : ℝ) ≤ 3 := by exact_mod_cast h3
        linarith

theorem W_one_le (h3 : ∀ v : V, G.degree v ≤ 3) {q : List V} (hq : Adm G q) : W π q 1 ≤ wt π q := by
  obtain ⟨hnd, hch, hlen⟩ := hq
  match q with
  | [] => simp at hlen
  | [_] => simp at hlen
  | b :: a :: rest =>
    rw [W_one]
    have hab : G.Adj b a := hch.rel_head
    calc wt π (b :: a :: rest) * ∑ c ∈ (G.neighborFinset b).filter (fun c => c ∉ b :: a :: rest),
          pStep π a b c ≤ wt π (b :: a :: rest) * 1 :=
          mul_le_mul_of_nonneg_left (sum_pStep_filter_le π (h3 b) hab _) (wt_nonneg π _)
      _ = wt π (b :: a :: rest) := mul_one _

theorem W_succ_le (h3 : ∀ v : V, G.degree v ≤ 3) {l : List V} (hl : Adm G l) (n : ℕ) :
    W π l (n + 1) ≤ W π l n := by
  rw [W_add, W]
  exact sum_le_sum (fun q hq => W_one_le π h3 (adm_of_mem_NodupExt hl hq))

theorem W_le_wt (h3 : ∀ v : V, G.degree v ≤ 3) {l : List V} (hl : Adm G l) : ∀ n : ℕ,
    W π l n ≤ wt π l
  | 0 => by simp
  | n + 1 => (W_succ_le π h3 hl n).trans (W_le_wt h3 hl n)

theorem W_antitone (h3 : ∀ v : V, G.degree v ≤ 3) {l : List V} (hl : Adm G l) {n n' : ℕ}
    (h : n ≤ n') : W π l n' ≤ W π l n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [W_add, W]
  exact sum_le_sum (fun q hq => W_le_wt π h3 (adm_of_mem_NodupExt hl hq) k)

theorem wt_ge_of_mem_NodupExt (h3 : ∀ v : V, G.degree v ≤ 3) {l : List V} (hl : Adm G l) :
    ∀ {j : ℕ} {q : List V}, q ∈ NodupExt G l j → (1 / 3 : ℝ) ^ j * wt π l ≤ wt π q
  | 0, q, h => by simp at h; subst h; simp
  | j + 1, q, h => by
    rw [NodupExt_succ, mem_biUnion] at h
    obtain ⟨q', hq', hq⟩ := h
    have hadm := adm_of_mem_NodupExt hl hq'
    have hrec := wt_ge_of_mem_NodupExt h3 hl hq'
    obtain ⟨b, rest, c, rfl, hadj, hc, rfl⟩ := exists_of_mem_ext1 hq
    obtain ⟨-, hch, hlen⟩ := hadm
    match rest with
    | [] => simp at hlen
    | a :: rest =>
      rw [wt_cons₃, pow_succ]
      have hab : G.Adj b a := hch.rel_head
      have hne : c ≠ a := fun h => hc (by simp [h])
      have hp : (1 / 3 : ℝ) ≤ pStep π a b c := by
        refine le_trans ?_ (one_div_degree_le_pStep π hab hadj hne)
        have h1 : (1 : ℝ) ≤ G.degree b := by
          have := (SimpleGraph.degree_pos_iff_exists_adj G b).2 ⟨a, hab⟩
          exact_mod_cast this
        have h2 : (G.degree b : ℝ) ≤ 3 := by exact_mod_cast h3 b
        rw [div_le_div_iff_of_pos_left one_pos (by linarith) (by linarith)]
        exact h2
      calc (1 / 3 : ℝ) ^ j * (1 / 3) * wt π l
          = (1 / 3) * ((1 / 3 : ℝ) ^ j * wt π l) := by ring
        _ ≤ pStep π a b c * wt π (b :: a :: rest) :=
          mul_le_mul hp hrec (mul_nonneg (by positivity) (wt_nonneg π _)) (pStep_nonneg π a b c)

variable (G) in
/-- A path with at most one self-avoiding continuation. -/
def Stuck (q : List V) : Prop :=
  ∃ b rest, q = b :: rest ∧ ((G.neighborFinset b).filter (fun c => c ∉ q)).card ≤ 1

theorem card_stepSet_le_pred (b : V) (a c : G.neighborSet b) :
    (stepSet π b a c).card ≤ G.degree b - 1 := by
  have hc : c ∉ stepSet π b a c := by
    simp only [stepSet, mem_filter, mem_univ, true_and, not_lt]
    rw [cycRank_self]
    exact cycRank_le _ _ _ _
  calc (stepSet π b a c).card ≤ (univ.erase c).card :=
        card_le_card (subset_erase.2 ⟨subset_univ _, hc⟩)
    _ = G.degree b - 1 := by rw [card_erase_of_mem (mem_univ c), card_univ,
        G.card_neighborSet_eq_degree]

theorem pStep_le_two_thirds {a b c : V} (h3 : G.degree b ≤ 3) : pStep π a b c ≤ 2 / 3 := by
  unfold pStep
  split_ifs with h
  · have hd : 1 ≤ G.degree b := (SimpleGraph.degree_pos_iff_exists_adj G b).2 ⟨a, h.1⟩
    have hcard := card_stepSet_le_pred π b ⟨a, h.1⟩ ⟨c, h.2⟩
    have h1 : ((stepSet π b ⟨a, h.1⟩ ⟨c, h.2⟩).card : ℝ) ≤ (G.degree b : ℝ) - 1 := by
      have := (Nat.cast_le (α := ℝ)).2 hcard
      rwa [Nat.cast_sub hd, Nat.cast_one] at this
    have hd' : (0 : ℝ) < G.degree b := by exact_mod_cast hd
    have h3' : (G.degree b : ℝ) ≤ 3 := by exact_mod_cast h3
    rw [div_le_iff₀ hd']
    linarith
  · positivity

theorem W_one_le_of_stuck (h3 : ∀ v : V, G.degree v ≤ 3) {q : List V} (hq : Adm G q)
    (hs : Stuck G q) : W π q 1 ≤ 2 / 3 * wt π q := by
  obtain ⟨hnd, hch, hlen⟩ := hq
  match q with
  | [] => simp at hlen
  | [_] => simp at hlen
  | b :: a :: rest =>
    obtain ⟨b', rest', hq', hcard⟩ := hs
    simp only [List.cons.injEq] at hq'
    obtain ⟨rfl, rfl⟩ := hq'
    rw [W_one, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (wt_nonneg π _)
    calc ∑ c ∈ (G.neighborFinset b).filter (fun c => c ∉ b :: a :: rest), pStep π a b c
        ≤ ((G.neighborFinset b).filter (fun c => c ∉ b :: a :: rest)).card • (2 / 3 : ℝ) :=
          sum_le_card_nsmul _ _ _ (fun c _ => pStep_le_two_thirds π (h3 b))
      _ ≤ 2 / 3 := by
          rw [nsmul_eq_mul]
          have : (((G.neighborFinset b).filter (fun c => c ∉ b :: a :: rest)).card : ℝ) ≤ 1 := by
            exact_mod_cast hcard
          linarith

/-- One block: a stuck extension within `m` steps loses a third of the weight `3^{-m}`. -/
theorem W_block (h3 : ∀ v : V, G.degree v ≤ 3) {l : List V} (hl : Adm G l) {m j : ℕ} (hj : j ≤ m)
    {q : List V} (hq : q ∈ NodupExt G l j) (hs : Stuck G q) :
    W π l (m + 1) ≤ (1 - (1 / 3 : ℝ) ^ m / 3) * wt π l := by
  have hadm := adm_of_mem_NodupExt hl hq
  have hsplit : m + 1 = j + (m + 1 - j) := by omega
  rw [hsplit, W_add, ← add_sum_erase _ _ hq]
  have h1 : W π q (m + 1 - j) ≤ 2 / 3 * wt π q :=
    (W_antitone π h3 hadm (by omega : 1 ≤ m + 1 - j)).trans (W_one_le_of_stuck π h3 hadm hs)
  have h2 : ∑ q' ∈ (NodupExt G l j).erase q, W π q' (m + 1 - j)
      ≤ ∑ q' ∈ (NodupExt G l j).erase q, wt π q' :=
    sum_le_sum (fun q' hq' => W_le_wt π h3 (adm_of_mem_NodupExt hl (mem_of_mem_erase hq')) _)
  have h3' : ∑ q' ∈ (NodupExt G l j).erase q, wt π q' = W π l j - wt π q := by
    rw [W, sum_erase_eq_sub hq]
  have h4 : W π l j ≤ wt π l := W_le_wt π h3 hl j
  have h5 : (1 / 3 : ℝ) ^ j * wt π l ≤ wt π q := wt_ge_of_mem_NodupExt π h3 hl hq
  have h6 : (1 / 3 : ℝ) ^ m ≤ (1 / 3) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have h8 : (1 / 3 : ℝ) ^ m * wt π l ≤ wt π q :=
    (mul_le_mul_of_nonneg_right h6 (wt_nonneg π l)).trans h5
  linarith

/-- `eq:chain-survival` over `n` blocks of `m + 1` steps. -/
theorem W_blocks (h3 : ∀ v : V, G.degree v ≤ 3) {m : ℕ}
    (hstuck : ∀ q : List V, Adm G q → ∃ j ≤ m, ∃ q' ∈ NodupExt G q j, Stuck G q')
    {l : List V} (hl : Adm G l) : ∀ n : ℕ,
    W π l (n * (m + 1)) ≤ (1 - (1 / 3 : ℝ) ^ m / 3) ^ n * wt π l
  | 0 => by simp
  | n + 1 => by
    rw [add_mul, one_mul, W_add, pow_succ]
    have hθ : 0 ≤ 1 - (1 / 3 : ℝ) ^ m / 3 := by
      have : (1 / 3 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    calc ∑ q ∈ NodupExt G l (n * (m + 1)), W π q (m + 1)
        ≤ ∑ q ∈ NodupExt G l (n * (m + 1)), (1 - (1 / 3 : ℝ) ^ m / 3) * wt π q := by
          refine sum_le_sum (fun q hq => ?_)
          have hadm := adm_of_mem_NodupExt hl hq
          obtain ⟨j, hj, q', hq', hs⟩ := hstuck q hadm
          exact W_block π h3 hadm hj hq' hs
      _ = (1 - (1 / 3 : ℝ) ^ m / 3) * W π l (n * (m + 1)) := by rw [W, mul_sum]
      _ ≤ (1 - (1 / 3 : ℝ) ^ m / 3) * ((1 - (1 / 3 : ℝ) ^ m / 3) ^ n * wt π l) :=
          mul_le_mul_of_nonneg_left (W_blocks h3 hstuck hl n) hθ
      _ = (1 - (1 / 3 : ℝ) ^ m / 3) ^ n * (1 - (1 / 3 : ℝ) ^ m / 3) * wt π l := by ring

end Rotor
