/-
The coarse path of block indices visited by a path in the graph: consecutive vertices lie in
the same block or in king-adjacent blocks; removing repetitions and erasing loops gives a
duplicate-free king path of block indices, in the order of visits, from the block of the first
vertex to the block of the last, of length at least the sup-distance between them.
-/
import Rotor.Support.KingPaths

namespace Rotor

/-! ### Lazy king chains -/

/-- A lazy king step: stay or move by a king step. -/
def LazyKingStep (a b : ℤ × ℤ) : Prop := a = b ∨ KingStep a b

theorem destutter'_lazy : ∀ (l : List (ℤ × ℤ)) (a : ℤ × ℤ), (a :: l).IsChain LazyKingStep →
    (l.destutter' (· ≠ ·) a).IsChain KingStep ∧ (l.destutter' (· ≠ ·) a).head? = some a ∧
      (l.destutter' (· ≠ ·) a).getLast? = (a :: l).getLast? := by
  intro l
  induction l with
  | nil =>
    intro a _
    exact ⟨List.isChain_singleton _, rfl, rfl⟩
  | cons b l ih =>
    intro a hchain
    have hab : LazyKingStep a b := (List.isChain_cons_cons.1 hchain).1
    have hrest : (b :: l).IsChain LazyKingStep := (List.isChain_cons_cons.1 hchain).2
    by_cases h : a ≠ b
    · rw [List.destutter'_cons_pos _ h]
      obtain ⟨hc, hh, hl⟩ := ih b hrest
      have hk : KingStep a b := hab.resolve_left h
      refine ⟨?_, rfl, ?_⟩
      · rcases hd : l.destutter' (· ≠ ·) b with _ | ⟨c, rest⟩
        · simp [hd] at hh
        · rw [hd] at hh hc
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          exact List.isChain_cons_cons.2 ⟨hk, hc⟩
      · rcases hd : l.destutter' (· ≠ ·) b with _ | ⟨c, rest⟩
        · simp [hd] at hh
        · rw [hd] at hl
          rw [List.getLast?_cons_cons, List.getLast?_cons_cons]
          exact hl
    · push Not at h
      subst h
      rw [List.destutter'_cons_neg _ (by simp)]
      have hrest' : (a :: l).IsChain LazyKingStep := hrest
      obtain ⟨hc, hh, hl⟩ := ih a hrest'
      exact ⟨hc, hh, by rw [hl, List.getLast?_cons_cons]⟩

/-- Removing consecutive repetitions from a lazy king chain gives a king chain with the same
first and last elements. -/
theorem destutter_lazy (l : List (ℤ × ℤ)) (h : l.IsChain LazyKingStep) :
    (l.destutter (· ≠ ·)).IsChain KingStep ∧ (l.destutter (· ≠ ·)).head? = l.head? ∧
      (l.destutter (· ≠ ·)).getLast? = l.getLast? := by
  rcases l with _ | ⟨a, l⟩
  · simp
  · rw [List.destutter_cons']
    exact destutter'_lazy l a h

/-- Along a king chain the sup-distance between the first and last point is at most the
number of steps. -/
theorem linf_le_of_kingChain : ∀ (l : List (ℤ × ℤ)), l.IsChain KingStep →
    ∀ x ∈ l.head?, ∀ y ∈ l.getLast?, linf (y - x) ≤ l.length - 1 := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a l ih =>
    intro hchain x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    subst hx
    rcases l with _ | ⟨b, l⟩
    · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hy
      subst hy
      simp [linf]
    · have hab : KingStep a b := (List.isChain_cons_cons.1 hchain).1
      have := ih (List.isChain_cons_cons.1 hchain).2 b rfl y (by rwa [List.getLast?_cons_cons] at hy)
      have htri := linf_triangle y b a
      have h1 : linf (b - a) ≤ 1 := hab.2
      simp only [List.length_cons] at this ⊢
      omega

/-! ### Positions of a sublist -/

/-- Two entries of a sublist appear in the ambient list at positions in the same order. -/
theorem Sublist.exists_lt_of_lt {α : Type*} {c m : List α} (h : c.Sublist m) {i j : ℕ}
    (hij : i < j) (hj : j < c.length) :
    ∃ a b : Fin m.length, a < b ∧ m.get a = c.get ⟨i, by omega⟩ ∧ m.get b = c.get ⟨j, hj⟩ := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 h
  refine ⟨f ⟨i, by omega⟩, f ⟨j, hj⟩, ?_, (hf ⟨i, by omega⟩).symm, (hf ⟨j, hj⟩).symm⟩
  exact f.strictMono (show (⟨i, by omega⟩ : Fin c.length) < ⟨j, hj⟩ from hij)

/-! ### The coarse path of a path in the graph -/

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] (P : DoublyPeriodic G)

omit [DecidableEq V] [G.LocallyFinite] in
/-- The block indices along a path form a lazy king chain once `L` exceeds the coordinate
bound. -/
theorem blockIndex_lazyChain {K : ℤ} (hK : ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K)
    {L : ℕ} (hL : K < L) (l : List V) (hl : l.IsChain G.Adj) :
    (l.map (P.blockIndex L)).IsChain LazyKingStep := by
  rw [List.isChain_map]
  refine hl.imp (fun u v huv => ?_)
  by_cases h : P.blockIndex L u = P.blockIndex L v
  · exact Or.inl h
  · exact Or.inr ⟨h, P.linf_blockIndex_adj hK hL u v huv⟩

omit [DecidableEq V] [G.LocallyFinite] in
/-- The duplicate-free king path of block indices visited by a path, in the order of visits. -/
theorem exists_blockChain {K : ℤ} (hK : ∀ u v : V, G.Adj u v → linf (P.coord v - P.coord u) ≤ K)
    {L : ℕ} (hL : K < L) (l : List V) (hl : l.IsChain G.Adj) (hne : l ≠ []) :
    ∃ c : List (ℤ × ℤ), c.IsChain KingStep ∧ c.Nodup ∧ c.Sublist (l.map (P.blockIndex L)) ∧
      c.head? = (l.map (P.blockIndex L)).head? ∧ c.getLast? = (l.map (P.blockIndex L)).getLast? := by
  obtain ⟨hc, hh, hlast⟩ := destutter_lazy _ (blockIndex_lazyChain P hK hL l hl)
  have hne' : (l.map (P.blockIndex L)).destutter (· ≠ ·) ≠ [] := by
    intro h0
    rw [h0] at hh
    rcases l with _ | ⟨x, l⟩
    · exact hne rfl
    · simp at hh
  obtain ⟨c, hcc, hnd, hch, hcl, hsub⟩ := exists_nodup_chain KingStep _ _ le_rfl hc hne'
  exact ⟨c, hcc, hnd, hsub.trans (List.destutter_sublist _ _), hch.trans hh, hcl.trans hlast⟩

end Rotor

