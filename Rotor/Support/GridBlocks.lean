import Rotor.Support.BlockRoute

open Finset

namespace Rotor

/-! ### Adjacency by cases, translation -/

theorem adj_unit_cases {v w : Site} (h : squareGraph.Adj v w) :
    (w.1 = v.1 + 1 ∧ w.2 = v.2) ∨ (w.1 = v.1 - 1 ∧ w.2 = v.2) ∨
    (w.1 = v.1 ∧ w.2 = v.2 + 1) ∨ (w.1 = v.1 ∧ w.2 = v.2 - 1) := by
  rw [squareGraph_adj] at h
  rcases abs_cases (v.1 - w.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (v.2 - w.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

theorem adj_add_right_iff (u v c : Site) : squareGraph.Adj (u + c) (v + c) ↔ squareGraph.Adj u v := by
  rw [squareGraph_adj, squareGraph_adj]
  simp only [Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub]

theorem isPath_map_add {l : List Site} (h : IsPath squareGraph l) (c : Site) :
    IsPath squareGraph (l.map (· + c)) := by
  refine ⟨h.1.map (add_left_injective c), ?_⟩
  rw [List.isChain_map]
  exact h.2.imp (fun a b hab => (adj_add_right_iff a b c).2 hab)

theorem traverses_map {l q : List Site} (h : Traverses l q) (f : Site → Site) :
    Traverses (l.map f) (q.map f) := by
  obtain ⟨i, h⟩ := h
  refine ⟨i, ?_⟩
  rw [List.length_map, ← List.map_drop, ← List.map_take, ← List.map_reverse]
  rcases h with h | h
  · left; rw [h]
  · right; rw [h]

/-! ### The fixed block -/

theorem mem_bd4 (v : Site) : v ∈ bd4 ↔ inBox4 v ∧ (v.1 = 0 ∨ v.1 = 4 ∨ v.2 = 0 ∨ v.2 = 4) := by
  obtain ⟨a, b⟩ := v
  constructor
  · intro h
    simp only [bd4, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    unfold inBox4; omega
  · rintro ⟨⟨h1, h2, h3, h4⟩, h⟩
    simp only at h1 h2 h3 h4 h
    interval_cases a <;> interval_cases b <;> first | decide | omega

theorem bd4_length : bd4.length = 16 := rfl

theorem route_of_mem {s t : Site} (hs : s ∈ bd4) (ht : t ∈ bd4) (hne : s ≠ t) :
    ∃ l, OkRoute l s t := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hs
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ht
  have hi' : i < 16 := bd4_length ▸ hi
  have hj' : j < 16 := bd4_length ▸ hj
  have hij : (⟨i, hi'⟩ : Fin 16) ≠ ⟨j, hj'⟩ := by
    intro h
    apply hne
    simp only [Fin.mk.injEq] at h
    subst h
    rfl
  obtain ⟨l, -, hl⟩ := route_table ⟨i, hi'⟩ ⟨j, hj'⟩ hij
  refine ⟨l, ?_⟩
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hl

/-! ### Blocks -/

/-- The corner of block `z` in the grid with vertical lines through `x` and horizontal lines
through `y`. -/
def blockCorner (x y : Site) (z : ℤ × ℤ) : Site := (x.1 + 4 * z.1, y.2 + 4 * z.2)

/-- The closed block with corner `c`. -/
def InBlock (c v : Site) : Prop := c.1 ≤ v.1 ∧ v.1 ≤ c.1 + 4 ∧ c.2 ≤ v.2 ∧ v.2 ≤ c.2 + 4

/-- The boundary of the block with corner `c`. -/
def OnBdry (c v : Site) : Prop :=
  InBlock c v ∧ (v.1 = c.1 ∨ v.1 = c.1 + 4 ∨ v.2 = c.2 ∨ v.2 = c.2 + 4)

/-- The interior of the block with corner `c`. -/
def InteriorB (c v : Site) : Prop := c.1 < v.1 ∧ v.1 < c.1 + 4 ∧ c.2 < v.2 ∧ v.2 < c.2 + 4

/-- The copy of `P⋆` in the block with corner `c`. -/
def copyAt (c : Site) : List Site := copy0.map (· + c)

theorem copyAt_length (c : Site) : (copyAt c).length = 6 := by
  simp [copyAt, copy0, pstar]

theorem interiorB_of_mem_copyAt {c v : Site} (h : v ∈ copyAt c) : InteriorB c v := by
  simp only [copyAt, copy0, pstar, List.map_map, List.mem_map, List.mem_cons, List.mem_nil_iff,
    or_false, Function.comp] at h
  unfold InteriorB
  rcases h with ⟨u, hu, rfl⟩
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem inBlock_of_interiorB {c v : Site} (h : InteriorB c v) : InBlock c v := by
  unfold InteriorB at h; unfold InBlock; omega

theorem not_onBdry_of_interiorB {c v : Site} (h : InteriorB c v) : ¬ OnBdry c v := by
  unfold InteriorB at h; unfold OnBdry InBlock; omega

theorem onBdry_of_adj_not {c v w : Site} (hv : InBlock c v) (hw : ¬ InBlock c w)
    (h : squareGraph.Adj v w) : OnBdry c v := by
  have := adj_unit_cases h
  unfold InBlock at hv hw; unfold OnBdry InBlock; omega

theorem interiorB_unique (x y : Site) {z z' : ℤ × ℤ} {v : Site}
    (h : InteriorB (blockCorner x y z) v) (h' : InteriorB (blockCorner x y z') v) : z = z' := by
  unfold InteriorB blockCorner at h h'
  exact Prod.ext (by omega) (by omega)

theorem onBdry_of_col (x y : Site) (z : ℤ × ℤ) {v : Site} (hv : InBlock (blockCorner x y z) v)
    (hcol : v.1 = x.1) : OnBdry (blockCorner x y z) v := by
  unfold InBlock blockCorner at hv; unfold OnBdry InBlock blockCorner; omega

theorem onBdry_of_row (x y : Site) (z : ℤ × ℤ) {v : Site} (hv : InBlock (blockCorner x y z) v)
    (hrow : v.2 = y.2) : OnBdry (blockCorner x y z) v := by
  unfold InBlock blockCorner at hv; unfold OnBdry InBlock blockCorner; omega

/-- The route through a block: from one boundary vertex to another through the copy. -/
theorem block_route (c : Site) {s t : Site} (hs : OnBdry c s) (ht : OnBdry c t) (hne : s ≠ t) :
    ∃ l : List Site, IsPath squareGraph l ∧ l.head? = some s ∧ l.getLast? = some t ∧
      (∀ v ∈ l, InBlock c v) ∧ Traverses l (copyAt c) := by
  have hs' : s - c ∈ bd4 := by
    rw [mem_bd4]; unfold OnBdry InBlock at hs; unfold inBox4
    simp only [Prod.fst_sub, Prod.snd_sub]; omega
  have ht' : t - c ∈ bd4 := by
    rw [mem_bd4]; unfold OnBdry InBlock at ht; unfold inBox4
    simp only [Prod.fst_sub, Prod.snd_sub]; omega
  obtain ⟨l, hl⟩ := route_of_mem hs' ht' (fun h => hne (sub_left_injective h))
  obtain ⟨hpath, hhead, hlast, hbox, i, -, hcp⟩ := hl
  refine ⟨l.map (· + c), isPath_map_add hpath c, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, hhead]; simp
  · rw [List.getLast?_map, hlast]; simp
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
    have := hbox u hu
    unfold inBox4 at this; unfold InBlock; simp only [Prod.fst_add, Prod.snd_add]; omega
  · refine ⟨i, ?_⟩
    rw [copyAt_length, ← List.map_drop, ← List.map_take]
    unfold copyAt
    rcases hcp with h | h
    · left; rw [h]
    · right; rw [← List.map_reverse, h]

/-! ### The box `D`, the block indices `Z`, the bonds `F` -/

/-- The block indices. -/
def Zset (r : ℕ) : Finset (ℤ × ℤ) := Icc (-(r : ℤ)) (r - 1) ×ˢ Icc (-(r : ℤ)) (r - 1)

/-- The box tiled by the blocks. -/
def Dset (x y : Site) (r : ℕ) : Finset Site :=
  Icc (x.1 - 4 * r) (x.1 + 4 * r) ×ˢ Icc (y.2 - 4 * r) (y.2 + 4 * r)

/-- The bonds of the box. -/
def Fset (x y : Site) (r : ℕ) : Finset (Sym2 Site) :=
  ((Dset x y r ×ˢ Dset x y r).filter (fun p => squareGraph.Adj p.1 p.2)).image
    (fun p => s(p.1, p.2))

theorem mem_Dset {x y : Site} {r : ℕ} {v : Site} : v ∈ Dset x y r ↔
    x.1 - 4 * r ≤ v.1 ∧ v.1 ≤ x.1 + 4 * r ∧ y.2 - 4 * r ≤ v.2 ∧ v.2 ≤ y.2 + 4 * r := by
  simp [Dset, and_assoc]

theorem mem_Zset {r : ℕ} {z : ℤ × ℤ} : z ∈ Zset r ↔
    -(r : ℤ) ≤ z.1 ∧ z.1 ≤ r - 1 ∧ -(r : ℤ) ≤ z.2 ∧ z.2 ≤ r - 1 := by
  simp [Zset, and_assoc]

theorem mem_Fset {x y : Site} {r : ℕ} {b : Sym2 Site} : b ∈ Fset x y r ↔
    ∃ u v, u ∈ Dset x y r ∧ v ∈ Dset x y r ∧ squareGraph.Adj u v ∧ b = s(u, v) := by
  unfold Fset
  rw [mem_image]
  constructor
  · rintro ⟨⟨u, v⟩, hp, rfl⟩
    rw [mem_filter, mem_product] at hp
    exact ⟨u, v, hp.1.1, hp.1.2, hp.2, rfl⟩
  · rintro ⟨u, v, hu, hv, h, rfl⟩
    exact ⟨(u, v), by rw [mem_filter, mem_product]; exact ⟨⟨hu, hv⟩, h⟩, rfl⟩

theorem mem_Dset_of_inBlock {x y : Site} {r : ℕ} {z : ℤ × ℤ} (hz : z ∈ Zset r) {v : Site}
    (hv : InBlock (blockCorner x y z) v) : v ∈ Dset x y r := by
  rw [mem_Zset] at hz; rw [mem_Dset]; unfold InBlock blockCorner at hv; omega

/-- Every bond of the box lies in some block. -/
theorem exists_block_of_adj {x y : Site} {r : ℕ} {u v : Site} (hu : u ∈ Dset x y r)
    (hv : v ∈ Dset x y r) (h : squareGraph.Adj u v) :
    ∃ z ∈ Zset r, InBlock (blockCorner x y z) u ∧ InBlock (blockCorner x y z) v := by
  rw [mem_Dset] at hu hv
  have hc := adj_unit_cases h
  refine ⟨(min ((min u.1 v.1 - x.1) / 4) (r - 1), min ((min u.2 v.2 - y.2) / 4) (r - 1)), ?_, ?_, ?_⟩
  · rw [mem_Zset]; simp only; omega
  · unfold InBlock blockCorner; simp only; omega
  · unfold InBlock blockCorner; simp only; omega

/-- The `ℓ^∞` ball of radius `r` about `x` lies in the box when `y` is on its sphere. -/
theorem mem_Dset_of_linf {x y : Site} {r : ℕ} (hy : linfDist y x = r) {v : Site}
    (hv : linfDist v x ≤ r) : v ∈ Dset x y r := by
  unfold linfDist at hy hv
  rw [mem_Dset]
  have h1 := abs_le.1 (le_trans (le_max_left _ _) hv)
  have h2 := abs_le.1 (le_trans (le_max_right _ _) hv)
  have h3 := abs_le.1 (le_trans (le_max_left _ _) hy.le)
  have h4 := abs_le.1 (le_trans (le_max_right _ _) hy.le)
  omega

end Rotor
