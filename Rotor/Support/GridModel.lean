import Rotor.Support.Surgery
import Rotor.Support.LowerParams

open Finset Classical

namespace Rotor

section GridModel

variable (x y : Site) (r : ℕ)

/-- The coordinates of the grid model: the bonds of the box and the marks of the blocks. -/
abbrev GIdx := ↥(Fset x y r) ⊕ ↥(Zset r)

/-- The bond configuration read off a model configuration. -/
def bondsOf (ω : GIdx x y r → Bool) : BondConfig :=
  extF (Fset x y r) (fun b => ω (Sum.inl b))

/-- The marks read off a model configuration. -/
def marksOf (ω : GIdx x y r → Bool) (z : ℤ × ℤ) : Bool :=
  if h : z ∈ Zset r then ω (Sum.inr ⟨z, h⟩) else false

/-- The event of the marked model. -/
def GEvent : Set (GIdx x y r → Bool) :=
  {ω | ∃ l, ValidPath x y (Dset x y r) (Zset r) (gridCopy x y) (bondsOf x y r ω)
    (marksOf x y r ω) l}

theorem bondsOf_apply (ω : GIdx x y r → Bool) (b : ↥(Fset x y r)) :
    bondsOf x y r ω b.1 = ω (Sum.inl b) := by
  unfold bondsOf extF; rw [dif_pos b.2]

theorem gEvent_incr : IncrEvent (GEvent x y r) := by
  rintro ω ω' hle ⟨l, hopen, hh, hl, hD, hm⟩
  refine ⟨l, isOpenPath_mono hopen (fun i hi h => ?_), hh, hl, hD, fun z hz hT => ?_⟩
  · unfold bondsOf extF at h ⊢
    split_ifs at h ⊢ with hb
    exact hle _ h
  · have := hm z hz hT
    unfold marksOf at this ⊢
    rw [dif_pos hz] at this ⊢
    exact hle _ this

theorem bondsOf_update_inl (ω : GIdx x y r → Bool) (b : ↥(Fset x y r)) (v : Bool) :
    bondsOf x y r (Function.update ω (Sum.inl b) v) =
      Function.update (bondsOf x y r ω) b.1 v := by
  funext b'
  by_cases hb : b' = b.1
  · rw [hb, Function.update_self, bondsOf_apply, Function.update_self]
  · rw [Function.update_of_ne hb]
    unfold bondsOf extF
    by_cases h : b' ∈ Fset x y r
    · rw [dif_pos h, dif_pos h]
      show Function.update ω (Sum.inl b) v (Sum.inl ⟨b', h⟩) = ω (Sum.inl ⟨b', h⟩)
      rw [Function.update_of_ne]
      intro heq
      exact hb (congrArg Subtype.val (Sum.inl.inj heq))
    · rw [dif_neg h, dif_neg h]

theorem marksOf_update_inl (ω : GIdx x y r → Bool) (b : ↥(Fset x y r)) (v : Bool) :
    marksOf x y r (Function.update ω (Sum.inl b) v) = marksOf x y r ω := by
  funext z
  unfold marksOf
  split_ifs with hz
  · rw [Function.update_of_ne (by simp)]
  · rfl

theorem bondsOf_update_inr (ω : GIdx x y r → Bool) (z : ↥(Zset r)) (v : Bool) :
    bondsOf x y r (Function.update ω (Sum.inr z) v) = bondsOf x y r ω := by
  funext b
  unfold bondsOf extF
  split_ifs with hb
  · show Function.update ω (Sum.inr z) v (Sum.inl ⟨b, hb⟩) = ω (Sum.inl ⟨b, hb⟩)
    rw [Function.update_of_ne (by simp)]
  · rfl

theorem marksOf_update_inr (ω : GIdx x y r → Bool) (z : ↥(Zset r)) (v : Bool) :
    marksOf x y r (Function.update ω (Sum.inr z) v) =
      Function.update (marksOf x y r ω) z.1 v := by
  funext z'
  by_cases hz : z' = z.1
  · rw [hz, Function.update_self]
    unfold marksOf
    rw [dif_pos z.2]
    exact Function.update_self (Sum.inr z) v ω
  · rw [Function.update_of_ne hz]
    unfold marksOf
    split_ifs with h
    · rw [Function.update_of_ne]
      intro heq
      exact hz (congrArg Subtype.val (Sum.inr.inj heq))
    · rfl

/-- A valid path only reads bonds of the box. -/
theorem validPath_congr {ω₁ ω₂ : BondConfig} (h : ∀ b ∈ Fset x y r, ω₁ b = ω₂ b)
    {σ : ℤ × ℤ → Bool} {l : List Site}
    (hv : ValidPath x y (Dset x y r) (Zset r) (gridCopy x y) ω₁ σ l) :
    ValidPath x y (Dset x y r) (Zset r) (gridCopy x y) ω₂ σ l := by
  obtain ⟨hopen, hh, hl, hD, hm⟩ := hv
  refine ⟨isOpenPath_of_agree hopen (fun i hi => ?_), hh, hl, hD, hm⟩
  have hadj := (List.isChain_iff_getElem.1 hopen.1.2) i hi
  exact (h _ (mem_Fset.2 ⟨l[i], l[i + 1], hD _ (List.getElem_mem _), hD _ (List.getElem_mem _),
    hadj, rfl⟩)).symm

/-! ### The bonds touching a block -/

/-- `b` touches the block with corner `c`. -/
def Touches (c : Site) (b : Sym2 Site) : Prop := ∃ v ∈ b, InBlock c v

/-- The model coordinates touching block `z`. -/
noncomputable def touchSet (z : ℤ × ℤ) : Finset (GIdx x y r) :=
  Finset.univ.filter (fun j => ∃ b : ↥(Fset x y r), j = Sum.inl b ∧ Touches (blockCorner x y z) b.1)

/-- The vertices of the block with corner `c`. -/
def blockVerts (c : Site) : Finset Site := Icc c.1 (c.1 + 4) ×ˢ Icc c.2 (c.2 + 4)

theorem card_blockVerts (c : Site) : (blockVerts c).card = 25 := by
  rw [blockVerts, card_product, Int.card_Icc, Int.card_Icc,
    show c.1 + 4 + 1 - c.1 = 5 by ring, show c.2 + 4 + 1 - c.2 = 5 by ring]
  rfl

theorem mem_blockVerts {c v : Site} : v ∈ blockVerts c ↔ InBlock c v := by
  simp [blockVerts, InBlock, and_assoc]

theorem card_touching_le (c : Site) : ((Fset x y r).filter (Touches c)).card ≤ 100 := by
  have hsurj : Set.SurjOn (fun p : Site × Dir => s(p.1, p.1 + dirVec p.2))
      ↑(blockVerts c ×ˢ (Finset.univ : Finset Dir)) ↑((Fset x y r).filter (Touches c)) := by
    intro b hb
    rw [mem_coe, mem_filter, mem_Fset] at hb
    obtain ⟨⟨u, w, hu, hw, hadj, rfl⟩, v, hv, hvB⟩ := hb
    rw [Set.mem_image]
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · refine ⟨(v, dirOf (w - v)), ?_, ?_⟩
      · rw [mem_coe, mem_product]; exact ⟨mem_blockVerts.2 hvB, mem_univ _⟩
      · simp only; rw [dirVec_dirOf_of_adj hadj]
    · refine ⟨(v, dirOf (u - v)), ?_, ?_⟩
      · rw [mem_coe, mem_product]; exact ⟨mem_blockVerts.2 hvB, mem_univ _⟩
      · simp only; rw [dirVec_dirOf_of_adj hadj.symm, Sym2.eq_swap]
  have := Finset.card_le_card_of_surjOn _ hsurj
  simp only [card_product, card_blockVerts, card_univ, Fintype.card_fin] at this
  omega

theorem card_touchSet_le (z : ℤ × ℤ) : (touchSet x y r z).card ≤ 100 := by
  refine le_trans (Finset.card_le_card_of_injOn
    (fun j : GIdx x y r => Sum.elim (fun b => b.1) (fun _ => s(x, x)) j) ?_ ?_)
    (card_touching_le x y r (blockCorner x y z))
  · intro j hj
    rw [mem_coe] at hj
    unfold touchSet at hj
    rw [mem_filter] at hj
    obtain ⟨-, b, rfl, hb⟩ := hj
    rw [mem_coe, mem_filter]
    exact ⟨b.2, hb⟩
  · intro j hj j' hj' heq
    rw [mem_coe] at hj hj'
    unfold touchSet at hj hj'
    rw [mem_filter] at hj hj'
    obtain ⟨-, b, rfl, -⟩ := hj
    obtain ⟨-, b', rfl, -⟩ := hj'
    simp only [Sum.elim_inl] at heq
    rw [Subtype.ext heq]

/-! ### The pivotal comparison -/

/-- The mass of `{e pivotal}` is at most `8^|J|` times the mass of `{σ_z pivotal}`, for a bond
`e` of the block `z`. -/
theorem gEvent_pivot_le {par : GIdx x y r → ℝ} (hpar : IsParam par)
    (hbond : ∀ b : ↥(Fset x y r), 1 / 4 ≤ par (Sum.inl b) ∧ par (Sum.inl b) ≤ 3 / 4)
    (z : ↥(Zset r)) (e : ↥(Fset x y r)) (he : ∀ v ∈ e.1, InBlock (blockCorner x y z.1) v) :
    fpr par (Pivot (Sum.inl e) (GEvent x y r)) ≤
      4 ^ (touchSet x y r z.1).card * ((2 ^ (touchSet x y r z.1).card : ℕ) : ℝ) *
        fpr par (Pivot (Sum.inr z) (GEvent x y r)) := by
  set S := Pivot (Sum.inl e) (GEvent x y r) with hS
  set J := touchSet x y r z.1 with hJ
  have hsurg : ∀ ω : GIdx x y r → Bool, ∃ ω' : BondConfig, ω ∈ S →
      (∀ b : Sym2 Site, (∀ v ∈ b, ¬ InBlock (blockCorner x y z.1) v) →
        ω' b = bondsOf x y r ω b) ∧
      (∃ l, ValidPath x y (Dset x y r) (Zset r) (gridCopy x y) ω'
        (Function.update (marksOf x y r ω) z.1 true) l) ∧
      ∀ l, ¬ ValidPath x y (Dset x y r) (Zset r) (gridCopy x y) ω'
        (Function.update (marksOf x y r ω) z.1 false) l := by
    intro ω
    by_cases hω : ω ∈ S
    · obtain ⟨h1, h2⟩ := hω
      obtain ⟨l, hl⟩ := h1
      rw [bondsOf_update_inl, marksOf_update_inl] at hl
      have h2' : ∀ l', ¬ ValidPath x y (Dset x y r) (Zset r) (gridCopy x y)
          (Function.update (bondsOf x y r ω) e.1 false) (marksOf x y r ω) l' := by
        intro l' hl'
        apply h2
        refine ⟨l', ?_⟩
        rw [bondsOf_update_inl, marksOf_update_inl]
        exact hl'
      obtain ⟨ω', hω'⟩ := surgery x y r z.2 he (bondsOf x y r ω) (marksOf x y r ω) hl h2'
      exact ⟨ω', fun _ => hω'⟩
    · exact ⟨bondsOf x y r ω, fun h => absurd h hω⟩
  choose ω' hω' using hsurg
  let φ : (GIdx x y r → Bool) → (GIdx x y r → Bool) :=
    fun ω => Sum.elim (fun b => ω' ω b.1) (fun z' => ω (Sum.inr z'))
  have hagree : ∀ ω ∈ S, ∀ j ∉ J, φ ω j = ω j := by
    intro ω hω j hj
    rcases j with b | z'
    · simp only [φ, Sum.elim_inl]
      rw [(hω' ω hω).1 b.1, bondsOf_apply]
      intro v hv hvB
      apply hj
      rw [hJ]
      unfold touchSet
      rw [mem_filter]
      exact ⟨mem_univ _, b, rfl, v, hv, hvB⟩
    · simp [φ]
  have hmarks : ∀ ω, marksOf x y r (φ ω) = marksOf x y r ω := by
    intro ω; funext z'; unfold marksOf; split_ifs <;> rfl
  have hbonds : ∀ ω, ∀ b ∈ Fset x y r, bondsOf x y r (φ ω) b = ω' ω b := by
    intro ω b hb
    have := bondsOf_apply x y r (φ ω) ⟨b, hb⟩
    simp only [φ, Sum.elim_inl] at this
    exact this
  have hT : ∀ ω ∈ S, φ ω ∈ Pivot (Sum.inr z) (GEvent x y r) := by
    intro ω hω
    obtain ⟨-, ⟨l, hl⟩, hno⟩ := hω' ω hω
    refine ⟨⟨l, ?_⟩, ?_⟩
    · rw [bondsOf_update_inr, marksOf_update_inr, hmarks]
      exact validPath_congr x y r (fun b hb => (hbonds ω b hb).symm) hl
    · rintro ⟨l', hl'⟩
      rw [bondsOf_update_inr, marksOf_update_inr, hmarks] at hl'
      exact hno l' (validPath_congr x y r (fun b hb => hbonds ω b hb) hl')
  have hwt : ∀ ω ∈ S, fpw par ω ≤ 4 ^ J.card * fpw par (φ ω) := by
    intro ω hω
    refine fpw_le_of_agree hpar J (by norm_num) (fun j hj => ?_)
      (fun j hj => (hagree ω hω j hj).symm)
    rw [hJ] at hj
    unfold touchSet at hj
    rw [mem_filter] at hj
    obtain ⟨-, b, rfl, -⟩ := hj
    have := hbond b
    constructor <;> linarith [this.1, this.2]
  have hM : ∀ ω'', (Finset.univ.filter (fun ω => ω ∈ S ∧ φ ω = ω'')).card ≤ 2 ^ J.card :=
    card_agree_le J S φ hagree
  exact fpr_le_of_map hpar φ hT (by positivity) hwt hM

/-! ### Telescoping over the blocks -/

/-- `b` lies inside block `z`. -/
def Inside (z : ℤ × ℤ) (b : Sym2 Site) : Prop := ∀ v ∈ b, InBlock (blockCorner x y z) v

theorem sym2_exists_mem {α : Type*} (b : Sym2 α) : ∃ v, v ∈ b :=
  Sym2.ind (fun u w => ⟨u, Sym2.mem_mk_left u w⟩) b

/-- The parameters after the blocks of `W` have been processed. -/
noncomputable def gridPar (ε : ℝ) (W : Finset (ℤ × ℤ)) : GIdx x y r → ℝ :=
  Sum.elim (fun b => if ∃ z ∈ W, Inside x y z b.1 then 1 / 2 - ε else 1 / 2)
    (fun z => if z.1 ∈ W then 1 else 0)

theorem gridPar_isParam {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 4) (W : Finset (ℤ × ℤ)) :
    IsParam (gridPar x y r ε W) := by
  intro j
  rcases j with b | z
  · simp only [gridPar, Sum.elim_inl]; split_ifs <;> constructor <;> linarith
  · simp only [gridPar, Sum.elim_inr]; split_ifs <;> norm_num

/-- The coordinates lowered when block `z` is processed after `W`. -/
noncomputable def newSet (W : Finset (ℤ × ℤ)) (z : ℤ × ℤ) : Finset (GIdx x y r) :=
  Finset.univ.filter (fun j => ∃ b : ↥(Fset x y r), j = Sum.inl b ∧ Inside x y z b.1 ∧
    ¬ ∃ z' ∈ W, Inside x y z' b.1)

theorem newSet_subset (W : Finset (ℤ × ℤ)) (z : ℤ × ℤ) :
    newSet x y r W z ⊆ touchSet x y r z := by
  intro j hj
  unfold newSet at hj; unfold touchSet
  rw [mem_filter] at hj ⊢
  obtain ⟨-, b, rfl, hin, -⟩ := hj
  obtain ⟨v, hv⟩ := sym2_exists_mem b.1
  exact ⟨mem_univ _, b, rfl, v, hv, hin v hv⟩

theorem inr_notMem_newSet (W : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (z' : ↥(Zset r)) :
    Sum.inr z' ∉ newSet x y r W z := by
  unfold newSet
  rw [mem_filter]
  rintro ⟨-, b, h, -⟩
  exact Sum.noConfusion h

theorem gridPar_insert (ε : ℝ) (W : Finset (ℤ × ℤ)) {z : ℤ × ℤ} (hz : z ∈ Zset r)
    (hzW : z ∉ W) :
    gridPar x y r ε (insert z W) = fun j => if j = Sum.inr ⟨z, hz⟩ then 1 else
      if j ∈ newSet x y r W z then gridPar x y r ε W j - ε else gridPar x y r ε W j := by
  funext j
  rcases j with b | z'
  · have hne : (Sum.inl b : GIdx x y r) ≠ Sum.inr ⟨z, hz⟩ := Sum.inl_ne_inr
    simp only [gridPar, Sum.elim_inl, if_neg hne]
    by_cases hE : Sum.inl b ∈ newSet x y r W z
    · rw [if_pos hE]
      unfold newSet at hE; rw [mem_filter] at hE
      obtain ⟨-, b', hbb', hin, hnot⟩ := hE
      have hb' : b' = b := (Sum.inl.inj hbb').symm
      subst hb'
      rw [if_pos ⟨z, mem_insert_self _ _, hin⟩, if_neg hnot]
    · rw [if_neg hE]
      unfold newSet at hE; rw [mem_filter] at hE
      by_cases hW : ∃ z' ∈ W, Inside x y z' b.1
      · rw [if_pos hW]
        obtain ⟨z', hz', hin⟩ := hW
        rw [if_pos ⟨z', mem_insert_of_mem hz', hin⟩]
      · rw [if_neg hW]
        have hnin : ¬ Inside x y z b.1 := fun hin => hE ⟨mem_univ _, b, rfl, hin, hW⟩
        rw [if_neg]
        rintro ⟨z', hz', hin⟩
        rw [mem_insert] at hz'
        rcases hz' with rfl | hz'
        · exact hnin hin
        · exact hW ⟨z', hz', hin⟩
  · simp only [gridPar, Sum.elim_inr]
    rw [if_neg (inr_notMem_newSet x y r W z z')]
    by_cases hzz : z'.1 = z
    · have hz' : z' = ⟨z, hz⟩ := Subtype.ext hzz
      rw [if_pos (show (Sum.inr z' : GIdx x y r) = Sum.inr ⟨z, hz⟩ by rw [hz']),
        if_pos (show z'.1 ∈ insert z W by rw [hzz]; exact mem_insert_self _ _)]
    · rw [if_neg (fun h => hzz (congrArg Subtype.val (Sum.inr.inj h)))]
      by_cases hW : z'.1 ∈ W
      · rw [if_pos (mem_insert_of_mem hW), if_pos hW]
      · rw [if_neg (show ¬ z'.1 ∈ insert z W by rw [mem_insert]; tauto), if_neg hW]

/-- Processing one more block does not decrease the probability of the marked event. -/
theorem gridPar_step {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (hεK : ε * 2 ^ 100 * 100 * (4 ^ 100 * 2 ^ 100) * 2 ^ 100 ≤ 1)
    (W : Finset (ℤ × ℤ)) {z : ℤ × ℤ} (hz : z ∈ Zset r) (hzW : z ∉ W) :
    fpr (gridPar x y r ε W) (GEvent x y r) ≤
      fpr (gridPar x y r ε (insert z W)) (GEvent x y r) := by
  rw [gridPar_insert x y r ε W hz hzW]
  have hpar : IsParam (gridPar x y r ε W) := gridPar_isParam x y r hε.le hε' W
  have hEcard : (newSet x y r W z).card ≤ 100 :=
    le_trans (card_le_card (newSet_subset x y r W z)) (card_touchSet_le x y r z)
  have hJcard : (touchSet x y r z).card ≤ 100 := card_touchSet_le x y r z
  refine fpr_block_step hpar (gEvent_incr x y r) hε.le (newSet x y r W z) ?_ (Sum.inr ⟨z, hz⟩)
    (inr_notMem_newSet x y r W z ⟨z, hz⟩) ?_
    (K := 4 ^ (touchSet x y r z).card * ((2 ^ (touchSet x y r z).card : ℕ) : ℝ))
    (by positivity) ?_ ?_
  · intro j hj
    unfold newSet at hj; rw [mem_filter] at hj
    obtain ⟨-, b, rfl, -, hnot⟩ := hj
    simp only [gridPar, Sum.elim_inl, if_neg hnot]
    constructor <;> linarith
  · simp only [gridPar, Sum.elim_inr, if_neg hzW]
  · intro j hj
    unfold newSet at hj; rw [mem_filter] at hj
    obtain ⟨-, b, rfl, hin, -⟩ := hj
    refine gEvent_pivot_le x y r hpar (fun b' => ?_) ⟨z, hz⟩ b hin
    simp only [gridPar, Sum.elim_inl]
    split_ifs <;> constructor <;> linarith
  · have h1 : (2:ℝ) ^ (newSet x y r W z).card ≤ 2 ^ 100 := pow_le_pow_right₀ (by norm_num) hEcard
    have h2 : ((newSet x y r W z).card : ℝ) ≤ 100 := by exact_mod_cast hEcard
    have h3 : (4:ℝ) ^ (touchSet x y r z).card ≤ 4 ^ 100 := pow_le_pow_right₀ (by norm_num) hJcard
    have h4 : (((2 ^ (touchSet x y r z).card : ℕ)) : ℝ) ≤ 2 ^ 100 := by
      push_cast; exact pow_le_pow_right₀ (by norm_num) hJcard
    calc ε * 2 ^ (newSet x y r W z).card * ((newSet x y r W z).card : ℝ) *
          (4 ^ (touchSet x y r z).card * ((2 ^ (touchSet x y r z).card : ℕ) : ℝ)) *
          2 ^ (newSet x y r W z).card
        ≤ ε * 2 ^ 100 * 100 * (4 ^ 100 * 2 ^ 100) * 2 ^ 100 := by gcongr
      _ ≤ 1 := hεK

theorem gridPar_mono {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (hεK : ε * 2 ^ 100 * 100 * (4 ^ 100 * 2 ^ 100) * 2 ^ 100 ≤ 1) :
    ∀ W : Finset (ℤ × ℤ), W ⊆ Zset r →
      fpr (gridPar x y r ε ∅) (GEvent x y r) ≤ fpr (gridPar x y r ε W) (GEvent x y r) := by
  intro W
  induction W using Finset.induction_on with
  | empty => intro _; exact le_rfl
  | insert z W hzW ih =>
    intro hsub
    have hz : z ∈ Zset r := hsub (mem_insert_self _ _)
    exact (ih (fun a ha => hsub (mem_insert_of_mem ha))).trans
      (gridPar_step x y r hε hε' hεK W hz hzW)

theorem gridPar_empty (ε : ℝ) :
    gridPar x y r ε ∅ = Sum.elim (fun _ => (1 / 2 : ℝ)) (fun _ => 0) := by
  funext j
  rcases j with b | z
  · simp [gridPar]
  · simp [gridPar]

theorem gridPar_full (ε : ℝ) :
    gridPar x y r ε (Zset r) = Sum.elim (fun _ => 1 / 2 - ε) (fun _ => (1 : ℝ)) := by
  funext j
  rcases j with b | z
  · simp only [gridPar, Sum.elim_inl]
    rw [if_pos]
    obtain ⟨u, w, hu, hw, hadj, hb⟩ := mem_Fset.1 b.2
    obtain ⟨z, hz, hzu, hzw⟩ := exists_block_of_adj hu hw hadj
    refine ⟨z, hz, fun v hv => ?_⟩
    rw [hb] at hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hzu
    · exact hzw
  · simp only [gridPar, Sum.elim_inr, if_pos z.2]

end GridModel

end Rotor
