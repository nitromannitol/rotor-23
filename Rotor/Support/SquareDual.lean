import Rotor.Dual
import Rotor.Support.StepProb
import Rotor.Support.KingPaths
import Rotor.Support.DegreeThreePassage

/-!
Coordinate identities for the dual edges of the square lattice (`rotor.tex:1541-1551`): the
dual edge of `v → v + dirVec a` runs from the face on its right to the face on its left, and
the four dual edges at `v` form the unit square around `v` traversed counterclockwise.
-/

open Fin.NatCast

namespace Rotor

theorem leftFace_eq (v : Site) (a : Dir) : leftFace v a = rightFace v (a - 1) := by
  fin_cases a
  · simp [leftFace, rightFace, dirVec]; omega
  all_goals simp [leftFace, rightFace, dirVec]

theorem adj_rightFace_leftFace (v : Site) (a : Dir) :
    squareGraph.Adj (rightFace v a) (leftFace v a) := by
  rw [squareGraph_adj]
  fin_cases a <;> simp [leftFace, rightFace, dirVec]

theorem primalTail_dual (v : Site) (a : Dir) : primalTail (rightFace v a) (leftFace v a) = v := by
  obtain ⟨x, y⟩ := v
  fin_cases a <;> simp [primalTail, leftFace, rightFace, dirVec]

theorem primalDir_dual (v : Site) (a : Dir) : primalDir (rightFace v a) (leftFace v a) = a := by
  obtain ⟨x, y⟩ := v
  fin_cases a <;> simp [primalDir, leftFace, rightFace, dirVec, dirOf]

theorem dualOpen_of_eq (ρ : Config squareGraph) {f g : Site} {v : Site} {a : Dir}
    (hv : primalTail f g = v) (ha : primalDir f g = a) :
    DualOpen ρ f g ↔ rank clockwise ρ v (nbr v a) = 2 ∨ rank clockwise ρ v (nbr v a) = 3 := by
  subst hv; subst ha; exact Iff.rfl

/-- The dual edge of `v → v + dirVec a` is open iff the rank of that edge is `2` or `3`. -/
theorem dualOpen_iff (ρ : Config squareGraph) (v : Site) (a : Dir) :
    DualOpen ρ (rightFace v a) (leftFace v a) ↔
      rank clockwise ρ v (nbr v a) = 2 ∨ rank clockwise ρ v (nbr v a) = 3 :=
  dualOpen_of_eq ρ (primalTail_dual v a) (primalDir_dual v a)

theorem fin4_offset (a b : Fin 4) :
    b + ((((a - b).val + 3) % 4 + 1 : ℕ) : Fin 4) = a := by
  revert a b
  decide

/-- The rank of the edge in direction `a` from the initial rotor `ρ v = nbr v b` is the
clockwise offset `a - b`, read in `{1, …, 4}`. -/
theorem rank_clockwise (ρ : Config squareGraph) (v : Site) (a : Dir) :
    rank clockwise ρ v (nbr v a) = ((a - (nbr v).symm (ρ v) : Dir).val + 3) % 4 + 1 := by
  set b := (nbr v).symm (ρ v) with hb
  have hρ : ρ v = nbr v b := ((nbr v).apply_symm_apply (ρ v)).symm
  rw [rank_eq_cycRank]
  apply cycRank_eq_of
  · omega
  · rw [Fintype.card_congr (nbr v).symm]
    show _ ≤ 4
    have := Nat.mod_lt ((a - b).val + 3) (by norm_num : 0 < 4)
    omega
  · show (turnAt v ^ _) (ρ v) = nbr v a
    rw [hρ, turnAt_pow_nbr]
    congr 1
    exact fin4_offset a b

theorem rank_add (ρ : Config squareGraph) (v : Site) (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    rank clockwise ρ v (nbr v ((nbr v).symm (ρ v) + (k : Dir))) = k := by
  rw [rank_clockwise, add_sub_cancel_left]
  interval_cases k <;> rfl

theorem val_cast_rank (ρ : Config squareGraph) (v : Site) (a : Dir) :
    ((rank clockwise ρ v (nbr v a) : ℕ) : Dir).val = (a - (nbr v).symm (ρ v)).val := by
  rw [rank_clockwise, Fin.val_natCast]
  have := (a - (nbr v).symm (ρ v)).isLt
  omega

theorem rank_pos' (ρ : Config squareGraph) (v : Site) (a : Dir) :
    1 ≤ rank clockwise ρ v (nbr v a) := by
  rw [rank_eq_cycRank]; exact cycRank_pos _ (clockwise.cyclic v) _ _

theorem rank_le_four (ρ : Config squareGraph) (v : Site) (a : Dir) :
    rank clockwise ρ v (nbr v a) ≤ 4 := by
  rw [rank_eq_cycRank]
  have := cycRank_le (clockwise.next v) (clockwise.cyclic v) (ρ v) (nbr v a)
  rwa [Fintype.card_congr (nbr v).symm] at this

/-- The face on the right of `p → v` is the face on the right of the edge out of `v` one step
clockwise before the reverse edge `v → p`. -/
theorem rightFace_rev {p v : Site} (h : squareGraph.Adj p v) :
    rightFace p (dirOf (v - p)) = rightFace v (dirOf (p - v) - 1) := by
  have hv : v = p + dirVec (dirOf (v - p)) := (dirVec_dirOf_of_adj h).symm
  generalize dirOf (v - p) = a at hv
  subst hv
  obtain ⟨x, y⟩ := p
  fin_cases a <;> simp [rightFace, dirVec, dirOf]

/-- The faces `rightFace v c, rightFace v (c-1), …, rightFace v (c-n)`. -/
def faces (v : Site) (c : Dir) : ℕ → List Site
  | 0 => [rightFace v c]
  | n + 1 => rightFace v c :: faces v (c - 1) n

theorem faces_head (v : Site) (c : Dir) (n : ℕ) : (faces v c n).head? = some (rightFace v c) := by
  cases n <;> rfl

theorem faces_ne_nil (v : Site) (c : Dir) (n : ℕ) : faces v c n ≠ [] := by
  cases n <;> simp [faces]

theorem faces_getLast (v : Site) (c : Dir) : ∀ n : ℕ,
    (faces v c n).getLast (faces_ne_nil v c n) = rightFace v (c - (n : Dir))
  | 0 => by simp [faces]
  | n + 1 => by
    show (rightFace v c :: faces v (c - 1) n).getLast _ = _
    rw [List.getLast_cons (faces_ne_nil v (c - 1) n), faces_getLast]
    congr 1
    apply Fin.ext
    simp only [Fin.coe_sub, Fin.val_natCast, Fin.val_one]
    omega

theorem faces_getLast? (v : Site) (c : Dir) (n : ℕ) :
    (faces v c n).getLast? = some (rightFace v (c - (n : Dir))) := by
  rw [List.getLast?_eq_some_getLast (faces_ne_nil v c n), faces_getLast]

/-- The relation of open dual edges. -/
def DualStep (ρ : Config squareGraph) (f g : Site) : Prop := DualOpen ρ f g ∧ squareGraph.Adj f g

theorem faces_chain (ρ : Config squareGraph) (v : Site) : ∀ (c : Dir) (n : ℕ),
    (∀ j < n, rank clockwise ρ v (nbr v (c - (j : Dir))) = 2 ∨
      rank clockwise ρ v (nbr v (c - (j : Dir))) = 3) →
    (faces v c n).IsChain (DualStep ρ)
  | c, 0, _ => List.isChain_singleton _
  | c, n + 1, h => by
    rw [faces, List.isChain_cons]
    refine ⟨fun y hy => ?_, faces_chain ρ v (c - 1) n (fun j hj => ?_)⟩
    · rw [faces_head, Option.mem_def, Option.some.injEq] at hy
      subst hy
      refine ⟨?_, ?_⟩
      · rw [← leftFace_eq, dualOpen_iff]
        simpa using h 0 (by omega)
      · rw [← leftFace_eq]; exact adj_rightFace_leftFace v c
    · have := h (j + 1) (by omega)
      have e : c - ((j + 1 : ℕ) : Dir) = c - 1 - (j : Dir) := by
        apply Fin.ext
        simp only [Fin.coe_sub, Fin.val_natCast, Fin.val_one]
        omega
      rwa [e] at this

/-- The dual faces traversed at `v` between the entrance direction `a_p` and the exit direction
`a_w`. -/
noncomputable def segAt (ρ : Config squareGraph) (v : Site) (a_p a_w : Dir) : List Site :=
  faces v (a_p - 1) (rank clockwise ρ v (nbr v a_p) - 1 - rank clockwise ρ v (nbr v a_w))

theorem segAt_head (ρ : Config squareGraph) (v : Site) (a_p a_w : Dir) :
    (segAt ρ v a_p a_w).head? = some (rightFace v (a_p - 1)) := faces_head _ _ _

theorem segAt_ne_nil (ρ : Config squareGraph) (v : Site) (a_p a_w : Dir) :
    segAt ρ v a_p a_w ≠ [] :=
  faces_ne_nil _ _ _

theorem segAt_getLast (ρ : Config squareGraph) (v : Site) {a_p a_w : Dir}
    (hlt : rank clockwise ρ v (nbr v a_w) < rank clockwise ρ v (nbr v a_p)) :
    (segAt ρ v a_p a_w).getLast? = some (rightFace v a_w) := by
  rw [segAt, faces_getLast?]
  congr 2
  have h1 := val_cast_rank ρ v a_p
  have h2 := val_cast_rank ρ v a_w
  have hp4 := rank_le_four ρ v a_p
  rw [Fin.val_natCast] at h1 h2
  apply Fin.ext
  simp only [Fin.coe_sub, Fin.val_natCast, Fin.val_one] at h1 h2 ⊢
  omega

theorem segAt_chain (ρ : Config squareGraph) (v : Site) {a_p a_w : Dir}
    (hlt : rank clockwise ρ v (nbr v a_w) < rank clockwise ρ v (nbr v a_p)) :
    (segAt ρ v a_p a_w).IsChain (DualStep ρ) := by
  refine faces_chain ρ v _ _ (fun j hj => ?_)
  have h1 := val_cast_rank ρ v a_p
  have hw1 := rank_pos' ρ v a_w
  have hp4 := rank_le_four ρ v a_p
  rw [Fin.val_natCast] at h1
  set r_p := rank clockwise ρ v (nbr v a_p) with hr_p
  set r_w := rank clockwise ρ v (nbr v a_w) with hr_w
  have hdir : a_p - 1 - (j : Dir) = (nbr v).symm (ρ v) + ((r_p - 1 - j : ℕ) : Dir) := by
    apply Fin.ext
    simp only [Fin.coe_sub, Fin.val_add, Fin.val_natCast, Fin.val_one] at h1 ⊢
    omega
  rw [hdir, rank_add ρ v (r_p - 1 - j) (by omega) (by omega)]
  omega

/-- Live at each internal vertex, in forward recursive form. -/
def LiveFwd (ρ : Config squareGraph) : List Site → Prop
  | p :: v :: w :: rest => LiveAt clockwise ρ p v w ∧ LiveFwd ρ (v :: w :: rest)
  | _ => True

theorem liveFwd_of_forall (ρ : Config squareGraph) : ∀ (l : List Site),
    (∀ i (h : i + 2 < l.length), LiveAt clockwise ρ l[i] l[i + 1] l[i + 2]) → LiveFwd ρ l
  | p :: v :: w :: rest, h => by
    refine ⟨h 0 (by simp), ?_⟩
    exact liveFwd_of_forall ρ (v :: w :: rest)
      (fun i hi => h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega))
  | [], _ => trivial
  | [_], _ => trivial
  | [_, _], _ => trivial

theorem liveFwd_of_isLive {ρ : Config squareGraph} {l : List Site}
    (hl : IsLive clockwise ρ l) : LiveFwd ρ l := by
  refine liveFwd_of_forall ρ l (fun i hi => ?_)
  have := liveAt_of_isLive clockwise hl (j := i + 1) (by omega) (by omega)
  convert this using 2

/-- The rank of the edge from `v` to an adjacent vertex, as a direction. -/
theorem rank'_eq (ρ : Config squareGraph) {v w : Site} (h : squareGraph.Adj v w) :
    rank' clockwise ρ v w h = rank clockwise ρ v (nbr v (dirOf (w - v))) := by
  unfold rank'
  congr 1
  exact Subtype.ext (dirVec_dirOf_of_adj h).symm

/-- The walk of dual faces along a path, oldest first. -/
noncomputable def dualWalk (ρ : Config squareGraph) : List Site → List Site
  | p :: v :: w :: rest =>
    (segAt ρ v (dirOf (p - v)) (dirOf (w - v))).dropLast ++ dualWalk ρ (v :: w :: rest)
  | [p, v] => [rightFace p (dirOf (v - p))]
  | _ => []

/-- The last two vertices of a path. -/
def last2 : List Site → Site × Site
  | _ :: v :: w :: rest => last2 (v :: w :: rest)
  | [p, v] => (p, v)
  | _ => (0, 0)

theorem last2_eq : ∀ (p v : Site) (rest : List Site),
    (p :: v :: rest)[(p :: v :: rest).length - 2]? = some (last2 (p :: v :: rest)).1 ∧
    (p :: v :: rest)[(p :: v :: rest).length - 1]? = some (last2 (p :: v :: rest)).2
  | p, v, [] => by simp [last2]
  | p, v, w :: rest => by
    obtain ⟨h1, h2⟩ := last2_eq v w rest
    simp only [List.length_cons] at h1 h2 ⊢
    rw [show rest.length + 1 + 1 + 1 - 2 = (rest.length + 1 + 1 - 2) + 1 by omega,
      show rest.length + 1 + 1 + 1 - 1 = (rest.length + 1 + 1 - 1) + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact ⟨h1, h2⟩

theorem dualWalk_ne_nil (ρ : Config squareGraph) : ∀ (p v : Site) (rest : List Site),
    dualWalk ρ (p :: v :: rest) ≠ []
  | p, v, [] => by simp [dualWalk]
  | p, v, w :: rest => by
    simp only [dualWalk, ne_eq, List.append_eq_nil_iff, not_and]
    intro _
    exact dualWalk_ne_nil ρ v w rest

theorem dualWalk_getLast (ρ : Config squareGraph) : ∀ (p v : Site) (rest : List Site),
    (dualWalk ρ (p :: v :: rest)).getLast? =
      some (rightFace (last2 (p :: v :: rest)).1
        (dirOf ((last2 (p :: v :: rest)).2 - (last2 (p :: v :: rest)).1)))
  | p, v, [] => by simp [dualWalk, last2]
  | p, v, w :: rest => by
    rw [dualWalk, List.getLast?_append_of_ne_nil _ (dualWalk_ne_nil ρ v w rest),
      dualWalk_getLast ρ v w rest]
    rfl

theorem dualWalk_head (ρ : Config squareGraph) : ∀ (p v : Site) (rest : List Site),
    (p :: v :: rest).IsChain squareGraph.Adj → LiveFwd ρ (p :: v :: rest) →
    (dualWalk ρ (p :: v :: rest)).head? = some (rightFace p (dirOf (v - p)))
  | p, v, [], _, _ => rfl
  | p, v, w :: rest, hch, hlive => by
    obtain ⟨hl, hlive'⟩ := hlive
    obtain ⟨hw, hp, hlt⟩ := hl
    rw [rank'_eq ρ hw, rank'_eq ρ hp] at hlt
    have hpv : squareGraph.Adj p v := hch.rel_head
    rw [dualWalk, rightFace_rev hpv]
    have hhead := segAt_head ρ v (dirOf (p - v)) (dirOf (w - v))
    have hlast := segAt_getLast ρ v hlt
    have hne := segAt_ne_nil ρ v (dirOf (p - v)) (dirOf (w - v))
    rcases hd : (segAt ρ v (dirOf (p - v)) (dirOf (w - v))).dropLast with _ | ⟨f, fs⟩
    · rw [List.nil_append, dualWalk_head ρ v w rest hch.of_cons hlive']
      have hlen : (segAt ρ v (dirOf (p - v)) (dirOf (w - v))).length = 1 := by
        have := congrArg List.length hd
        rw [List.length_dropLast] at this
        have := List.length_pos_iff.2 hne
        simp at *; omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hlen
      rw [hx] at hhead hlast
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
      rw [← hhead, ← hlast]
    · rw [List.cons_append, List.head?_cons]
      rw [← List.dropLast_append_getLast hne, hd, List.cons_append, List.head?_cons] at hhead
      exact hhead

theorem dualWalk_chain (ρ : Config squareGraph) : ∀ (l : List Site),
    l.IsChain squareGraph.Adj → LiveFwd ρ l → (dualWalk ρ l).IsChain (DualStep ρ)
  | p :: v :: w :: rest, hch, hlive => by
    obtain ⟨hl, hlive'⟩ := hlive
    obtain ⟨hw, hp, hlt⟩ := hl
    rw [rank'_eq ρ hw, rank'_eq ρ hp] at hlt
    rw [dualWalk, List.isChain_append]
    have hseg := segAt_chain ρ v hlt
    have hne := segAt_ne_nil ρ v (dirOf (p - v)) (dirOf (w - v))
    rw [← List.dropLast_append_getLast hne, List.isChain_append] at hseg
    refine ⟨hseg.1, dualWalk_chain ρ (v :: w :: rest) hch.of_cons hlive', fun x hx y hy => ?_⟩
    rw [dualWalk_head ρ v w rest hch.of_cons hlive'] at hy
    have hlast := segAt_getLast ρ v hlt
    rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hlast
    rw [Option.mem_def, Option.some.injEq] at hy
    subst hy
    rw [← hlast]
    exact hseg.2.2 x hx _ rfl
  | [], _, _ => List.isChain_nil
  | [_], _, _ => by simp [dualWalk]
  | [_, _], _, _ => by simp [dualWalk]

/-- Lemma 5.1. -/
theorem square_dual_path_proof (ρ : Config squareGraph) (l : List Site)
    (hl : IsPath squareGraph l) (hlive : IsLive clockwise ρ l) (hm : 2 ≤ l.length)
    (x₀ x₁ y₀ y₁ : Site) (h0 : l[0]? = some x₀) (h1 : l[1]? = some x₁)
    (hy0 : l[l.length - 2]? = some y₀) (hy1 : l[l.length - 1]? = some y₁) :
    ∃ q : List Site, IsOpenDualPath ρ q ∧
      q.head? = some (rightFace x₀ (dirOf (x₁ - x₀))) ∧
      q.getLast? = some (rightFace y₀ (dirOf (y₁ - y₀))) := by
  obtain ⟨p, v, rest, rfl⟩ : ∃ p v rest, l = p :: v :: rest := by
    match l, hm with
    | p :: v :: rest, _ => exact ⟨p, v, rest, rfl⟩
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
  obtain ⟨hl2, hl2'⟩ := last2_eq p v rest
  rw [hy0] at hl2; rw [hy1] at hl2'
  have hch := hl.2
  have hlf := liveFwd_of_isLive hlive
  have hchain := dualWalk_chain ρ _ hch hlf
  obtain ⟨q, hq, hnd, hhead, hlast, -⟩ := exists_nodup_chain (DualStep ρ) _ _ le_rfl hchain
    (dualWalk_ne_nil ρ p v rest)
  refine ⟨q, ⟨⟨hnd, hq.imp (fun _ _ h => h.2)⟩, hq.imp (fun _ _ h => h.1)⟩, ?_, ?_⟩
  · rw [hhead, dualWalk_head ρ p v rest hch hlf, h0, h1]
  · rw [hlast, dualWalk_getLast ρ p v rest, ← Option.some.inj hl2, ← Option.some.inj hl2']

end Rotor
