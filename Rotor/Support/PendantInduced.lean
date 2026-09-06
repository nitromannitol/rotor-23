import Rotor.Support.PendantBasics
import Rotor.Support.WalkBasics

/-!
The rotor walk on `G_M` and the induced walk on `ℤ²` (`rotor.tex:2230-2238`): "Deleting each
two-step visit to a leaf leaves a rotor walk on `ℤ²` whose initial rotors are independent and
point west with probability `(M+1)/(M+4)`."  The induced initial rotor at `v` is the last
lattice direction at or before the rotor `ρ(v)` in the clockwise order `N, E, S, W, L_1, …, L_M`.
-/

open Fin.NatCast

namespace Rotor

variable (M : ℕ)

/-- The index of a neighbour of the lattice vertex `v` in the order `N, E, S, W, L_1, …, L_M`. -/
def nbrIdx {v : Site} (a : (pendantGraph M).neighborSet (.inl v)) : Fin (M + 4) :=
  (pendantNbrLattice M v).symm a

/-- The lattice direction induced by a neighbour index: itself if it is a lattice direction,
and `W` for a leaf. -/
def latDir (k : Fin (M + 4)) : Dir := if h : (k : ℕ) < 4 then ⟨k, h⟩ else 3

/-- The induced rotor configuration on `ℤ²`. -/
def induce (ρ : Config (pendantGraph M)) : Config squareGraph :=
  fun v => nbr v (latDir M (nbrIdx M (ρ (.inl v))))

/-- The number of leaves visited before the next lattice move, from neighbour index `k`. -/
def leafVisits (k : Fin (M + 4)) : ℕ := if (k : ℕ) ≤ 2 then 0 else M + 3 - k

theorem nbrIdx_nbrLattice (v : Site) (k : Fin (M + 4)) :
    nbrIdx M (pendantNbrLattice M v k) = k := by
  simp [nbrIdx]

theorem pendantMech_next_inl (v : Site) (k : Fin (M + 4)) :
    (pendantMech M).next (.inl v) (pendantNbrLattice M v k) = pendantNbrLattice M v (k + 1) := by
  simpa using pendantTurn_pow M v 1 k

theorem pendantNbrLattice_val_lattice (v : Site) (k : Fin (M + 4)) (h : (k : ℕ) < 4) :
    (pendantNbrLattice M v k).1 = .inl (v + dirVec ⟨k, h⟩) := by
  simp [pendantNbrLattice, h]

theorem pendantNbrLattice_val_leaf (v : Site) (k : Fin (M + 4)) (h : ¬ (k : ℕ) < 4) :
    (pendantNbrLattice M v k).1 = .inr (v, ⟨k - 4, by omega⟩) := by
  simp [pendantNbrLattice, h]

/-- The single neighbour of a leaf is its lattice vertex. -/
theorem leaf_nbr_val (w : Site × Fin M) (a : (pendantGraph M).neighborSet (.inr w)) :
    a.1 = .inl w.1 := by
  obtain ⟨u | u, h⟩ := a
  · exact congrArg Sum.inl (show w.1 = u from h).symm
  · exact h.elim

/-- Two steps from a lattice vertex whose rotor points before the last leaf: visit the next
leaf and come back, advancing the rotor by one. -/
theorem step_leaf (ρ : Config (pendantGraph M)) (v : Site) (k : Fin (M + 4))
    (hρ : ρ (.inl v) = pendantNbrLattice M v k) (hk : 3 ≤ (k : ℕ)) (hkM : (k : ℕ) < M + 3) :
    step (pendantMech M) (step (pendantMech M) ⟨.inl v, ρ⟩) =
      ⟨.inl v, Function.update ρ (.inl v) (pendantNbrLattice M v (k + 1))⟩ := by
  have hk1 : ((k + 1 : Fin (M + 4)) : ℕ) = k + 1 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < M + 4 by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hnot : ¬ ((k + 1 : Fin (M + 4)) : ℕ) < 4 := by omega
  -- first step: to the leaf
  have h1 : step (pendantMech M) ⟨.inl v, ρ⟩ =
      ⟨.inr (v, ⟨(k + 1 : Fin (M + 4)) - 4, by omega⟩),
        Function.update ρ (.inl v) (pendantNbrLattice M v (k + 1))⟩ := by
    simp only [step, hρ, pendantMech_next_inl]
    rw [pendantNbrLattice_val_leaf M v (k + 1) hnot]
  rw [h1]
  -- second step: back to `v`, rotor at the leaf unchanged
  set ρ' := Function.update ρ (.inl v) (pendantNbrLattice M v (k + 1)) with hρ'
  set w : Site × Fin M := (v, ⟨(k + 1 : Fin (M + 4)) - 4, by omega⟩) with hw
  have hnext : (pendantMech M).next (.inr w) (ρ' (.inr w)) = ρ' (.inr w) := rfl
  simp only [step, hnext, leaf_nbr_val, Function.update_eq_self]
  rfl

theorem step_to_leaf (ρ : Config (pendantGraph M)) (v : Site) (k : Fin (M + 4))
    (hρ : ρ (.inl v) = pendantNbrLattice M v k) (hk : 3 ≤ (k : ℕ)) (hkM : (k : ℕ) < M + 3) :
    ∃ i : Fin M, (step (pendantMech M) ⟨.inl v, ρ⟩).pos = .inr (v, i) := by
  have hk1 : ((k + 1 : Fin (M + 4)) : ℕ) = k + 1 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < M + 4 by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hnot : ¬ ((k + 1 : Fin (M + 4)) : ℕ) < 4 := by omega
  refine ⟨⟨(k + 1 : Fin (M + 4)) - 4, by omega⟩, ?_⟩
  simp only [step, hρ, pendantMech_next_inl]
  rw [pendantNbrLattice_val_leaf M v (k + 1) hnot]

/-- The last leaf index. -/
def lastLeaf : Fin (M + 4) := ⟨M + 3, by omega⟩

/-- The leaf phase: from rotor index `k ≥ 3` at `v`, after `2 (M + 3 - k)` steps the walker is
back at `v` with its rotor at the last leaf, and in between it alternates between `v` and its
leaves. -/
theorem leaf_phase (v : Site) : ∀ (n : ℕ) (ρ : Config (pendantGraph M)) (k : Fin (M + 4)),
    ρ (.inl v) = pendantNbrLattice M v k → 3 ≤ (k : ℕ) → (k : ℕ) + n = M + 3 →
    (step (pendantMech M))^[2 * n] ⟨.inl v, ρ⟩ =
      ⟨.inl v, Function.update ρ (.inl v) (pendantNbrLattice M v (lastLeaf M))⟩ ∧
    ∀ j ≤ 2 * n, (Even j → ((step (pendantMech M))^[j] ⟨.inl v, ρ⟩).pos = .inl v) ∧
      (¬ Even j → ∃ i : Fin M, ((step (pendantMech M))^[j] ⟨.inl v, ρ⟩).pos = .inr (v, i))
  | 0, ρ, k, hρ, hk, hn => by
    have hk' : k = lastLeaf M := Fin.ext (by simp [lastLeaf]; omega)
    refine ⟨?_, fun j hj => ?_⟩
    · simp only [mul_zero, Function.iterate_zero, id_eq]
      rw [← hk', ← hρ, Function.update_eq_self]
    · have : j = 0 := by omega
      subst this
      exact ⟨fun _ => rfl, fun h => absurd ⟨0, rfl⟩ h⟩
  | n + 1, ρ, k, hρ, hk, hn => by
    have hkM : (k : ℕ) < M + 3 := by omega
    have h2 := step_leaf M ρ v k hρ hk hkM
    have hk1 : ((k + 1 : Fin (M + 4)) : ℕ) = k + 1 := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < M + 4 by omega),
        Nat.mod_eq_of_lt (by omega)]
    set ρ₁ := Function.update ρ (.inl v) (pendantNbrLattice M v (k + 1)) with hρ₁
    have hρ₁v : ρ₁ (.inl v) = pendantNbrLattice M v (k + 1) := by
      rw [hρ₁, Function.update_self]
    obtain ⟨hend, hpos⟩ := leaf_phase v n ρ₁ (k + 1) hρ₁v (by omega) (by omega)
    have hiter : ∀ j, (step (pendantMech M))^[j + 2] ⟨.inl v, ρ⟩ =
        (step (pendantMech M))^[j] ⟨.inl v, ρ₁⟩ := by
      intro j
      rw [Function.iterate_add_apply]
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      rw [h2]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [show 2 * (n + 1) = 2 * n + 2 by ring, hiter, hend, hρ₁, Function.update_idem]
    · rcases lt_or_ge j 2 with hj2 | hj2
      · refine ⟨fun he => ?_, fun ho => ?_⟩
        · have : j = 0 := by
            rcases Nat.even_iff.1 he with h; omega
          subst this; rfl
        · have : j = 1 := by
            rcases Nat.even_or_odd j with h | h
            · exact absurd h ho
            · rcases Nat.odd_iff.1 h with h'; omega
          subst this
          simpa using step_to_leaf M ρ v k hρ hk hkM
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj2
        rw [add_comm, hiter]
        have := hpos j' (by omega)
        rw [show Even (j' + 2) ↔ Even j' by simp [Nat.even_add]]
        exact this

theorem induce_update (ρ : Config (pendantGraph M)) (v : Site) (k : Fin (M + 4)) :
    induce M (Function.update ρ (.inl v) (pendantNbrLattice M v k)) =
      Function.update (induce M ρ) v (nbr v (latDir M k)) := by
  funext w
  by_cases hw : w = v
  · subst hw
    simp [induce, nbrIdx_nbrLattice]
  · simp [induce, Function.update_of_ne hw]

theorem latDir_of_ge (k : Fin (M + 4)) (hk : 3 ≤ (k : ℕ)) : latDir M k = 3 := by
  unfold latDir
  split_ifs with h
  · exact Fin.ext (by show (k : ℕ) = 3; omega)
  · rfl

theorem latDir_lastLeaf : latDir M (lastLeaf M) = 3 :=
  latDir_of_ge M (lastLeaf M) (by simp [lastLeaf])

/-- The induced rotors are unchanged by a leaf phase. -/
theorem induce_update_lastLeaf (ρ : Config (pendantGraph M)) (v : Site) (k : Fin (M + 4))
    (hρ : ρ (.inl v) = pendantNbrLattice M v k) (hk : 3 ≤ (k : ℕ)) :
    induce M (Function.update ρ (.inl v) (pendantNbrLattice M v (lastLeaf M))) = induce M ρ := by
  rw [induce_update, latDir_lastLeaf]
  have : induce M ρ v = nbr v 3 := by
    simp [induce, hρ, nbrIdx_nbrLattice, latDir_of_ge M k hk]
  rw [← this, Function.update_eq_self]

/-- The lattice move: from a lattice direction or the last leaf. -/
theorem step_lattice (ρ : Config (pendantGraph M)) (v : Site) (k : Fin (M + 4))
    (hρ : ρ (.inl v) = pendantNbrLattice M v k) (hk : (k : ℕ) ≤ 2 ∨ (k : ℕ) = M + 3) :
    ((k + 1 : Fin (M + 4)) : ℕ) < 4 ∧
    step (pendantMech M) ⟨.inl v, ρ⟩ =
      ⟨.inl (v + dirVec (latDir M (k + 1))),
        Function.update ρ (.inl v) (pendantNbrLattice M v (k + 1))⟩ := by
  have hk1 : ((k + 1 : Fin (M + 4)) : ℕ) = (k + 1) % (M + 4) := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < M + 4 by omega)]
  have hlt : ((k + 1 : Fin (M + 4)) : ℕ) < 4 := by
    rw [hk1]
    rcases hk with hk | hk
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [hk, show M + 3 + 1 = M + 4 by ring, Nat.mod_self]
      omega
  refine ⟨hlt, ?_⟩
  simp only [step, hρ, pendantMech_next_inl]
  rw [pendantNbrLattice_val_lattice M v (k + 1) hlt]
  congr 3
  simp [latDir, hlt]

theorem latDir_succ (k : Fin (M + 4)) (hk : (k : ℕ) ≤ 2 ∨ (k : ℕ) = M + 3) :
    latDir M (k + 1) = latDir M k + 1 := by
  have hk1 : ((k + 1 : Fin (M + 4)) : ℕ) = (k + 1) % (M + 4) := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < M + 4 by omega)]
  rcases hk with hk | hk
  · have h1 : ((k + 1 : Fin (M + 4)) : ℕ) = k + 1 := by rw [hk1, Nat.mod_eq_of_lt (by omega)]
    have h4 : (k : ℕ) < 4 := by omega
    have h5 : (k : ℕ) + 1 < 4 := by omega
    apply Fin.ext
    simp only [latDir, h1, dif_pos h4, dif_pos h5, Fin.val_add, Fin.val_one]
    omega
  · have h1 : ((k + 1 : Fin (M + 4)) : ℕ) = 0 := by
      rw [hk1, hk, show M + 3 + 1 = M + 4 by ring, Nat.mod_self]
    rw [latDir_of_ge M k (by omega)]
    apply Fin.ext
    simp [latDir, h1]

section Simulation

variable (ρ : Config (pendantGraph M)) (o : Site)

/-- The induced square-lattice walk. -/
noncomputable abbrev Ysq (s : ℕ) : Site := X clockwise (induce M ρ) o s
noncomputable abbrev σsq (s : ℕ) : Config squareGraph := rot clockwise (induce M ρ) o s
noncomputable abbrev Xpend (t : ℕ) : PVertex M := X (pendantMech M) ρ (.inl o) t
noncomputable abbrev ρpend (t : ℕ) : Config (pendantGraph M) := rot (pendantMech M) ρ (.inl o) t

/-- The times of the lattice moves of the walk on `G_M`. -/
noncomputable def latTime : ℕ → ℕ
  | 0 => 2 * leafVisits M (nbrIdx M (ρ (.inl o)))
  | s + 1 => latTime s + 1 + 2 * leafVisits M (nbrIdx M (ρpend M ρ o (latTime s + 1) (.inl (Ysq M ρ o (s + 1)))))

theorem walk_add (t k : ℕ) : walk (pendantMech M) ρ (.inl o) (t + k) =
    (step (pendantMech M))^[k] (walk (pendantMech M) ρ (.inl o) t) := by
  rw [walk, walk, add_comm, Function.iterate_add_apply]

theorem walk_eq (t : ℕ) : walk (pendantMech M) ρ (.inl o) t = ⟨Xpend M ρ o t, ρpend M ρ o t⟩ := rfl

theorem leafVisits_le (k : Fin (M + 4)) : leafVisits M k ≤ M := by
  unfold leafVisits; split_ifs <;> omega

/-- The leaf phase from a lattice vertex at time `t`. -/
theorem leaf_phase_at (t : ℕ) (v : Site) (hpos : Xpend M ρ o t = .inl v) :
    let k := nbrIdx M (ρpend M ρ o t (.inl v))
    (Xpend M ρ o (t + 2 * leafVisits M k) = .inl v ∧
      induce M (ρpend M ρ o (t + 2 * leafVisits M k)) = induce M (ρpend M ρ o t) ∧
      ∃ k' : Fin (M + 4), ρpend M ρ o (t + 2 * leafVisits M k) (.inl v) = pendantNbrLattice M v k' ∧
        ((k' : ℕ) ≤ 2 ∨ (k' : ℕ) = M + 3)) ∧
    ∀ j ≤ 2 * leafVisits M k, Xpend M ρ o (t + j) = .inl v ∨ ∃ i : Fin M, Xpend M ρ o (t + j) = .inr (v, i) := by
  intro k
  have hρ : ρpend M ρ o t (.inl v) = pendantNbrLattice M v k := by
    simp [k, nbrIdx]
  have hw : walk (pendantMech M) ρ (.inl o) t = ⟨.inl v, ρpend M ρ o t⟩ := by
    rw [walk_eq, hpos]
  by_cases hk : (k : ℕ) ≤ 2
  · have h0 : leafVisits M k = 0 := by simp [leafVisits, hk]
    rw [h0]
    refine ⟨⟨by simpa using hpos, by simp, k, by simpa using hρ, Or.inl hk⟩, fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    exact Or.inl (by simpa using hpos)
  · push_neg at hk
    have hn : (k : ℕ) + (M + 3 - k) = M + 3 := by
      have := k.isLt; omega
    have hlv : leafVisits M k = M + 3 - k := by simp [leafVisits]; omega
    obtain ⟨hend, hpos'⟩ := leaf_phase M v (M + 3 - k) (ρpend M ρ o t) k hρ (by omega) hn
    rw [hlv]
    refine ⟨?_, fun j hj => ?_⟩
    · have hwalk : walk (pendantMech M) ρ (.inl o) (t + 2 * (M + 3 - k)) =
          ⟨.inl v, Function.update (ρpend M ρ o t) (.inl v) (pendantNbrLattice M v (lastLeaf M))⟩ := by
        rw [walk_add, hw, hend]
      refine ⟨?_, ?_, lastLeaf M, ?_, Or.inr rfl⟩
      · show (walk (pendantMech M) ρ (.inl o) (t + 2 * (M + 3 - k))).pos = _
        rw [hwalk]
      · show induce M (walk (pendantMech M) ρ (.inl o) (t + 2 * (M + 3 - k))).rotor = _
        rw [hwalk]
        exact induce_update_lastLeaf M _ v k hρ (by omega)
      · show (walk (pendantMech M) ρ (.inl o) (t + 2 * (M + 3 - k))).rotor (.inl v) = _
        rw [hwalk]
        simp
    · have hj' := hpos' j hj
      have hwj : walk (pendantMech M) ρ (.inl o) (t + j) =
          (step (pendantMech M))^[j] ⟨.inl v, ρpend M ρ o t⟩ := by rw [walk_add, hw]
      show (walk (pendantMech M) ρ (.inl o) (t + j)).pos = _ ∨ ∃ i, (walk (pendantMech M) ρ (.inl o) (t + j)).pos = _
      rw [hwj]
      by_cases he : Even j
      · exact Or.inl (hj'.1 he)
      · exact Or.inr (hj'.2 he)

/-- The simulation invariant at the lattice-move times. -/
theorem sim : ∀ s : ℕ,
    Xpend M ρ o (latTime M ρ o s) = .inl (Ysq M ρ o s) ∧
    induce M (ρpend M ρ o (latTime M ρ o s)) = σsq M ρ o s ∧
    ∃ k : Fin (M + 4), ρpend M ρ o (latTime M ρ o s) (.inl (Ysq M ρ o s)) = pendantNbrLattice M (Ysq M ρ o s) k ∧
      ((k : ℕ) ≤ 2 ∨ (k : ℕ) = M + 3)
  | 0 => by
    have := (leaf_phase_at M ρ o 0 o rfl).1
    simpa [latTime] using this
  | s + 1 => by
    obtain ⟨hpos, hind, k, hk, hk2⟩ := sim s
    obtain ⟨hlt, hstep⟩ := step_lattice M (ρpend M ρ o (latTime M ρ o s)) (Ysq M ρ o s) k hk hk2
    -- the lattice move
    have hw1 : walk (pendantMech M) ρ (.inl o) (latTime M ρ o s + 1) =
        ⟨.inl (Ysq M ρ o s + dirVec (latDir M (k + 1))),
          Function.update (ρpend M ρ o (latTime M ρ o s)) (.inl (Ysq M ρ o s)) (pendantNbrLattice M (Ysq M ρ o s) (k + 1))⟩ := by
      rw [walk_add, walk_eq, hpos, Function.iterate_one, hstep]
    -- the square walk
    have hσ : rot clockwise (induce M ρ) o s (X clockwise (induce M ρ) o s) =
        nbr (X clockwise (induce M ρ) o s) (latDir M k) := by
      show σsq M ρ o s (Ysq M ρ o s) = _
      rw [← hind]; simp [induce, hk, nbrIdx_nbrLattice]
    have hY : Ysq M ρ o (s + 1) = Ysq M ρ o s + dirVec (latDir M (k + 1)) := by
      show X clockwise (induce M ρ) o (s + 1) = X clockwise (induce M ρ) o s + dirVec (latDir M (k + 1))
      rw [X_succ, hσ, latDir_succ M k hk2]
      show (turnAt _ _).1 = _
      rw [turnAt_nbr]
      rfl
    have hpos1 : Xpend M ρ o (latTime M ρ o s + 1) = .inl (Ysq M ρ o (s + 1)) := by
      show (walk (pendantMech M) ρ (.inl o) (latTime M ρ o s + 1)).pos = _
      rw [hw1, hY]
    have hind1 : induce M (ρpend M ρ o (latTime M ρ o s + 1)) = σsq M ρ o (s + 1) := by
      show induce M (walk (pendantMech M) ρ (.inl o) (latTime M ρ o s + 1)).rotor = _
      rw [hw1]
      show induce M (Function.update (ρpend M ρ o (latTime M ρ o s)) (Sum.inl (Ysq M ρ o s))
        (pendantNbrLattice M (Ysq M ρ o s) (k + 1))) = _
      rw [induce_update M (ρpend M ρ o (latTime M ρ o s)) (Ysq M ρ o s) (k + 1), hind]
      show _ = rot clockwise (induce M ρ) o (s + 1)
      rw [rot_succ, hσ, latDir_succ M k hk2]
      show _ = Function.update (rot clockwise (induce M ρ) o s) (X clockwise (induce M ρ) o s)
        (turnAt (X clockwise (induce M ρ) o s) (nbr (X clockwise (induce M ρ) o s) (latDir M k)))
      rw [turnAt_nbr]
    -- the leaf phase at `Y (s+1)`
    have := (leaf_phase_at M ρ o (latTime M ρ o s + 1) (Ysq M ρ o (s + 1)) hpos1).1
    rw [hind1] at this
    simpa [latTime] using this

theorem latTime_succ_ge (s : ℕ) : latTime M ρ o s + 1 ≤ latTime M ρ o (s + 1) := by
  simp only [latTime]; omega

theorem latTime_mono {s s' : ℕ} (h : s ≤ s') : latTime M ρ o s ≤ latTime M ρ o s' := by
  induction s' with
  | zero => rw [Nat.le_zero.1 h]
  | succ s' ih =>
    rcases Nat.lt_or_ge s (s' + 1) with h' | h'
    · exact (ih (by omega)).trans (by have := latTime_succ_ge M ρ o s'; omega)
    · rw [Nat.le_antisymm h h']

theorem le_latTime (s : ℕ) : s ≤ latTime M ρ o s := by
  induction s with
  | zero => exact Nat.zero_le _
  | succ s ih => have := latTime_succ_ge M ρ o s; omega

/-- The lattice move at time `latTime s`. -/
theorem lattice_move (s : ℕ) :
    Xpend M ρ o (latTime M ρ o s + 1) = .inl (Ysq M ρ o (s + 1)) ∧
    traversal (pendantMech M) ρ (.inl o) (latTime M ρ o s) = (.inl (Ysq M ρ o s), .inl (Ysq M ρ o (s + 1))) := by
  obtain ⟨hpos, hind, k, hk, hk2⟩ := sim M ρ o s
  obtain ⟨hlt, hstep⟩ := step_lattice M (ρpend M ρ o (latTime M ρ o s)) (Ysq M ρ o s) k hk hk2
  have hw1 : walk (pendantMech M) ρ (.inl o) (latTime M ρ o s + 1) =
      ⟨.inl (Ysq M ρ o s + dirVec (latDir M (k + 1))),
        Function.update (ρpend M ρ o (latTime M ρ o s)) (.inl (Ysq M ρ o s))
          (pendantNbrLattice M (Ysq M ρ o s) (k + 1))⟩ := by
    rw [walk_add, walk_eq, hpos, Function.iterate_one, hstep]
  have hσ : rot clockwise (induce M ρ) o s (X clockwise (induce M ρ) o s) =
      nbr (X clockwise (induce M ρ) o s) (latDir M k) := by
    show σsq M ρ o s (Ysq M ρ o s) = _
    rw [← hind]; simp [induce, hk, nbrIdx_nbrLattice]
  have hY : Ysq M ρ o (s + 1) = Ysq M ρ o s + dirVec (latDir M (k + 1)) := by
    show X clockwise (induce M ρ) o (s + 1) = X clockwise (induce M ρ) o s + dirVec (latDir M (k + 1))
    rw [X_succ, hσ, latDir_succ M k hk2]
    show (turnAt _ _).1 = _
    rw [turnAt_nbr]
    rfl
  have hpos1 : Xpend M ρ o (latTime M ρ o s + 1) = .inl (Ysq M ρ o (s + 1)) := by
    show (walk (pendantMech M) ρ (.inl o) (latTime M ρ o s + 1)).pos = _
    rw [hw1, hY]
  exact ⟨hpos1, Prod.ext hpos hpos1⟩

/-- Between consecutive lattice moves the walker is at the current lattice vertex or one of
its leaves. -/
theorem pos_between (s t : ℕ) (h1 : latTime M ρ o s < t) (h2 : t ≤ latTime M ρ o (s + 1)) :
    Xpend M ρ o t = .inl (Ysq M ρ o (s + 1)) ∨ ∃ i : Fin M, Xpend M ρ o t = .inr (Ysq M ρ o (s + 1), i) := by
  have hpos1 := (lattice_move M ρ o s).1
  have := (leaf_phase_at M ρ o (latTime M ρ o s + 1) (Ysq M ρ o (s + 1)) hpos1).2 (t - (latTime M ρ o s + 1))
    (by simp only [latTime] at h2; omega)
  rwa [Nat.add_sub_cancel' (by omega)] at this

theorem pos_initial (t : ℕ) (ht : t ≤ latTime M ρ o 0) :
    Xpend M ρ o t = .inl o ∨ ∃ i : Fin M, Xpend M ρ o t = .inr (o, i) := by
  have := (leaf_phase_at M ρ o 0 o rfl).2 t (by simpa [latTime] using ht)
  simpa using this

theorem exists_between (t : ℕ) (ht : latTime M ρ o 0 < t) :
    ∃ s, latTime M ρ o s < t ∧ t ≤ latTime M ρ o (s + 1) := by
  classical
  have hex : ∃ s, t ≤ latTime M ρ o (s + 1) := ⟨t, by have := le_latTime M ρ o (t + 1); omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; exact ht
  · obtain ⟨s', hs'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have := Nat.find_min hex (show s' < Nat.find hex by omega)
    rw [hs']; push_neg at this; exact this

/-- If the induced walk never returns to `o`, the walk on `G_M` visits `o` only during the
initial leaf phase, hence finitely often. -/
theorem visits_subset_of_no_return (h : ∀ s, 1 ≤ s → Ysq M ρ o s ≠ o) :
    {t | Xpend M ρ o t = .inl o} ⊆ Set.Iic (latTime M ρ o 0) := by
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  by_contra hlt
  simp only [Set.mem_Iic, not_le] at hlt
  obtain ⟨s, hs1, hs2⟩ := exists_between M ρ o t hlt
  rcases pos_between M ρ o s t hs1 hs2 with h' | ⟨i, h'⟩
  · rw [ht] at h'
    exact h (s + 1) (by omega) (Sum.inl_injective h').symm
  · rw [ht] at h'
    exact Sum.inl_ne_inr h'

theorem not_recurrent_of_no_return (h : ∀ s, 1 ≤ s → Ysq M ρ o s ≠ o) :
    ¬ Recurrent (pendantMech M) ρ (.inl o) := by
  intro hrec
  have := hrec (.inl o)
  exact this ((Set.finite_Iic _).subset (visits_subset_of_no_return M ρ o h))

end Simulation


end Rotor
