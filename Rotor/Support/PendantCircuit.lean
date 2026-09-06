import Rotor.Support.PendantInduced
import Rotor.Frozen.Circuits.OneCircuit

/-!
The first return of the induced walk (`rotor.tex:2245-2252`): the lattice edges traversed
by the walk on `G_M` up to the induced walk's first return to `o` are distinct, by
`lem:one-circuit` applied to `G_M`, because the walk has visited `o` at most `M + 1` times
before the return, fewer than the `M + 4` visits that complete a circuit.
-/

open Finset

namespace Rotor

variable (M : ℕ) (ρ : Config (pendantGraph M)) (o : Site)

theorem latTime_zero_even : ∃ n ≤ M, latTime M ρ o 0 = 2 * n :=
  ⟨leafVisits M (nbrIdx M (ρ (.inl o))), leafVisits_le M _, rfl⟩

/-- During the initial leaf phase the walker is at `o` only at even times. -/
theorem even_of_pos_initial (t : ℕ) (ht : t ≤ latTime M ρ o 0) (h : Xpend M ρ o t = .inl o) :
    Even t := by
  by_contra hodd
  have hρ : ρ (.inl o) = pendantNbrLattice M o (nbrIdx M (ρ (.inl o))) := by simp [nbrIdx]
  set k := nbrIdx M (ρ (.inl o)) with hk
  by_cases hk2 : (k : ℕ) ≤ 2
  · have : latTime M ρ o 0 = 0 := by
      show 2 * leafVisits M k = 0
      simp [leafVisits, hk2]
    rw [this] at ht
    have : t = 0 := by omega
    subst this
    exact hodd ⟨0, rfl⟩
  · push_neg at hk2
    have hn : (k : ℕ) + (M + 3 - k) = M + 3 := by have := k.isLt; omega
    obtain ⟨-, hpos⟩ := leaf_phase M o (M + 3 - k) ρ k hρ (by omega) hn
    have hlt : latTime M ρ o 0 = 2 * (M + 3 - k) := by
      show 2 * leafVisits M k = _
      have : ¬ (k : ℕ) ≤ 2 := by omega
      simp [leafVisits, this]
    obtain ⟨i, hi⟩ := (hpos t (by omega)).2 hodd
    have : Xpend M ρ o t = ((step (pendantMech M))^[t] ⟨.inl o, ρ⟩).pos := rfl
    rw [this, hi] at h
    exact Sum.inr_ne_inl h

/-- Before the induced walk's first return, `o` has been visited at most `M + 1` times. -/
theorem visits_le_of_no_return {r : ℕ} (hr : ∀ s, 1 ≤ s → s < r → Ysq M ρ o s ≠ o)
    {t : ℕ} (ht : t ≤ latTime M ρ o (r - 1) + 1) :
    visits (pendantMech M) ρ (.inl o) t ≤ M + 1 := by
  classical
  obtain ⟨n, hnM, hn⟩ := latTime_zero_even M ρ o
  have hsub : (range t).filter (fun s => X (pendantMech M) ρ (.inl o) s = .inl o) ⊆
      (range (n + 1)).image (fun j => 2 * j) := by
    intro t' ht'
    rw [mem_filter, mem_range] at ht'
    obtain ⟨htt, hX⟩ := ht'
    have hle0 : t' ≤ latTime M ρ o 0 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨s, hs1, hs2⟩ := exists_between M ρ o t' hgt
      have hs : s + 1 < r := by
        by_contra hge
        push_neg at hge
        have := latTime_mono M ρ o (show r - 1 ≤ s by omega)
        omega
      rcases pos_between M ρ o s t' hs1 hs2 with h' | ⟨i, h'⟩
      · have := hr (s + 1) (by omega) hs
        exact this (Sum.inl_injective (h'.symm.trans hX))
      · exact Sum.inr_ne_inl (h'.symm.trans hX)
    obtain ⟨j, hj⟩ := even_of_pos_initial M ρ o t' hle0 hX
    rw [mem_image]
    exact ⟨j, mem_range.2 (by omega), by omega⟩
  calc visits (pendantMech M) ρ (.inl o) t
      ≤ ((range (n + 1)).image (fun j => 2 * j)).card := card_le_card hsub
    _ ≤ (range (n + 1)).card := card_image_le
    _ = n + 1 := card_range _
    _ ≤ M + 1 := by omega

theorem T_zero_le : T (pendantMech M) ρ (.inl o) 0 ≤ 0 :=
  T_le_of_mem _ _ _ _ ⟨rfl, Nat.zero_le _⟩

/-- The first induced return happens before the first circuit of the walk on `G_M`. -/
theorem latTime_lt_T_one {r : ℕ} (hr : ∀ s, 1 ≤ s → s < r → Ysq M ρ o s ≠ o) :
    (latTime M ρ o (r - 1) : ℕ∞) < T (pendantMech M) ρ (.inl o) 1 := by
  by_contra hle
  push_neg at hle
  have hlt : T (pendantMech M) ρ (.inl o) 1 < ⊤ := lt_of_le_of_lt hle (WithTop.coe_lt_top _)
  have hmem := T_mem (pendantMech M) ρ (.inl o) 1 hlt
  obtain ⟨-, hvis⟩ := hmem
  rw [pendantGraph_degree_inl, mul_one] at hvis
  have ht : (T (pendantMech M) ρ (.inl o) 1).toNat ≤ latTime M ρ o (r - 1) :=
    ENat.toNat_le_of_le_coe hle
  have := visits_le_of_no_return M ρ o hr (t := (T (pendantMech M) ρ (.inl o) 1).toNat) (by omega)
  omega

/-- The induced walk's traversals up to its first return are distinct. -/
theorem induced_traversal_injective (hFLP : External.OneCircuit (pendantGraph M)) {r : ℕ}
    (hr : ∀ s, 1 ≤ s → s < r → Ysq M ρ o s ≠ o) {a b : ℕ} (hab : a < b) (hb : b ≤ r - 1) :
    (Ysq M ρ o a, Ysq M ρ o (a + 1)) ≠ (Ysq M ρ o b, Ysq M ρ o (b + 1)) := by
  intro heq
  have h0 : T (pendantMech M) ρ (.inl o) 0 < ⊤ :=
    lt_of_le_of_lt (T_zero_le M ρ o) (WithTop.coe_lt_top 0)
  have hdist := (Rotor.Frozen.one_circuit hFLP (pendantMech M) (pendantGraph_connected M) ρ
    (.inl o) 0 h0).1 (latTime M ρ o a) (latTime M ρ o b)
    ((T_zero_le M ρ o).trans (by exact_mod_cast Nat.zero_le _))
    (lt_of_lt_of_le (by have := latTime_succ_ge M ρ o a; omega)
      (latTime_mono M ρ o (show a + 1 ≤ b by omega)))
    (lt_of_le_of_lt (by exact_mod_cast latTime_mono M ρ o hb) (latTime_lt_T_one M ρ o hr))
  apply hdist
  rw [(lattice_move M ρ o a).2, (lattice_move M ρ o b).2]
  simp only [Prod.mk.injEq] at heq ⊢
  exact ⟨congrArg Sum.inl heq.1, congrArg Sum.inl heq.2⟩

end Rotor
