/-
Basic facts about the walk of `Rotor/Model.lean`: one step, rotors change only
at visited vertices, the range grows, and the circuit times `T n` attain their
defining conditions.
-/
import Rotor.Support.BoundaryRouting

open Finset

namespace Rotor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
variable (π : Mechanism G)

theorem walk_succ (ρ : Config G) (o : V) (t : ℕ) :
    walk π ρ o (t + 1) = step π (walk π ρ o t) := by
  rw [walk, Function.iterate_succ', Function.comp_apply, walk]

theorem X_succ (ρ : Config G) (o : V) (t : ℕ) :
    X π ρ o (t + 1) = (π.next (X π ρ o t) (rot π ρ o t (X π ρ o t))).1 := by
  rw [X, walk_succ]; rfl

theorem rot_succ (ρ : Config G) (o : V) (t : ℕ) :
    rot π ρ o (t + 1) = Function.update (rot π ρ o t) (X π ρ o t)
      (π.next (X π ρ o t) (rot π ρ o t (X π ρ o t))) := by
  rw [rot, walk_succ]; rfl

@[simp] theorem X_zero (ρ : Config G) (o : V) : X π ρ o 0 = o := rfl
@[simp] theorem rot_zero (ρ : Config G) (o : V) : rot π ρ o 0 = ρ := rfl

/-- The walk steps to a neighbor. -/
theorem adj_X_succ (ρ : Config G) (o : V) (t : ℕ) : G.Adj (X π ρ o t) (X π ρ o (t + 1)) := by
  rw [X_succ]; exact (π.next _ _).2

/-- `x ∈ R_t` iff the walk is at `x` at some time `≤ t`. -/
theorem mem_R (ρ : Config G) (o : V) (t : ℕ) (x : V) :
    x ∈ R π ρ o t ↔ ∃ s ≤ t, X π ρ o s = x := by
  simp [R, Finset.mem_image, Nat.lt_succ_iff]

theorem X_mem_R (ρ : Config G) (o : V) (s t : ℕ) (h : s ≤ t) : X π ρ o s ∈ R π ρ o t :=
  (mem_R π ρ o t _).2 ⟨s, h, rfl⟩

theorem R_mono (ρ : Config G) (o : V) {s t : ℕ} (h : s ≤ t) : R π ρ o s ⊆ R π ρ o t := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := (mem_R π ρ o s x).1 hx
  exact X_mem_R π ρ o u t (hu.trans h)

/-- A rotor never changes at a vertex the walk has not visited. -/
theorem rot_eq_of_not_mem_R (ρ : Config G) (o : V) (t : ℕ) (x : V) (hx : x ∉ R π ρ o t) :
    rot π ρ o t x = ρ x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hx' : x ∉ R π ρ o t := fun h => hx (R_mono π ρ o (Nat.le_succ t) h)
    have hne : x ≠ X π ρ o t := fun h => hx (h ▸ X_mem_R π ρ o t (t + 1) (Nat.le_succ t))
    rw [rot_succ, Function.update_of_ne hne, ih hx']

/-- The range after `t + 1` steps. -/
theorem R_succ (ρ : Config G) (o : V) (t : ℕ) :
    R π ρ o (t + 1) = insert (X π ρ o (t + 1)) (R π ρ o t) := by
  ext x
  simp only [mem_R, Finset.mem_insert]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases Nat.lt_or_ge s (t + 1) with h | h
    · exact Or.inr ⟨s, Nat.lt_succ_iff.1 h, rfl⟩
    · exact Or.inl (by rw [le_antisymm hs h])
  · rintro (rfl | ⟨s, hs, rfl⟩)
    · exact ⟨t + 1, le_rfl, rfl⟩
    · exact ⟨s, hs.trans (Nat.le_succ t), rfl⟩

/-! ### The circuit times -/

section
variable [G.LocallyFinite]

/-- The defining set of `T n`. -/
def circuitSet (ρ : Config G) (o : V) (n : ℕ) : Set ℕ :=
  {t : ℕ | X π ρ o t = o ∧ G.degree o * n ≤ visits π ρ o t}

theorem T_eq (ρ : Config G) (o : V) (n : ℕ) :
    T π ρ o n = ⨅ t ∈ circuitSet π ρ o n, (t : ℕ∞) := rfl

theorem T_le_of_mem (ρ : Config G) (o : V) (n : ℕ) {t : ℕ} (ht : t ∈ circuitSet π ρ o n) :
    T π ρ o n ≤ t := by
  rw [T_eq]; exact iInf₂_le t ht

/-- When `T n < ⊤`, its value is a member of the defining set. -/
theorem T_mem (ρ : Config G) (o : V) (n : ℕ) (h : T π ρ o n < ⊤) :
    (T π ρ o n).toNat ∈ circuitSet π ρ o n := by
  classical
  have hne : (circuitSet π ρ o n).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : T π ρ o n = ⊤ := by rw [T_eq, hemp]; simp
    rw [this] at h
    exact lt_irrefl _ h
  have hex : ∃ t, t ∈ circuitSet π ρ o n := hne
  have hmem : Nat.find hex ∈ circuitSet π ρ o n := Nat.find_spec hex
  have hle : T π ρ o n ≤ Nat.find hex := T_le_of_mem π ρ o n hmem
  have hge : ((Nat.find hex : ℕ) : ℕ∞) ≤ T π ρ o n := by
    rw [T_eq]
    exact le_iInf₂ (fun t ht => by exact_mod_cast Nat.find_min' hex ht)
  rw [le_antisymm hle hge, ENat.toNat_coe]
  exact hmem

/-- `T n` is the least element of its defining set. -/
theorem T_min (ρ : Config G) (o : V) (n : ℕ) {t : ℕ} (ht : t ∈ circuitSet π ρ o n) :
    (T π ρ o n).toNat ≤ t := by
  have := T_le_of_mem π ρ o n ht
  exact ENat.toNat_le_of_le_coe this

/-- At time `T n`, the walk is at `o`. -/
theorem X_T (ρ : Config G) (o : V) (n : ℕ) (h : T π ρ o n < ⊤) :
    X π ρ o (T π ρ o n).toNat = o := (T_mem π ρ o n h).1

/-- `T` is monotone. -/
theorem T_mono (ρ : Config G) (o : V) (n : ℕ) : T π ρ o n ≤ T π ρ o (n + 1) := by
  rw [T_eq, T_eq]
  refine le_iInf₂ (fun t ht => iInf₂_le t ⟨ht.1, ?_⟩)
  exact le_trans (Nat.mul_le_mul_left _ (Nat.le_succ n)) ht.2

end

end Rotor
