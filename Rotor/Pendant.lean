/-
The graph `G_M`: the square lattice with `M` leaves attached to every lattice
vertex, `rotor.tex:291-299` and Section 6:

  "For an integer `M ≥ 1`, let `G_M` be the square lattice with `M` leaves
   attached to every lattice vertex, all of them drawn between the edge to the
   west and the edge to the north, so that the clockwise order at a lattice
   vertex is `N, E, S, W, L_1, …, L_M`."

  M-020  The vertices of `G_M` are `Site ⊕ (Site × Fin M)`: lattice sites and
         the leaves `(v, i)` attached to `v`.  The leaf `(v, i)` is drawn at
         `v + ((i+1)/(2(M+1))) • (-1, 1)`, in the open quadrant between the
         west and north edges of `v`, which makes the drawing injective.  At a
         leaf the mechanism is the identity on its single neighbor.
-/
import Rotor.Dual

open Fin.NatCast

namespace Rotor

/-- The vertices of `G_M`. -/
abbrev PVertex (M : ℕ) := Site ⊕ (Site × Fin M)

/-- Adjacency in `G_M`: lattice edges, and each leaf to its lattice vertex. -/
def pendantAdj (M : ℕ) : PVertex M → PVertex M → Prop
  | .inl u, .inl v => squareGraph.Adj u v
  | .inl u, .inr w => u = w.1
  | .inr w, .inl v => w.1 = v
  | .inr _, .inr _ => False

/-- The graph `G_M`. -/
def pendantGraph (M : ℕ) : SimpleGraph (PVertex M) where
  Adj := pendantAdj M
  symm x y h := by
    cases x <;> cases y <;> simp only [pendantAdj] at h ⊢
    · exact squareGraph.symm h
    · exact h.symm
    · exact h.symm
  loopless x h := by
    cases x <;> simp only [pendantAdj] at h
    exact squareGraph.loopless _ h

/-- The neighbors of a lattice vertex of `G_M`: the four lattice directions and
the `M` leaves, in the clockwise order `N, E, S, W, L_1, …, L_M`. -/
def pendantNbrLattice (M : ℕ) (v : Site) : Fin (M + 4) ≃ (pendantGraph M).neighborSet (.inl v) where
  toFun k := if h : (k : ℕ) < 4 then ⟨.inl (v + dirVec ⟨k, h⟩), adj_add_dirVec v ⟨k, h⟩⟩
    else ⟨.inr (v, ⟨k - 4, by omega⟩), rfl⟩
  invFun w :=
    match w with
    | ⟨.inl u, h⟩ => ⟨(dirOf (u - v) : ℕ), by have := (dirOf (u - v)).2; omega⟩
    | ⟨.inr (_, i), _⟩ => ⟨4 + i, by omega⟩
  left_inv k := by
    by_cases h : (k : ℕ) < 4
    · simp only [h, dite_true]
      ext
      simp [dirOf_dirVec]
    · simp only [h, dite_false]
      ext
      simp
      omega
  right_inv w := by
    rcases w with ⟨u | ⟨u, i⟩, h⟩
    · have hd : (dirOf (u - v) : ℕ) < 4 := (dirOf (u - v)).2
      simp only [hd, dite_true]
      ext
      simp only [Fin.eta]
      exact congrArg Sum.inl (dirVec_dirOf_of_adj h)
    · have h' : v = u := by simpa [pendantGraph, pendantAdj] using h
      subst h'
      have : ¬ (4 + (i : ℕ) < 4) := by omega
      simp only [this, dite_false]
      ext
      simp

/-- The single neighbor of a leaf. -/
def pendantNbrLeaf (M : ℕ) (w : Site × Fin M) : Unit ≃ (pendantGraph M).neighborSet (.inr w) where
  toFun _ := ⟨.inl w.1, rfl⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨u | u, h⟩
    · have : w.1 = u := by simpa [pendantGraph, pendantAdj] using h
      subst this; rfl
    · simp [pendantGraph, pendantAdj] at h

instance (M : ℕ) : (pendantGraph M).LocallyFinite := fun v =>
  match v with
  | .inl v => Fintype.ofEquiv _ (pendantNbrLattice M v)
  | .inr w => Fintype.ofEquiv _ (pendantNbrLeaf M w)

/-- Turning by one position in the clockwise order `N, E, S, W, L_1, …, L_M`
at a lattice vertex. -/
def pendantTurn (M : ℕ) (v : Site) : Equiv.Perm ((pendantGraph M).neighborSet (.inl v)) :=
  (pendantNbrLattice M v).symm.trans ((Equiv.addRight (1 : Fin (M + 4))).trans (pendantNbrLattice M v))

theorem pendantTurn_pow (M : ℕ) (v : Site) (k : ℕ) (a : Fin (M + 4)) :
    ((pendantTurn M v) ^ k) (pendantNbrLattice M v a) = pendantNbrLattice M v (a + (k : Fin (M + 4))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    simp only [pendantTurn, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.coe_addRight]
    congr 1
    rw [Nat.cast_succ, add_assoc]

/-- The clockwise rotor mechanism on `G_M`: order `N, E, S, W, L_1, …, L_M` at
lattice vertices, the identity at leaves. -/
def pendantMech (M : ℕ) : Mechanism (pendantGraph M) where
  next x := match x with
    | .inl v => pendantTurn M v
    | .inr _ => Equiv.refl _
  cyclic x a b := by
    match x with
    | .inl v =>
      obtain ⟨i, rfl⟩ := (pendantNbrLattice M v).surjective a
      obtain ⟨j, rfl⟩ := (pendantNbrLattice M v).surjective b
      refine ⟨(j - i).val, ?_⟩
      show ((pendantTurn M v) ^ (j - i).val) _ = _
      rw [pendantTurn_pow, Fin.cast_val_eq_self]
      congr 1
      exact add_sub_cancel i j
    | .inr w =>
      refine ⟨0, ?_⟩
      have : a = b := (pendantNbrLeaf M w).symm.injective rfl
      simp [this]
  nonempty x := match x with
    | .inl v => ⟨pendantNbrLattice M v (0 : Fin (M + 4))⟩
    | .inr w => ⟨pendantNbrLeaf M w ()⟩

/-- The drawing of `G_M` in the plane (ruling M-020). -/
noncomputable def pendantEmb (M : ℕ) : PVertex M → Plane
  | .inl v => squareEmb v
  | .inr (v, i) => squareEmb v + (((i : ℕ) + 1 : ℝ) / (2 * ((M : ℝ) + 1))) • WithLp.toLp 2 ![(-1 : ℝ), 1]

/-- The lattice action on `G_M`. -/
def pendantShift (M : ℕ) (z : Site) : PVertex M → PVertex M
  | .inl v => .inl (v + z)
  | .inr (v, i) => .inr (v + z, i)

end Rotor

namespace Rotor

theorem pendantEmb_injective (M : ℕ) : Function.Injective (pendantEmb M) := by
  intro x y h
  rcases x with u | ⟨u, i⟩ <;> rcases y with v | ⟨v, j⟩
  · exact congrArg Sum.inl (squareEmb_injective (by simpa [pendantEmb] using h))
  all_goals
    have h' := congrArg WithLp.ofLp h
    simp only [pendantEmb, squareEmb, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_toLp] at h'
    have h0 := congrFun h' 0
    have h1 := congrFun h' 1
    simp at h0 h1
  · -- a lattice point against a leaf: the leaf's coordinates are not integers
    exfalso
    have hM : (0 : ℝ) < 2 * ((M : ℝ) + 1) := by positivity
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj' : ((j : ℝ) + 1) / (2 * ((M : ℝ) + 1)) < 1 := by
      rw [div_lt_one hM]
      have hjM : ((j : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast j.2
      linarith
    have : (u.1 : ℝ) - v.1 = -(((j : ℝ) + 1) / (2 * ((M : ℝ) + 1))) := by linarith
    have hint : ∃ k : ℤ, (k : ℝ) = -(((j : ℝ) + 1) / (2 * ((M : ℝ) + 1))) := ⟨u.1 - v.1, by push_cast; linarith⟩
    obtain ⟨k, hk⟩ := hint
    have : (-1 : ℝ) < k ∧ (k : ℝ) < 0 := by
      constructor <;> · rw [hk]; linarith [div_pos hj hM]
    have : (-1 : ℤ) < k ∧ k < 0 := by exact_mod_cast this
    omega
  · exfalso
    have hM : (0 : ℝ) < 2 * ((M : ℝ) + 1) := by positivity
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hi' : ((i : ℝ) + 1) / (2 * ((M : ℝ) + 1)) < 1 := by
      rw [div_lt_one hM]
      have hiM : ((i : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast i.2
      linarith
    have hint : ∃ k : ℤ, (k : ℝ) = ((i : ℝ) + 1) / (2 * ((M : ℝ) + 1)) := ⟨u.1 - v.1, by push_cast; linarith⟩
    obtain ⟨k, hk⟩ := hint
    have : (0 : ℝ) < k ∧ (k : ℝ) < 1 := by
      constructor <;> · rw [hk]; linarith [div_pos hi hM]
    have : (0 : ℤ) < k ∧ k < 1 := by exact_mod_cast this
    omega
  · -- two leaves: the difference of coordinates is an integer of size less than one
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hiM : ((i : ℕ) : ℝ) < M := by exact_mod_cast i.2
    have hjM : ((j : ℕ) : ℝ) < M := by exact_mod_cast j.2
    set a : ℝ := ((i : ℝ) + 1) / (2 * ((M : ℝ) + 1)) with ha
    set b : ℝ := ((j : ℝ) + 1) / (2 * ((M : ℝ) + 1)) with hb
    have hab : 2 * a - 2 * b = (((i : ℕ) : ℝ) - (j : ℕ)) / ((M : ℝ) + 1) := by
      rw [ha, hb]; field_simp; ring
    have hk : (((u.1 - u.2) - (v.1 - v.2) : ℤ) : ℝ) = (((i : ℕ) : ℝ) - (j : ℕ)) / ((M : ℝ) + 1) := by
      rw [← hab]; push_cast; linarith
    have hlt : (((i : ℕ) : ℝ) - (j : ℕ)) / ((M : ℝ) + 1) < 1 := by
      rw [div_lt_one hM]; have : (0 : ℝ) ≤ (j : ℕ) := by positivity
      linarith
    have hgt : (-1 : ℝ) < (((i : ℕ) : ℝ) - (j : ℕ)) / ((M : ℝ) + 1) := by
      rw [lt_div_iff₀ hM]; have : (0 : ℝ) ≤ (i : ℕ) := by positivity
      linarith
    have hk0 : ((u.1 - u.2) - (v.1 - v.2) : ℤ) = 0 := by
      have h1' : (-1 : ℝ) < (((u.1 - u.2) - (v.1 - v.2) : ℤ) : ℝ) := by rw [hk]; exact hgt
      have h2' : (((u.1 - u.2) - (v.1 - v.2) : ℤ) : ℝ) < 1 := by rw [hk]; exact hlt
      have h1'' : (-1 : ℤ) < (u.1 - u.2) - (v.1 - v.2) := by exact_mod_cast h1'
      have h2'' : (u.1 - u.2) - (v.1 - v.2) < (1 : ℤ) := by exact_mod_cast h2'
      omega
    have hij : ((i : ℕ) : ℝ) = (j : ℕ) := by
      have : (((i : ℕ) : ℝ) - (j : ℕ)) / ((M : ℝ) + 1) = 0 := by rw [← hk, hk0]; simp
      rw [div_eq_zero_iff] at this
      rcases this with h | h
      · linarith
      · linarith
    have hij' : i = j := Fin.ext (by exact_mod_cast hij)
    subst hij'
    have hab' : a = b := by rw [ha, hb]
    have hu1 : (u.1 : ℝ) = v.1 := by linarith
    have hu2 : (u.2 : ℝ) = v.2 := by linarith
    have : u = v := Prod.ext (by exact_mod_cast hu1) (by exact_mod_cast hu2)
    subst this
    rfl

end Rotor
