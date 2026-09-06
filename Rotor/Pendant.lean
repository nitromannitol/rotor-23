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
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only [pendantAdj] at h ⊢
    · exact h.symm
    · exact h.symm
    · exact h.symm⟩
  loopless := ⟨fun x h => by
    cases x <;> simp only [pendantAdj] at h
    exact squareGraph.irrefl h⟩

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
    · exact Subtype.ext (congrArg Sum.inl h)
    · exact h.elim

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
      simp only [pendantTurn_pow, Fin.cast_val_eq_self, add_sub_cancel]
    | .inr w =>
      exact ⟨0, (pendantNbrLeaf M w).symm.injective rfl⟩
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
  let t (i : Fin M) : ℝ := ((i : ℕ) + 1 : ℝ) / (2 * ((M : ℝ) + 1))
  have hM : (0 : ℝ) < 2 * ((M : ℝ) + 1) := by positivity
  have ht (i : Fin M) : 0 < t i ∧ t i < 1 := by
    constructor
    · dsimp [t]; positivity
    · dsimp [t]
      rw [div_lt_one hM]
      have hi : (i : ℝ) < M := by exact_mod_cast i.isLt
      linarith
  have frac (z : ℤ) (i : Fin M) : Int.fract ((z : ℝ) + t i) = t i := by
    rw [Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨(ht i).1.le, (ht i).2⟩]
  intro x y h
  rcases x with u | ⟨u, i⟩ <;> rcases y with v | ⟨v, j⟩
  · exact congrArg Sum.inl (squareEmb_injective h)
  all_goals
    have h1 := congrArg (fun p : Plane => p 1) h
    simp [pendantEmb, squareEmb] at h1
  · change (u.2 : ℝ) = (v.2 : ℝ) + t j at h1
    have hf := congrArg Int.fract h1
    rw [Int.fract_intCast, frac] at hf
    exact ((ht j).1.ne' hf.symm).elim
  · change (u.2 : ℝ) + t i = (v.2 : ℝ) at h1
    have hf := congrArg Int.fract h1
    rw [frac, Int.fract_intCast] at hf
    exact ((ht i).1.ne' hf).elim
  · change (u.2 : ℝ) + t i = (v.2 : ℝ) + t j at h1
    have htij := congrArg Int.fract h1
    rw [frac, frac] at htij
    have hij : (i : ℝ) + 1 = (j : ℝ) + 1 := (div_left_inj' hM.ne').mp htij
    have hij' : i = j := Fin.ext (by exact_mod_cast add_right_cancel hij)
    subst hij'
    exact congrArg Sum.inr (Prod.ext (squareEmb_injective (add_right_cancel h)) rfl)

end Rotor
