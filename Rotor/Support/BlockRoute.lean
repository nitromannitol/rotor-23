import Rotor.Support.FiniteProduct

namespace Rotor

/-- `l` contains `q` consecutively, in either direction. -/
def Traverses (l q : List Site) : Prop :=
  ∃ i, (l.drop i).take q.length = q ∨ (l.drop i).take q.length = q.reverse

/-- The boundary of the block `[0,4]²` in cyclic order. -/
def bd4 : List Site :=
  [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(3,4),(2,4),(1,4),(0,4),(0,3),(0,2),(0,1)]

/-- The copy of `P⋆` inside the block. -/
def copy0 : List Site := pstar.map (· + (1, 1))

def inBox4 (v : Site) : Prop := 0 ≤ v.1 ∧ v.1 ≤ 4 ∧ 0 ≤ v.2 ∧ v.2 ≤ 4

instance : DecidablePred inBox4 := fun v => by unfold inBox4; infer_instance

/-- Forward arc of the boundary cycle from index `i` to index `j`. -/
def arcF (i j : ℕ) : List Site :=
  (List.range ((j + 16 - i) % 16 + 1)).map (fun k => bd4.getD ((i + k) % 16) (0, 0))

/-- Backward arc of the boundary cycle from index `i` to index `j`. -/
def arcB (i j : ℕ) : List Site :=
  (List.range ((i + 16 - j) % 16 + 1)).map (fun k => bd4.getD ((i + 16 - k) % 16) (0, 0))

/-- Candidate routes from `bd4[i]` to `bd4[j]` through the copy: the foot `(0,1)` has index
`15`, the foot `(4,3)` has index `7`. -/
def cands (i j : ℕ) : List (List Site) :=
  [arcF i 15 ++ copy0 ++ [(3, 3)] ++ arcF 7 j,
   arcF i 15 ++ copy0 ++ [(3, 3)] ++ arcB 7 j,
   arcB i 15 ++ copy0 ++ [(3, 3)] ++ arcF 7 j,
   arcB i 15 ++ copy0 ++ [(3, 3)] ++ arcB 7 j,
   arcF i 7 ++ [(3, 3)] ++ copy0.reverse ++ arcF 15 j,
   arcF i 7 ++ [(3, 3)] ++ copy0.reverse ++ arcB 15 j,
   arcB i 7 ++ [(3, 3)] ++ copy0.reverse ++ arcF 15 j,
   arcB i 7 ++ [(3, 3)] ++ copy0.reverse ++ arcB 15 j]

def OkRoute (l : List Site) (s t : Site) : Prop :=
  IsPath squareGraph l ∧ l.head? = some s ∧ l.getLast? = some t ∧ (∀ v ∈ l, inBox4 v) ∧
    ∃ i, i < l.length ∧ ((l.drop i).take 6 = copy0 ∨ (l.drop i).take 6 = copy0.reverse)

instance (l : List Site) (s t : Site) : Decidable (OkRoute l s t) := by
  unfold OkRoute IsPath; infer_instance

set_option maxRecDepth 100000 in
theorem route_table : ∀ i j : Fin 16, i ≠ j →
    ∃ l ∈ cands i j, OkRoute l (bd4.getD i (0, 0)) (bd4.getD j (0, 0)) := by decide

end Rotor
