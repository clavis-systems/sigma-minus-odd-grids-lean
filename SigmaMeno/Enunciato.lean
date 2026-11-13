import Mathlib

/-!
# The σ⁻-game on grids with all sides odd: the statement

This file contains only the definitions and the statement of the main theorem of the note
"The σ⁻-game on grids with all sides odd, in every dimension" (E. Rizzan, version 2).
The theorem is written as a proposition (`TeoremaPrincipale : Prop`) and is **not** proved here.

The definitions follow the note, but with coordinates from `0` to `n i - 1` instead of from `1`
to `n i`. Adjacency is defined directly on cells, not through the matrices `J_i`.
-/

namespace SigmaMeno

open Finset

variable {d : ℕ}

/-- The cells of the grid with sides `n 0, …, n (d-1)`: one coordinate `ξ i ∈ {0, …, n i - 1}`
for each direction. -/
abbrev Cell (n : Fin d → ℕ) := (i : Fin d) → Fin (n i)

/-- **Edge** neighbourhood (□): the two cells differ by `1` in exactly one coordinate and are
equal in the others. -/
def EdgeAdj {n : Fin d → ℕ} (ξ η : Cell n) : Prop :=
  ∃ i, (((ξ i : ℕ) : ℤ) - ((η i : ℕ) : ℤ)).natAbs = 1 ∧ ∀ j, j ≠ i → ξ j = η j

/-- **King** neighbourhood (⊠): distinct cells that differ by at most `1` in every coordinate. -/
def KingAdj {n : Fin d → ℕ} (ξ η : Cell n) : Prop :=
  ξ ≠ η ∧ ∀ i, (((ξ i : ℕ) : ℤ) - ((η i : ℕ) : ℤ)).natAbs ≤ 1

instance {n : Fin d → ℕ} : DecidableRel (EdgeAdj (n := n)) := fun ξ η => by
  unfold EdgeAdj; infer_instance

instance {n : Fin d → ℕ} : DecidableRel (KingAdj (n := n)) := fun ξ η => by
  unfold KingAdj; infer_instance

/-- Pressing the set of cells `w` (a function with values in `𝔽₂`): each cell `ξ` changes state
once for each of its neighbours that is pressed. The pressed cell itself does not change
(the σ⁻ game). In terms of matrices, `press adj w = A · w` with `A` the adjacency matrix over
`𝔽₂`. -/
def press {V : Type*} [Fintype V] (adj : V → V → Prop) [DecidableRel adj]
    (w : V → ZMod 2) : V → ZMod 2 :=
  fun ξ => ∑ η ∈ univ.filter (fun η => adj ξ η), w η

/-- A configuration `x` is reachable (starting from all off) if there is a set of cells to press
that produces it. -/
def Reachable {V : Type*} [Fintype V] (adj : V → V → Prop) [DecidableRel adj]
    (x : V → ZMod 2) : Prop :=
  ∃ w : V → ZMod 2, press adj w = x

/-- The configuration with all lights on. -/
def allOn {V : Type*} : V → ZMod 2 := fun _ => 1

/-- The reflection of coordinate `i`: `ξ i ↦ n i - 1 - ξ i` (in the note `ξ_i ↦ n_i + 1 - ξ_i`,
with coordinates from `1`). -/
def reflect {n : Fin d → ℕ} (i : Fin d) (ξ : Cell n) : Cell n :=
  Function.update ξ i (Fin.rev (ξ i))

/-- Completely symmetric configuration: invariant under each reflection
(Florence–Meunier, Definition 0.3). -/
def CompletelySymmetric {n : Fin d → ℕ} (x : Cell n → ZMod 2) : Prop :=
  ∀ i ξ, x (reflect i ξ) = x ξ

/-- `a(n) = v₂(n + 1)`, the exponent of the largest power of `2` that divides `n + 1`. -/
def a (n : ℕ) : ℕ := padicValNat 2 (n + 1)

/-- Condition 3 of the note: in the multiset `{a(n_i) : a(n_i) ≥ 2}`, some value appears an odd
number of times. -/
def Condition3 (n : Fin d → ℕ) : Prop :=
  ∃ k, 2 ≤ k ∧ Odd (univ.filter (fun i => a (n i) = k)).card

/-- **The main theorem of the note**, for both neighbourhoods: if all sides are odd,
(1) all-on is reachable ⇔ (3), and (2) every completely symmetric configuration is
reachable ⇔ (3). Here it is only stated, not proved. -/
def TeoremaPrincipale : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ), (∀ i, Odd (n i)) →
    (Reachable (EdgeAdj (n := n)) allOn ↔ Condition3 n) ∧
    ((∀ x : Cell n → ZMod 2, CompletelySymmetric x → Reachable (EdgeAdj (n := n)) x) ↔
      Condition3 n) ∧
    (Reachable (KingAdj (n := n)) allOn ↔ Condition3 n) ∧
    ((∀ x : Cell n → ZMod 2, CompletelySymmetric x → Reachable (KingAdj (n := n)) x) ↔
      Condition3 n)

end SigmaMeno
