import Mathlib

/-!
# Parte I: i polinomi del cammino

`Q 0 = 1`, `Q 1 = X`, `Q (n+2) = X Q (n+1) + Q n`; `f n = Q 0 + … + Q (n-1)` (il vettore "tutte
accese" del cammino `P_n`). In caratteristica 2 valgono:
* `Q (2k+1) = X Q_k^2`, `Q (2k+2) = (Q_{k+1} + Q_k)^2`;
* `f (2k+3) = Q_{k+1} (Q_{k+1} + Q_k)` (identità nuova rispetto alla nota, controllata al
  calcolatore per `k ≤ 148` e qui dimostrata);
* `Q_a` e `Q_b` sono coprimi se `a+1` e `b+1` lo sono.
Da qui le molteplicità delle radici (Lemmi 1 e 2 della nota), senza radici dell'unità.
-/

namespace SigmaMeno.Globale

open Polynomial

section Anello

variable (K : Type*) [CommRing K]

/-- I polinomi `Q_n` della nota. -/
noncomputable def Q : ℕ → K[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * Q (n + 1) + Q n

/-- `f_n = Q_0 + … + Q_{n-1}`. -/
noncomputable def f (n : ℕ) : K[X] := ∑ k ∈ Finset.range n, Q K k

variable {K}

@[simp] lemma Q_zero : Q K 0 = 1 := rfl
@[simp] lemma Q_one : Q K 1 = X := rfl
lemma Q_ss (n : ℕ) : Q K (n + 2) = X * Q K (n + 1) + Q K n := rfl

lemma f_succ (n : ℕ) : f K (n + 1) = f K n + Q K n := Finset.sum_range_succ _ _

/-- Formula di addizione: `Q_{a+b+2} = Q_{a+1} Q_{b+1} + Q_a Q_b`. -/
lemma Q_add (a b : ℕ) : Q K (a + b + 2) = Q K (a + 1) * Q K (b + 1) + Q K a * Q K b := by
  induction b using Nat.twoStepInduction with
  | zero => rw [Nat.add_zero, Q_ss, Q_one, Q_zero]; ring
  | one =>
    have e1 : Q K (a + 1 + 2) = X * Q K (a + 2) + Q K (a + 1) := Q_ss (a + 1)
    have e2 : Q K (1 + 1) = X * X + 1 := by
      show Q K (0 + 2) = _; rw [Q_ss]; simp
    rw [e1, e2, Q_ss a, Q_one]; ring
  | more b ih1 ih2 =>
    have e1 : Q K (a + (b + 2) + 2) = X * Q K (a + (b + 1) + 2) + Q K (a + b + 2) := by
      rw [show a + (b + 2) + 2 = (a + b + 2) + 2 by ring, Q_ss,
        show a + b + 2 + 1 = a + (b + 1) + 2 by ring]
    have e2 : Q K (b + 2 + 1) = X * Q K (b + 2) + Q K (b + 1) := by
      rw [show b + 2 + 1 = (b + 1) + 2 by ring, Q_ss]
    have e3 : Q K (b + 1 + 1) = Q K (b + 2) := rfl
    rw [e1, ih2, ih1, e2, e3, Q_ss b]
    ring

lemma Q_eval_zero (n : ℕ) : (Q K n).eval 0 = if n % 2 = 0 then 1 else 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 _ =>
    rw [Q_ss, eval_add, eval_mul, eval_X, zero_mul, zero_add, ih1]
    simp [Nat.add_mod]

lemma Q_monic [Nontrivial K] (n : ℕ) : (Q K n).Monic ∧ (Q K n).natDegree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    have hm : (X * Q K (n + 1)).Monic := monic_X.mul ih2.1
    have hd : (X * Q K (n + 1)).natDegree = n + 2 := by
      rw [monic_X.natDegree_mul ih2.1, natDegree_X, ih2.2]; ring
    have hlt : (Q K n).degree < (X * Q K (n + 1)).degree := by
      rw [degree_eq_natDegree ih1.1.ne_zero, degree_eq_natDegree hm.ne_zero, hd, ih1.2]
      exact_mod_cast (by omega : n < n + 2)
    refine ⟨?_, ?_⟩
    · rw [Q_ss]; exact hm.add_of_left hlt
    · rw [Q_ss, natDegree_add_eq_left_of_degree_lt hlt, hd]

lemma Q_ne_zero [Nontrivial K] (n : ℕ) : Q K n ≠ 0 := (Q_monic n).1.ne_zero

end Anello

section CarDue

variable {K : Type*} [Field K] [CharP K 2]

lemma two_eq_zero_poly : (2 : K[X]) = 0 := by
  have h : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  rw [← map_ofNat C 2, h, map_zero]

/-- Identità di Cassini in caratteristica 2. -/
lemma cassini (k : ℕ) : Q K (k + 1) ^ 2 + X * Q K (k + 1) * Q K k + Q K k ^ 2 = 1 := by
  have h2 := two_eq_zero_poly (K := K)
  induction k with
  | zero =>
    show Q K 1 ^ 2 + X * Q K 1 * Q K 0 + Q K 0 ^ 2 = 1
    simp only [Q_one, Q_zero]; linear_combination (X ^ 2 : K[X]) * h2
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 from rfl, Q_ss]
    linear_combination ih + (X ^ 2 * Q K (k + 1) ^ 2 + X * Q K (k + 1) * Q K k) * h2

lemma coprime_succ (k : ℕ) : IsCoprime (Q K (k + 1)) (Q K k) :=
  ⟨Q K (k + 1) + X * Q K k, Q K k, by linear_combination cassini (K := K) k⟩

lemma Q_odd (k : ℕ) : Q K (2 * k + 1) = X * Q K k ^ 2 := by
  have h2 := two_eq_zero_poly (K := K)
  cases k with
  | zero => simp
  | succ j =>
    rw [show 2 * (j + 1) + 1 = j + (j + 1) + 2 by ring, Q_add,
      show j + 1 + 1 = j + 2 from rfl, Q_ss j]
    linear_combination (Q K (j + 1) * Q K j) * h2

lemma Q_even (k : ℕ) : Q K (2 * k + 2) = (Q K (k + 1) + Q K k) ^ 2 := by
  have h2 := two_eq_zero_poly (K := K)
  rw [show 2 * k + 2 = k + k + 2 by ring, Q_add]
  linear_combination (-(Q K (k + 1) * Q K k)) * h2

/-- `f_{2k+3} = Q_{k+1} (Q_{k+1} + Q_k)`. -/
lemma f_odd (k : ℕ) : f K (2 * k + 3) = Q K (k + 1) * (Q K (k + 1) + Q K k) := by
  have h2 := two_eq_zero_poly (K := K)
  induction k with
  | zero =>
    have : f K 3 = Q K 0 + Q K 1 + Q K 2 := by
      simp only [f, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [show 2 * 0 + 3 = 3 from rfl, this, show (2 : ℕ) = 0 + 2 from rfl, Q_ss]
    simp only [Q_one, Q_zero, zero_add]
    linear_combination (1 : K[X]) * h2
  | succ k ih =>
    have hO : Q K (2 * k + 3) = X * Q K (k + 1) ^ 2 := by
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 by ring, Q_odd]
    have hE : Q K (2 * k + 4) = (Q K (k + 2) + Q K (k + 1)) ^ 2 := by
      rw [show 2 * k + 4 = 2 * (k + 1) + 2 by ring, Q_even]
    have hss : Q K (k + 2) = X * Q K (k + 1) + Q K k := Q_ss k
    rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 1 + 1 by ring, f_succ, f_succ,
      show 2 * k + 3 + 1 = 2 * k + 4 by ring, show k + 1 + 1 = k + 2 from rfl]
    linear_combination ih + hO + hE + Q K (k + 1) * hss
      + (Q K (k + 1) ^ 2 + Q K (k + 1) * Q K k + X * Q K (k + 1) ^ 2) * h2

/-- `Q_a` e `Q_b` sono coprimi se `a + 1` e `b + 1` sono coprimi. -/
lemma coprime_of_coprime (a b : ℕ) (h : Nat.Coprime (a + 1) (b + 1)) :
    IsCoprime (Q K a) (Q K b) := by
  induction hs : a + b using Nat.strong_induction_on generalizing a b with
  | _ s ih =>
    wlog hle : b ≤ a generalizing a b with H
    · exact (H b a (Nat.Coprime.symm h) (by omega) (by omega)).symm
    rcases Nat.eq_or_lt_of_le hle with hab | hab
    · subst hab
      have : b + 1 = 1 := by simpa using h
      have ha : b = 0 := by omega
      subst ha; exact isCoprime_one_left
    · cases b with
      | zero => exact isCoprime_one_right
      | succ b' =>
        obtain ⟨c, rfl⟩ : ∃ c, a = c + (b' + 1) + 1 := ⟨a - b' - 2, by omega⟩
        have hc : Nat.Coprime (c + 1) (b' + 1 + 1) := by
          have : c + (b' + 1) + 1 + 1 = (c + 1) + (b' + 1 + 1) := by ring
          rw [this] at h
          exact Nat.coprime_add_self_left.1 h
        have ih' : IsCoprime (Q K c) (Q K (b' + 1)) :=
          ih (c + (b' + 1)) (by omega) c (b' + 1) hc rfl
        have hcons : IsCoprime (Q K b') (Q K (b' + 1)) := (coprime_succ b').symm
        have hprod : IsCoprime (Q K c * Q K b') (Q K (b' + 1)) := ih'.mul_left hcons
        have e : Q K (c + (b' + 1) + 1) = Q K c * Q K b' + Q K (b' + 1) * Q K (c + 1) := by
          rw [show c + (b' + 1) + 1 = c + b' + 2 by ring, Q_add]; ring
        rw [e]
        exact hprod.add_mul_left_left _

end CarDue

end SigmaMeno.Globale
