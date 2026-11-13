import SigmaMeno.Globale.Finale

/-!
# Una coordinata: le fibre della riflessione

Per `N` dispari e `t ∈ {0, …, N-1}`, la somma `Q_t + Q_{N-1-t}` (o `Q_k` se `t = k` è il centro)
è congrua a `g · f_N` modulo `Q_N`, per un polinomio `g`. Ingredienti:
* `Q_{M+j+1} Q_{j+1} = Q_M + Q_{M+j+2} Q_j` (dalla formula di addizione e da Cassini);
* `X f_N = 1 + Q_{N-1} + Q_N`;
* al centro: `f_{2k+1} = Q_k (Q_k + Q_{k-1})` e `Q_k + Q_{k-1}` è invertibile modulo `Q_N`.
-/

namespace SigmaMeno.Globale

open Polynomial

variable {F : Type*} [Field F] [CharP F 2]

/-- Riflessione: `Q_{M+j+1} Q_{j+1} = Q_M + Q_{M+j+2} Q_j`. -/
lemma refl_Q (M j : ℕ) : Q F (M + j + 1) * Q F (j + 1) = Q F M + Q F (M + j + 2) * Q F j := by
  have h2 := two_eq_zero_poly (K := F)
  have hc := cassini (K := F) j
  cases M with
  | zero =>
    have e : Q F (0 + j + 2) = X * Q F (j + 1) + Q F j := by
      rw [show 0 + j + 2 = j + 2 by ring]; exact Q_ss j
    rw [show 0 + j + 1 = j + 1 by ring, e, Q_zero]
    linear_combination (-1 : F[X]) * hc + (Q F j ^ 2 + X * Q F (j + 1) * Q F j
      + (-1 - X * Q F (j + 1) * Q F j + Q F (j + 1) ^ 2 - Q F j ^ 2)) * h2
  | succ M =>
    have a1 : Q F (M + j + 2) = Q F (M + 1) * Q F (j + 1) + Q F M * Q F j := Q_add M j
    have a2 : Q F (M + 1 + j + 2) = Q F (M + 2) * Q F (j + 1) + Q F (M + 1) * Q F j := by
      rw [show M + 1 + j + 2 = (M + 1) + j + 2 by ring, Q_add]
    have hs : Q F (M + 2) = X * Q F (M + 1) + Q F M := Q_ss M
    rw [show M + 1 + j + 1 = M + j + 2 by ring, a1, a2, hs]
    linear_combination (-(Q F (M + 1))) * hc
      + (Q F (M + 1) * Q F (j + 1) ^ 2 + X * Q F (M + 1) * Q F (j + 1) * Q F j
        + Q F (M + 1) * Q F j ^ 2 + Q F M * Q F j * Q F (j + 1)
        + (-(Q F (M + 1)) - Q F (M + 1) * Q F (j + 1) * Q F j * X
          - Q F (M + 1) * Q F j ^ 2 - Q F (j + 1) * Q F M * Q F j)) * h2

/-- `X f_{n+1} = 1 + Q_n + Q_{n+1}`. -/
lemma X_mul_f (n : ℕ) : X * f F (n + 1) = 1 + Q F n + Q F (n + 1) := by
  have h2 := two_eq_zero_poly (K := F)
  induction n with
  | zero => simp [f]; linear_combination (1 : F[X]) * h2
  | succ n ih =>
    rw [f_succ, mul_add, ih, show n + 1 + 1 = n + 2 from rfl, Q_ss]
    linear_combination (0 : F[X]) * h2

/-- Fibra non centrale: `Q_a + Q_b ≡ X Q_a f_N` se `a + b + 1 = N`. -/
lemma fibra_pair (N a b : ℕ) (hab : a + b + 1 = N) :
    Q F N ∣ (Q F a + Q F b) - X * Q F a * f F N := by
  have h2 := two_eq_zero_poly (K := F)
  have hN : N = (N - 1) + 1 := by omega
  have hxf := X_mul_f (F := F) (N - 1)
  rw [← hN] at hxf
  cases a with
  | zero =>
    refine ⟨-1, ?_⟩
    have hb : b = N - 1 := by omega
    rw [hb, Q_zero]
    linear_combination (-1 : F[X]) * hxf
  | succ j =>
    have hr := refl_Q (F := F) b j
    rw [show b + j + 1 = N - 1 by omega, show b + j + 2 = N by omega] at hr
    refine ⟨-(Q F j + Q F (j + 1)), ?_⟩
    linear_combination (-(Q F (j + 1))) * hxf + hr
      + (Q F b + Q F N * Q F j - Q F (j + 1) * Q F (N - 1)) * h2

/-- Fibra centrale: `Q_k ≡ u f_{2k+1}` per un `u`. -/
lemma fibra_centro (k : ℕ) : ∃ u : F[X], Q F (2 * k + 1) ∣ Q F k - u * f F (2 * k + 1) := by
  cases k with
  | zero => exact ⟨1, by simp [f]⟩
  | succ j =>
    have hf : f F (2 * (j + 1) + 1) = Q F (j + 1) * (Q F (j + 1) + Q F j) := by
      rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]; exact f_odd j
    have hQ : Q F (2 * (j + 1) + 1) = X * Q F (j + 1) ^ 2 := Q_odd (j + 1)
    have hcB : IsCoprime (Q F (j + 1) + Q F j) (Q F (j + 1)) := by
      have := (coprime_succ (K := F) j).symm
      have h := this.add_mul_left_left 1
      rw [mul_one, add_comm] at h
      exact h
    have hX : IsCoprime (Q F (j + 1) + Q F j) X := by
      rw [isCoprime_comm, Irreducible.coprime_iff_not_dvd irreducible_X, X_dvd_iff,
        coeff_zero_eq_eval_zero]
      have := g_eval_zero (K := F) j
      rw [g] at this
      rw [this]
      exact one_ne_zero
    have hcop : IsCoprime (Q F (j + 1) + Q F j) (Q F (2 * (j + 1) + 1)) := by
      rw [hQ]; exact hX.mul_right hcB.pow_right
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨u, Q F (j + 1) * v, ?_⟩
    rw [hf]
    linear_combination (-(Q F (j + 1))) * huv

/-- **Ogni fibra** `{t, N-1-t}` di un cammino di lunghezza dispari. -/
lemma fibra (N : ℕ) (hN : Odd N) (t : Fin N) :
    ∃ g : F[X], Q F N ∣ (∑ s ∈ ({t, Fin.rev t} : Finset (Fin N)), Q F (s : ℕ)) - g * f F N := by
  have hrev : ((Fin.rev t : Fin N) : ℕ) = N - ((t : ℕ) + 1) := Fin.val_rev t
  have htlt := t.isLt
  by_cases ht : t = Fin.rev t
  · have hset : ({t, Fin.rev t} : Finset (Fin N)) = {t} := by rw [← ht]; simp
    rw [hset, Finset.sum_singleton]
    obtain ⟨k, hk⟩ := hN
    have htk : (t : ℕ) = k := by have := congrArg Fin.val ht; omega
    obtain ⟨u, hu⟩ := fibra_centro (F := F) k
    refine ⟨u, ?_⟩
    rw [htk]
    rw [hk]
    exact hu
  · rw [Finset.sum_pair ht, hrev]
    exact ⟨_, fibra_pair N t (N - ((t : ℕ) + 1)) (by omega)⟩

end SigmaMeno.Globale
