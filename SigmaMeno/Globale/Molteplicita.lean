import SigmaMeno.Globale.Polinomi

/-!
# Parte I: le molteplicità delle radici (Lemmi 1 e 2 della nota)

Per `n + 1 = 2^a (M + 1)` con `M` pari e `a ≥ 1`:
* `Q_n = X^(2^a - 1) · Q_M^(2^a)` e `Q_M = g^2` con `g` separabile e `g(0) = 1`;
* radice `0`: molteplicità `2^a - 1` in `Q_n` e `2^(a-1) - 1` in `f_n` (fattore `Z_q`, `q = 2^(a-1)`);
* radice `x ≠ 0`: molteplicità `2^(a+1)` in `Q_n` e `2^a` in `f_n` (fattore `N_p`, `p = 2^a`).
-/

namespace SigmaMeno.Globale

open Polynomial

variable {K : Type*} [Field K] [CharP K 2]

lemma rootMult_pow (p : K[X]) (hp : p ≠ 0) (x : K) (e : ℕ) :
    rootMultiplicity x (p ^ e) = e * rootMultiplicity x p := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ih]; ring

open Classical in
lemma rootMult_X_pow (x : K) (e : ℕ) :
    rootMultiplicity x ((X : K[X]) ^ e) = if x = 0 then e else 0 := by
  split_ifs with hx
  · subst hx
    have : (X : K[X]) = X - C 0 := by simp
    rw [this]; exact rootMultiplicity_X_sub_C_pow 0 e
  · apply rootMultiplicity_eq_zero
    simp [hx]

lemma Q_pow_form (a M : ℕ) : Q K (2 ^ a * (M + 1) - 1) = X ^ (2 ^ a - 1) * Q K M ^ (2 ^ a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hpos : 0 < 2 ^ a := by positivity
    set t := 2 ^ a * (M + 1) with ht
    have h1 : 2 ^ (a + 1) * (M + 1) = 2 * t := by rw [ht, pow_succ]; ring
    have ht1 : 1 ≤ t := by rw [ht]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [h1, show 2 * t - 1 = 2 * (t - 1) + 1 by omega, Q_odd, ih, mul_pow, ← pow_mul,
      ← pow_mul, ← mul_assoc, ← pow_succ']
    rw [show (2 ^ a - 1) * 2 + 1 = 2 ^ (a + 1) - 1 by rw [pow_succ]; omega,
      show 2 ^ a * 2 = 2 ^ (a + 1) by rw [pow_succ]]

lemma deriv_Q_even (r : ℕ) : derivative (Q K (2 * r)) = 0 := by
  have h2 := two_eq_zero_poly (K := K)
  cases r with
  | zero => simp
  | succ r =>
    rw [show 2 * (r + 1) = 2 * r + 2 by ring, Q_even, pow_two, derivative_mul]
    linear_combination (derivative (Q K (r + 1) + Q K r) * (Q K (r + 1) + Q K r)) * h2

lemma deriv_Q_odd (r : ℕ) : derivative (Q K (2 * r + 1)) = Q K r ^ 2 := by
  have h2 := two_eq_zero_poly (K := K)
  rw [Q_odd, derivative_mul, derivative_X, pow_two, derivative_mul]
  linear_combination (X * Q K r * derivative (Q K r)) * h2

/-- `g_k = Q_{k+1} + Q_k`, la "radice quadrata" di `Q_{2k+2}`. -/
noncomputable def g (K : Type*) [CommRing K] (k : ℕ) : K[X] := Q K (k + 1) + Q K k

lemma g_eval_zero (k : ℕ) : (g K k).eval 0 = 1 := by
  rw [g, eval_add, Q_eval_zero, Q_eval_zero]
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · subst hr; simp [show (r + r + 1) % 2 = 1 by omega, show (r + r) % 2 = 0 by omega]
  · subst hr; simp [show (2 * r + 1 + 1) % 2 = 0 by omega, show (2 * r + 1) % 2 = 1 by omega]

lemma coprime_aux1 (r : ℕ) : Nat.Coprime (4 * r + 3) (r + 1) := by
  have h1 := Nat.gcd_dvd_left (4 * r + 3) (r + 1)
  have h2 := Nat.gcd_dvd_right (4 * r + 3) (r + 1)
  have h3 : Nat.gcd (4 * r + 3) (r + 1) ∣ 4 * r + 4 := by
    rw [show 4 * r + 4 = 4 * (r + 1) by ring]; exact Dvd.dvd.mul_left h2 4
  have h4 := Nat.dvd_sub h3 h1
  rw [show 4 * r + 4 - (4 * r + 3) = 1 by omega] at h4
  exact Nat.dvd_one.1 h4

lemma coprime_aux2 (r : ℕ) : Nat.Coprime (4 * r + 5) (r + 1) := by
  have h1 := Nat.gcd_dvd_left (4 * r + 5) (r + 1)
  have h2 := Nat.gcd_dvd_right (4 * r + 5) (r + 1)
  have h3 : Nat.gcd (4 * r + 5) (r + 1) ∣ 4 * r + 4 := by
    rw [show 4 * r + 4 = 4 * (r + 1) by ring]; exact Dvd.dvd.mul_left h2 4
  have h4 := Nat.dvd_sub h1 h3
  rw [show 4 * r + 5 - (4 * r + 4) = 1 by omega] at h4
  exact Nat.dvd_one.1 h4

/-- `g_k` è separabile (quindi senza radici multiple). -/
lemma g_separable (k : ℕ) : (g K k).Separable := by
  show IsCoprime (g K k) (derivative (g K k))
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hk : k = 2 * r := by omega
    have hd : derivative (g K k) = Q K r ^ 2 := by
      rw [g, derivative_add, hk, deriv_Q_odd, deriv_Q_even, add_zero]
    have hcop : Nat.Coprime (2 * k + 2 + 1) (r + 1) := by
      rw [hk, show 2 * (2 * r) + 2 + 1 = 4 * r + 3 by ring]; exact coprime_aux1 r
    have hc : IsCoprime (Q K (2 * k + 2)) (Q K r) := coprime_of_coprime (2 * k + 2) r hcop
    rw [Q_even, pow_two] at hc
    rw [hd]
    exact (IsCoprime.of_mul_left_left hc).pow_right
  · have hd : derivative (g K k) = Q K r ^ 2 := by
      rw [g, derivative_add, hr, show 2 * r + 1 + 1 = 2 * (r + 1) by ring, deriv_Q_even,
        deriv_Q_odd, zero_add]
    have hcop : Nat.Coprime (2 * k + 2 + 1) (r + 1) := by
      rw [hr, show 2 * (2 * r + 1) + 2 + 1 = 4 * r + 5 by ring]; exact coprime_aux2 r
    have hc : IsCoprime (Q K (2 * k + 2)) (Q K r) := coprime_of_coprime (2 * k + 2) r hcop
    rw [Q_even, pow_two] at hc
    rw [hd]
    exact (IsCoprime.of_mul_left_left hc).pow_right

/-- **Lemma 1, radice 0.** -/
lemma mult_zero_Q (a M : ℕ) (hM : Even M) :
    rootMultiplicity 0 (Q K (2 ^ a * (M + 1) - 1)) = 2 ^ a - 1 := by
  rw [Q_pow_form, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero)
      (pow_ne_zero _ (Q_ne_zero M))), rootMult_X_pow, if_pos rfl, rootMult_pow _ (Q_ne_zero M),
    rootMultiplicity_eq_zero, mul_zero, add_zero]
  simp [IsRoot, Q_eval_zero, Nat.even_iff.1 hM]

/-- **Lemma 1, radici non nulle.** -/
lemma mult_ne_zero_Q (a M : ℕ) (hM : Even M) (x : K) (hx : x ≠ 0)
    (hroot : (Q K (2 ^ a * (M + 1) - 1)).IsRoot x) :
    rootMultiplicity x (Q K (2 ^ a * (M + 1) - 1)) = 2 ^ (a + 1) := by
  obtain ⟨r, hr⟩ := hM
  rw [Q_pow_form] at hroot ⊢
  cases r with
  | zero =>
    exfalso
    simp only [show M = 0 by omega, Q_zero, one_pow, mul_one, IsRoot, eval_pow, eval_X] at hroot
    exact hx (pow_eq_zero_iff'.1 hroot).1
  | succ k =>
    have hM2 : M = 2 * k + 2 := by omega
    rw [hM2, Q_even] at hroot ⊢
    have hgk : (Q K (k + 1) + Q K k) = g K k := rfl
    rw [hgk] at hroot ⊢
    have hg0 : g K k ≠ 0 := by
      intro h; have := g_eval_zero (K := K) k; rw [h, eval_zero] at this; exact zero_ne_one this
    have hgroot : (g K k).IsRoot x := by
      simp only [IsRoot, eval_mul, eval_pow, eval_X, mul_eq_zero, pow_eq_zero_iff', ne_eq] at hroot
      rcases hroot with ⟨h, _⟩ | ⟨⟨h, _⟩, _⟩
      · exact absurd h hx
      · exact h
    have h1 : rootMultiplicity x (g K k) = 1 := by
      have := rootMultiplicity_le_one_of_separable (g_separable (K := K) k) x
      have := (rootMultiplicity_pos hg0).2 hgroot
      omega
    rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero)
        (pow_ne_zero _ (pow_ne_zero _ hg0))), rootMult_X_pow, if_neg hx,
      rootMult_pow _ (pow_ne_zero _ hg0), rootMult_pow _ hg0, h1, pow_succ]
    ring

lemma n_odd_form (n a M : ℕ) (hn : n + 1 = 2 ^ a * (M + 1)) (ha : 1 ≤ a) :
    ∃ j, n = 2 * j + 1 ∧ 2 * j + 2 = 2 ^ a * (M + 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  refine ⟨2 ^ b * (M + 1) - 1, ?_, ?_⟩
  · have : 1 ≤ 2 ^ b * (M + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [pow_succ] at hn
    have e : 2 ^ b * 2 * (M + 1) = 2 * (2 ^ b * (M + 1)) := by ring
    omega
  · have : 1 ≤ 2 ^ b * (M + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [pow_succ]
    have e : 2 ^ b * 2 * (M + 1) = 2 * (2 ^ b * (M + 1)) := by ring
    omega

/-- **Lemmi 1 e 2.** I dati di ogni radice `x` di `Q_n`: le molteplicità in `Q_n` e in `f_n`. -/
theorem mult_data (n a M : ℕ) (hn : n + 1 = 2 ^ a * (M + 1)) (ha : 1 ≤ a) (hM : Even M)
    (x : K) (hroot : (Q K n).IsRoot x) :
    (x = 0 → rootMultiplicity x (Q K n) = 2 ^ a - 1 ∧
      rootMultiplicity x (f K n) = 2 ^ (a - 1) - 1) ∧
    (x ≠ 0 → rootMultiplicity x (Q K n) = 2 ^ (a + 1) ∧ rootMultiplicity x (f K n) = 2 ^ a) := by
  have hn' : n = 2 ^ a * (M + 1) - 1 := by omega
  have hQ0 := mult_zero_Q (K := K) a M hM
  rw [← hn'] at hQ0
  have hpa : 2 ^ a = 2 * 2 ^ (a - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel ha]
  obtain ⟨j, hj, -⟩ := n_odd_form n a M hn ha
  cases j with
  | zero =>
    -- n = 1: `Q_1 = X`, `f_1 = 1`
    have hn1 : n = 1 := by omega
    subst hn1
    have h2a : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have hle : 2 ^ a * 1 ≤ 2 ^ a * (M + 1) := Nat.mul_le_mul_left _ (by omega)
    have ha1 : 2 ^ a = 2 := by simp at h2a; omega
    refine ⟨fun hx0 => ⟨hx0 ▸ hQ0, ?_⟩, fun hx => ?_⟩
    · have : f K 1 = 1 := by simp [f]
      rw [this, rootMultiplicity_eq_zero (by simp)]
      omega
    · exfalso; simp [IsRoot] at hroot; exact hx hroot
  | succ k =>
    have hQn : Q K n = X * Q K (k + 1) ^ 2 := by rw [hj]; exact Q_odd (k + 1)
    have hfn : f K n = Q K (k + 1) * g K k := by
      rw [hj, show 2 * (k + 1) + 1 = 2 * k + 3 by ring, f_odd]; rfl
    have hQk : Q K (k + 1) ≠ 0 := Q_ne_zero _
    have hg0 : g K k ≠ 0 := by
      intro h; have := g_eval_zero (K := K) k; rw [h, eval_zero] at this; exact zero_ne_one this
    have hmulQ : ∀ y : K, rootMultiplicity y (Q K n) =
        rootMultiplicity y ((X : K[X]) ^ 1) + 2 * rootMultiplicity y (Q K (k + 1)) := by
      intro y
      rw [hQn, rootMultiplicity_mul (mul_ne_zero X_ne_zero (pow_ne_zero _ hQk)),
        rootMult_pow _ hQk, pow_one]
    have hmulf : ∀ y : K, rootMultiplicity y (f K n) =
        rootMultiplicity y (Q K (k + 1)) + rootMultiplicity y (g K k) := by
      intro y; rw [hfn, rootMultiplicity_mul (mul_ne_zero hQk hg0)]
    refine ⟨fun hx0 => ?_, fun hx => ?_⟩
    · subst hx0
      refine ⟨hQ0, ?_⟩
      have h1 := hmulQ 0
      rw [hQ0, rootMult_X_pow, if_pos rfl] at h1
      rw [hmulf, rootMultiplicity_eq_zero (p := g K k) (by simp [IsRoot, g_eval_zero])]
      omega
    · have hQx := mult_ne_zero_Q (K := K) a M hM x hx (by rw [← hn']; exact hroot)
      rw [← hn'] at hQx
      refine ⟨hQx, ?_⟩
      have h1 := hmulQ x
      rw [hQx, rootMult_X_pow, if_neg hx] at h1
      have hQkx : rootMultiplicity x (Q K (k + 1)) = 2 ^ a := by
        rw [pow_succ] at h1; omega
      have hroot' : (Q K (k + 1)).IsRoot x := by
        rw [← rootMultiplicity_pos hQk, hQkx]; positivity
      have hgx : ¬ (g K k).IsRoot x := by
        intro hg
        have hc := congrArg (eval x) (cassini (K := K) k)
        simp only [IsRoot] at hroot' hg
        rw [g, eval_add, hroot', zero_add] at hg
        simp [eval_add, eval_mul, eval_pow, eval_X, hroot', hg] at hc
      rw [hmulf, hQkx, rootMultiplicity_eq_zero hgx, add_zero]

end SigmaMeno.Globale
