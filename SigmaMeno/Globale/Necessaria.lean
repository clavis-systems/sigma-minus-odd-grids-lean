import SigmaMeno.Globale.Griglia

/-!
# Teorema principale, metà "raggiungibile ⇒ condizione 3"

Se "tutte accese" è raggiungibile, la relazione `c = m · Φ(w)` vale modulo `(Q_{n_i}(X_i))`, quindi
anche modulo l'ideale più grande `(X_i^{2^{a_i} - 1})` del blocco `Z` (tutti gli autovalori nulli).
Lì `c` è un'unità per `∏ X_i^{2^{a_i - 1} - 1}`: è il problema locale con soli fattori `Z`, e il
teorema locale dà la condizione. Tutto avviene su `F_2`, senza chiusura algebrica.
-/

namespace SigmaMeno.Globale

open MvPolynomial Finset SigmaMeno.Locale

/-- Per `n` dispari: `n + 1 = 2^(a n) (M + 1)` con `M` pari e `a n ≥ 1`. -/
lemma odd_decomp (n : ℕ) (hn : Odd n) :
    ∃ M, Even M ∧ n + 1 = 2 ^ (SigmaMeno.a n) * (M + 1) ∧ 1 ≤ SigmaMeno.a n := by
  obtain ⟨k, m, hm, h⟩ := Nat.exists_eq_two_pow_mul_odd (n := n + 1) (by omega)
  obtain ⟨r, rfl⟩ := hm
  have ha : SigmaMeno.a n = k := by
    unfold SigmaMeno.a
    rw [h, padicValNat.mul (pow_ne_zero _ two_ne_zero) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (fun h2 => by obtain ⟨c, hc⟩ := h2; omega), add_zero]
  refine ⟨2 * r, even_two_mul r, by rw [ha, h], ?_⟩
  rw [ha]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨t, ht⟩ := hn
    simp at h
    omega
  · exact hk

variable {d : ℕ}

/-- Il blocco con tutti gli autovalori nulli: fattori `Z_{2^(a_i - 1)}`. -/
def fZ (n : Fin d → ℕ) : Fin d → Factor := fun i => Factor.Z (SigmaMeno.a (n i) - 1)

lemma fZ_s (n : Fin d → ℕ) (i : Fin d) (ha : 1 ≤ SigmaMeno.a (n i)) :
    (fZ n i).s = 2 ^ (SigmaMeno.a (n i)) - 1 := by
  simp only [fZ, Factor.s]
  rw [← pow_succ', Nat.sub_add_cancel ha]

lemma fZ_j (n : Fin d → ℕ) (i : Fin d) : (fZ n i).j = 2 ^ (SigmaMeno.a (n i) - 1) - 1 := rfl

variable {F : Type*} [Field F] [CharP F 2]

/-- `(Q_{n_i}(X_i)) ⊆ (X_i^{2^{a_i} - 1})`. -/
lemma Jid_le (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) : Jid F n ≤ Locale.I F (fZ n) := by
  unfold Jid
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨M, hM, hnM, ha⟩ := odd_decomp (n i) (hn i)
  set A := SigmaMeno.a (n i) with hA
  have hn' : n i = 2 ^ A * (M + 1) - 1 := by omega
  have hX := Locale.X_pow_mem (F := F) (fZ n) i
  rw [fZ_s n i ha] at hX
  show qq F i (n i) ∈ Locale.I F (fZ n)
  rw [qq, hn', Q_pow_form, map_mul, map_pow, Polynomial.aeval_X]
  exact Ideal.mul_mem_right _ _ hX

lemma f_ne_zero_odd (n : ℕ) (hn : Odd n) : f F n ≠ 0 := by
  obtain ⟨j, rfl⟩ := hn
  cases j with
  | zero => simp [f]
  | succ k =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, f_odd]
    refine mul_ne_zero (Q_ne_zero _) ?_
    intro h
    have := g_eval_zero (K := F) k
    rw [g, h, Polynomial.eval_zero] at this
    exact zero_ne_one this

/-- `f_n = X^(2^(a-1) - 1) · U` con `U(0) ≠ 0`. -/
lemma f_split (n : ℕ) (hn : Odd n) :
    ∃ U : Polynomial F, f F n = Polynomial.X ^ (2 ^ (SigmaMeno.a n - 1) - 1) * U ∧
      U.coeff 0 ≠ 0 := by
  obtain ⟨U, hU, hndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (f F n) (f_ne_zero_odd n hn) 0
  simp only [map_zero, sub_zero] at hU hndvd
  obtain ⟨M, hM, hnM, ha⟩ := odd_decomp n hn
  have hroot : (Q F n).IsRoot 0 := by
    obtain ⟨t, ht⟩ := hn
    simp [Polynomial.IsRoot, Q_eval_zero, ht, Nat.add_mod]
  have hmult := ((mult_data n (SigmaMeno.a n) M hnM ha hM (0 : F) hroot).1 rfl).2
  rw [hmult] at hU
  exact ⟨U, hU, by rwa [Polynomial.X_dvd_iff] at hndvd⟩

/-- Un polinomio con termine noto non nullo, valutato in `X_i`, è un'unità nell'anello locale. -/
lemma isUnit_aeval (f₀ : Fin d → Factor) (i : Fin d) (U : Polynomial F) (hU : U.coeff 0 ≠ 0) :
    IsUnit (Ideal.Quotient.mk (Locale.I F f₀) (Polynomial.aeval (X i) U)) := by
  rw [← Polynomial.X_mul_divX_add U, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
    map_add, add_comm]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ (Commute.all _ _)
  · refine ⟨(f₀ i).s, ?_⟩
    rw [← map_pow, mul_pow, map_mul, Locale.mk_X_pow f₀ i le_rfl, zero_mul]
  · exact ((isUnit_iff_ne_zero.2 hU).map (algebraMap F (MvPolynomial (Fin d) F))).map _

/-- `c` del blocco `Z` è `cc (fZ n)` per un'unità. -/
lemma cc_grid_split (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) :
    ∃ W : MvPolynomial (Fin d) F,
      ∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) F) (f F (n i)) = Locale.cc F (fZ n) * W ∧
      IsUnit (Ideal.Quotient.mk (Locale.I F (fZ n)) W) := by
  have hex : ∀ i, ∃ U : Polynomial F, f F (n i) =
      Polynomial.X ^ (2 ^ (SigmaMeno.a (n i) - 1) - 1) * U ∧ U.coeff 0 ≠ 0 :=
    fun i => f_split (n i) (hn i)
  choose U hU hU0 using hex
  refine ⟨∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) F) (U i), ?_, ?_⟩
  · rw [Locale.cc, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [hU i, map_mul, map_pow, Polynomial.aeval_X, fZ_j]
  · rw [map_prod]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => isUnit_aeval (fZ n) i (U i) (hU0 i))

/-- La condizione del teorema locale per il blocco `Z` è la condizione 3. -/
lemma cond_fZ_iff (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) :
    Cond (fZ n) ↔ SigmaMeno.Condition3 n := by
  have ha : ∀ i, 1 ≤ SigmaMeno.a (n i) := fun i => (odd_decomp (n i) (hn i)).choose_spec.2.2
  have hfilt : ∀ ℓ, 1 ≤ ℓ → univ.filter (fun i => fZ n i = Factor.Z ℓ) =
      univ.filter (fun i => SigmaMeno.a (n i) = ℓ + 1) := by
    intro ℓ hℓ
    ext i
    simp only [mem_filter, mem_univ, true_and, fZ, Factor.Z.injEq]
    have := ha i
    omega
  constructor
  · rintro ⟨ℓ, hℓ, hg⟩
    rcases hg with ⟨i, hi⟩ | ho
    · simp [fZ] at hi
    · rw [hfilt ℓ hℓ] at ho
      exact ⟨ℓ + 1, by omega, ho⟩
  · rintro ⟨k, hk, ho⟩
    refine ⟨k - 1, by omega, Or.inr ?_⟩
    rw [hfilt (k - 1) (by omega), Nat.sub_add_cancel (by omega : 1 ≤ k)]
    exact ho

/-- Da `c ≡ m · Φ(w)` modulo `(Q_{n_i}(X_i))` alla raggiungibilità del blocco `Z`. -/
lemma reach_Z_of_grid (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (m : MvPolynomial (Fin d) F)
    (y : MvPolynomial (Fin d) F)
    (h : Ideal.Quotient.mk (Jid F n) (∏ i, Polynomial.aeval (X i) (f F (n i))) =
      Ideal.Quotient.mk (Jid F n) m * Ideal.Quotient.mk (Jid F n) y) :
    Locale.Reach (fZ n) m := by
  have hmem : (∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) F) (f F (n i))) - m * y ∈
      Locale.I F (fZ n) :=
    Jid_le n hn (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, h, sub_self])
  obtain ⟨W, hW, hWu⟩ := cc_grid_split (F := F) n hn
  rw [hW, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, sub_eq_zero] at hmem
  obtain ⟨v, hv⟩ := hWu
  rw [Locale.reach_iff_mk]
  refine ⟨Ideal.Quotient.mk (Locale.I F (fZ n)) y * ↑v⁻¹, ?_⟩
  calc Ideal.Quotient.mk (Locale.I F (fZ n)) (Locale.cc F (fZ n))
      = Ideal.Quotient.mk (Locale.I F (fZ n)) (Locale.cc F (fZ n)) * (↑v * ↑v⁻¹) := by
        rw [Units.mul_inv, mul_one]
    _ = (Ideal.Quotient.mk (Locale.I F (fZ n)) (Locale.cc F (fZ n)) * ↑v) * ↑v⁻¹ := by ring
    _ = _ := by rw [hv, hmem]; ring

/-- **Teorema principale, (1) ⇒ (3), vicinato edge.** -/
theorem necessaria_edge (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) :
    SigmaMeno.Reachable (SigmaMeno.EdgeAdj (n := n)) SigmaMeno.allOn → SigmaMeno.Condition3 n := by
  rintro ⟨w, hw⟩
  have key := mk_Phi_edge (F := ZMod 2) (n := n) w
  have hp : pressF SigmaMeno.EdgeAdj w = fun _ => (1 : ZMod 2) := hw
  rw [hp, Phi_allOn] at key
  have hr := reach_Z_of_grid (F := ZMod 2) n hn _ _ key
  exact (cond_fZ_iff n hn).1 ((Locale.local_theorem_edge (fZ n)).1 hr)

/-- **Teorema principale, (1) ⇒ (3), vicinato king.** -/
theorem necessaria_king (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) :
    SigmaMeno.Reachable (SigmaMeno.KingAdj (n := n)) SigmaMeno.allOn → SigmaMeno.Condition3 n := by
  rintro ⟨w, hw⟩
  have key := mk_Phi_king (F := ZMod 2) (n := n) w
  have hp : pressF SigmaMeno.KingAdj w = fun _ => (1 : ZMod 2) := hw
  rw [hp, Phi_allOn] at key
  have hr := reach_Z_of_grid (F := ZMod 2) n hn _ _ key
  exact (cond_fZ_iff n hn).1 ((Locale.local_theorem_king (fZ n)).1 hr)

end SigmaMeno.Globale
