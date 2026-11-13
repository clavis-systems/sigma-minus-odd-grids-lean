import SigmaMeno.Globale.Inversa

/-!
# Blocchi e incollamento su un campo algebricamente chiuso

Su `K` algebricamente chiuso di caratteristica 2, `Q_n = ∏_r (X - r)^{m_r}`. Con gli idempotenti di
Bezout `e_r` (`∑ e_r = 1`, `Q_n ∣ e_r (X - r)^{m_r}`) e i loro prodotti `E` sulle `d` variabili, la
relazione `c ≡ m · Y` modulo `(Q_{n_i}(X_i))` si ottiene incollando le relazioni dei blocchi.
Ogni blocco, dopo lo spostamento `X_i ↦ α_i X_i + r_i`, è un problema locale: o `m` è invertibile,
o si applica il teorema locale (un fattore `N` rende vera la condizione; il blocco tutto `Z` è la
condizione 3).
-/

namespace SigmaMeno.Globale

open MvPolynomial Finset SigmaMeno.Locale

variable {K : Type*} [Field K] [IsAlgClosed K] [CharP K 2] [DecidableEq K]

/-! ### Una variabile -/

/-- Le radici distinte di `Q_N`. -/
noncomputable def Lam (K : Type*) [Field K] [DecidableEq K] (N : ℕ) : Finset K :=
  (Q K N).roots.toFinset

/-- Il fattore `(X - r)^{m_r}`. -/
noncomputable def sP (K : Type*) [Field K] (N : ℕ) (r : K) : Polynomial K :=
  (Polynomial.X - Polynomial.C r) ^ Polynomial.rootMultiplicity r (Q K N)

lemma Q_eq_prod (N : ℕ) : Q K N = ∏ r ∈ Lam K N, sP K N r := by
  have hm := (Q_monic (K := K) N).1
  have hc : (Q K N).roots.card = (Q K N).natDegree := IsAlgClosed.card_roots_eq_natDegree
  conv_lhs => rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc]
  rw [Finset.prod_multiset_map_count]
  simp only [Lam, sP, Polynomial.count_roots]

lemma mem_Lam {N : ℕ} {r : K} : r ∈ Lam K N ↔ (Q K N).IsRoot r := by
  rw [Lam, Multiset.mem_toFinset, Polynomial.mem_roots (Q_ne_zero N)]

lemma sP_coprime (N : ℕ) : Pairwise (Function.onFun IsCoprime fun r : Lam K N => sP K N (r : K)) := by
  intro r r' hrr'
  simp only [Function.onFun, sP]
  apply IsCoprime.pow
  apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
  exact (sub_ne_zero.2 fun h => hrr' (Subtype.ext h)).isUnit

/-- Gli idempotenti di una variabile. -/
lemma idem_exists (N : ℕ) (hN : Odd N) : ∃ e : K → Polynomial K,
    (∑ r ∈ Lam K N, e r = 1) ∧ ∀ r ∈ Lam K N, Q K N ∣ e r * sP K N r := by
  have hne : (Lam K N).Nonempty := ⟨0, by
    rw [mem_Lam]
    obtain ⟨t, ht⟩ := hN
    simp [Polynomial.IsRoot, Q_eval_zero, ht, Nat.add_mod]⟩
  obtain ⟨μ, hμ⟩ := (exists_sum_eq_one_iff_pairwise_coprime (s := sP K N) hne).2 (sP_coprime N)
  refine ⟨fun r => μ r * ∏ j ∈ Lam K N \ {r}, sP K N j, hμ, fun r hr => ⟨μ r, ?_⟩⟩
  rw [Q_eq_prod N, ← Finset.prod_sdiff (Finset.singleton_subset_iff.2 hr), prod_singleton]
  ring

/-! ### Più variabili -/

variable {d : ℕ}

/-- L'ideale del blocco `lv`: `((X_i - lv_i)^{m})`. -/
noncomputable def Ib (n : Fin d → ℕ) (lv : Fin d → K) : Ideal (MvPolynomial (Fin d) K) :=
  Ideal.span (Set.range fun i => Polynomial.aeval (X i) (sP K (n i) (lv i)))

/-- **Incollamento.** Se `c ≡ m y` in ogni blocco, allora `c ≡ m Y` modulo `(Q_{n_i}(X_i))`. -/
lemma glue (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (c m : MvPolynomial (Fin d) K)
    (h : ∀ lv ∈ Fintype.piFinset (fun i => Lam K (n i)), ∃ y, c - m * y ∈ Ib n lv) :
    ∃ Y, c - m * Y ∈ Jid K n := by
  choose e he1 he2 using fun i => idem_exists (K := K) (n i) (hn i)
  set E : (Fin d → K) → MvPolynomial (Fin d) K :=
    fun lv => ∏ i, Polynomial.aeval (X i) (e i (lv i)) with hE
  have hsum : ∑ lv ∈ Fintype.piFinset (fun i => Lam K (n i)), E lv = 1 := by
    rw [hE, ← prod_univ_sum (fun i => Lam K (n i))
      (fun i r => Polynomial.aeval (X i : MvPolynomial (Fin d) K) (e i r))]
    refine prod_eq_one fun i _ => ?_
    rw [← map_sum, he1 i, map_one]
  have hEI : ∀ lv ∈ Fintype.piFinset (fun i => Lam K (n i)), ∀ p ∈ Ib n lv, E lv * p ∈ Jid K n := by
    intro lv hlv p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨g, hg⟩ := he2 i (lv i) (Fintype.mem_piFinset.1 hlv i)
      have e1 : E lv = Polynomial.aeval (X i) (e i (lv i)) *
          ∏ j ∈ univ.erase i, Polynomial.aeval (X j : MvPolynomial (Fin d) K) (e j (lv j)) :=
        (mul_prod_erase univ _ (mem_univ i)).symm
      have e2 : E lv * Polynomial.aeval (X i) (sP K (n i) (lv i)) =
          qq K i (n i) * (Polynomial.aeval (X i) g *
            ∏ j ∈ univ.erase i, Polynomial.aeval (X j : MvPolynomial (Fin d) K) (e j (lv j))) := by
        rw [e1, qq, mul_comm (Polynomial.aeval (X i) (e i (lv i))), mul_assoc, ← map_mul, hg,
          map_mul]
        ring
      rw [e2]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
  have h' : ∀ lv, ∃ y, lv ∈ Fintype.piFinset (fun i => Lam K (n i)) → c - m * y ∈ Ib n lv := by
    intro lv
    by_cases hlv : lv ∈ Fintype.piFinset (fun i => Lam K (n i))
    · obtain ⟨y, hy⟩ := h lv hlv; exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hlv⟩
  choose y hy using h'
  refine ⟨∑ lv ∈ Fintype.piFinset (fun i => Lam K (n i)), E lv * y lv, ?_⟩
  have e : ∑ lv ∈ Fintype.piFinset (fun i => Lam K (n i)), E lv * (c - m * y lv) =
      (∑ lv ∈ Fintype.piFinset (fun i => Lam K (n i)), E lv) * c -
        m * ∑ lv ∈ Fintype.piFinset (fun i => Lam K (n i)), E lv * y lv := by
    rw [sum_mul, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun lv _ => ?_
    ring
  rw [hsum, one_mul] at e
  rw [← e]
  exact sum_mem fun lv hlv => hEI lv hlv _ (hy lv hlv)

/-! ### Un blocco: lo spostamento `X_i ↦ α_i X_i + lv_i` -/

/-- Lo spostamento in avanti. -/
noncomputable def rhoP (lv α : Fin d → K) : MvPolynomial (Fin d) K →ₐ[K] MvPolynomial (Fin d) K :=
  aeval fun i => C (α i) * X i + C (lv i)

/-- Lo spostamento all'indietro. -/
noncomputable def rhoM (lv α : Fin d → K) : MvPolynomial (Fin d) K →ₐ[K] MvPolynomial (Fin d) K :=
  aeval fun i => C (α i)⁻¹ * (X i - C (lv i))

lemma rhoM_rhoP (lv α : Fin d → K) (hα : ∀ i, α i ≠ 0) (p : MvPolynomial (Fin d) K) :
    rhoM lv α (rhoP lv α p) = p := by
  have : (rhoM lv α).comp (rhoP lv α) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rhoP, rhoM, aeval_X, map_add, map_mul, aeval_C,
      algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hα i), C_1, one_mul]
    ring
  exact congrArg (fun φ => φ p) this

/-- L'istanza locale del blocco `lv`. -/
noncomputable def fl (n : Fin d → ℕ) (lv : Fin d → K) : Fin d → Factor :=
  fun i => if lv i = 0 then Factor.Z (SigmaMeno.a (n i) - 1) else Factor.N (SigmaMeno.a (n i))

lemma fl_data (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (lv : Fin d → K)
    (hlv : lv ∈ Fintype.piFinset (fun i => Lam K (n i))) (i : Fin d) :
    Polynomial.rootMultiplicity (lv i) (Q K (n i)) = (fl n lv i).s ∧
      Polynomial.rootMultiplicity (lv i) (f K (n i)) = (fl n lv i).j := by
  obtain ⟨M, hM, hnM, ha⟩ := odd_decomp (n i) (hn i)
  have hroot : (Q K (n i)).IsRoot (lv i) := mem_Lam.1 (Fintype.mem_piFinset.1 hlv i)
  have hd := mult_data (K := K) (n i) (SigmaMeno.a (n i)) M hnM ha hM (lv i) hroot
  by_cases h0 : lv i = 0
  · obtain ⟨h1, h2⟩ := hd.1 h0
    simp only [fl, h0, if_true]
    refine ⟨?_, ?_⟩
    · rw [← h0, h1]; simp only [Factor.s]; rw [← pow_succ', Nat.sub_add_cancel ha]
    · rw [← h0, h2]; rfl
  · obtain ⟨h1, h2⟩ := hd.2 h0
    simp only [fl, h0, if_false]
    refine ⟨?_, ?_⟩
    · rw [h1]; simp only [Factor.s]; rw [pow_succ']
    · rw [h2]; rfl

/-- `rhoM` manda l'ideale locale dentro l'ideale del blocco. -/
lemma rhoM_I (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (lv α : Fin d → K)
    (hlv : lv ∈ Fintype.piFinset (fun i => Lam K (n i))) {p : MvPolynomial (Fin d) K}
    (hp : p ∈ Locale.I K (fl n lv)) : rhoM lv α p ∈ Ib n lv := by
  have : Locale.I K (fl n lv) ≤ Ideal.comap (rhoM lv α) (Ib n lv) := by
    unfold Locale.I
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, rhoM, aeval_X, mul_pow]
    have hs := (fl_data n hn lv hlv i).1
    have hgen : (X i - C (lv i) : MvPolynomial (Fin d) K) ^ (fl n lv i).s =
        Polynomial.aeval (X i) (sP K (n i) (lv i)) := by
      simp [sP, hs]
    rw [hgen]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  exact this hp

/-- Da una relazione locale a una relazione nel blocco. -/
lemma block_of_local (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (lv α : Fin d → K)
    (hα : ∀ i, α i ≠ 0) (hlv : lv ∈ Fintype.piFinset (fun i => Lam K (n i)))
    (c m : MvPolynomial (Fin d) K)
    (h : ∃ y, rhoP lv α c - rhoP lv α m * y ∈ Locale.I K (fl n lv)) :
    ∃ y, c - m * y ∈ Ib n lv := by
  obtain ⟨y, hy⟩ := h
  refine ⟨rhoM lv α y, ?_⟩
  have := rhoM_I n hn lv α hlv hy
  rwa [map_sub, map_mul, rhoM_rhoP lv α hα, rhoM_rhoP lv α hα] at this

/-- `rhoP (c) = cc · W` con `W` invertibile nell'anello locale. -/
lemma c_shift (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (lv α : Fin d → K) (hα : ∀ i, α i ≠ 0)
    (hlv : lv ∈ Fintype.piFinset (fun i => Lam K (n i))) :
    ∃ W, rhoP lv α (∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) K) (f K (n i))) =
      Locale.cc K (fl n lv) * W ∧ IsUnit (Ideal.Quotient.mk (Locale.I K (fl n lv)) W) := by
  have hex : ∀ i, ∃ U : Polynomial K, rhoP lv α (Polynomial.aeval (X i) (f K (n i))) =
      X i ^ (fl n lv i).j * Polynomial.aeval (X i) U ∧ U.coeff 0 ≠ 0 := by
    intro i
    have hf0 : f K (n i) ≠ 0 := f_ne_zero_odd (n i) (hn i)
    obtain ⟨U, hU, hndvd⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (f K (n i)) hf0 (lv i)
    rw [(fl_data n hn lv hlv i).2] at hU
    rw [Polynomial.dvd_iff_isRoot] at hndvd
    refine ⟨Polynomial.C (α i ^ (fl n lv i).j) *
      U.comp (Polynomial.C (α i) * Polynomial.X + Polynomial.C (lv i)), ?_, ?_⟩
    · rw [← Polynomial.aeval_algHom_apply, hU]
      simp only [rhoP, aeval_X, map_mul, map_pow, map_sub, Polynomial.aeval_X,
        Polynomial.aeval_C, Polynomial.aeval_comp, map_add, algebraMap_eq]
      ring
    · rw [Polynomial.coeff_zero_eq_eval_zero]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X, mul_zero, zero_add]
      exact mul_ne_zero (pow_ne_zero _ (hα i)) hndvd
  choose U hU hU0 using hex
  refine ⟨∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) K) (U i), ?_, ?_⟩
  · rw [map_prod, Locale.cc, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => hU i
  · rw [map_prod]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => isUnit_aeval (fl n lv) i (U i) (hU0 i))

/-- Dalla raggiungibilità locale alla relazione spostata. -/
lemma shifted_of_reach (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (lv α : Fin d → K)
    (hα : ∀ i, α i ≠ 0) (hlv : lv ∈ Fintype.piFinset (fun i => Lam K (n i)))
    (m u : MvPolynomial (Fin d) K) (hm : rhoP lv α m = u) (hr : Locale.Reach (fl n lv) u) :
    ∃ y, rhoP lv α (∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) K) (f K (n i))) -
      rhoP lv α m * y ∈ Locale.I K (fl n lv) := by
  obtain ⟨W, hW, -⟩ := c_shift n hn lv α hα hlv
  obtain ⟨y, hy⟩ := hr
  refine ⟨y * W, ?_⟩
  rw [hW, hm]
  have : Locale.cc K (fl n lv) * W - u * (y * W) = W * (Locale.cc K (fl n lv) - u * y) := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ hy

/-- Se `m` spostato è invertibile nell'anello locale, la relazione spostata c'è. -/
lemma shifted_of_unit (n : Fin d → ℕ) (lv α : Fin d → K) (c m : MvPolynomial (Fin d) K)
    (hu : IsUnit (Ideal.Quotient.mk (Locale.I K (fl n lv)) (rhoP lv α m))) :
    ∃ y, rhoP lv α c - rhoP lv α m * y ∈ Locale.I K (fl n lv) := by
  obtain ⟨v, hv⟩ := hu
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
    (((v⁻¹ : (MvPolynomial (Fin d) K ⧸ Locale.I K (fl n lv))ˣ) :
      MvPolynomial (Fin d) K ⧸ Locale.I K (fl n lv)) *
      Ideal.Quotient.mk (Locale.I K (fl n lv)) (rhoP lv α c))
  refine ⟨y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, ← hv, ← mul_assoc, Units.mul_inv,
    one_mul, sub_self]

/-- `X_i` è nilpotente nell'anello locale. -/
lemma nil_X (f₀ : Fin d → Factor) (i : Fin d) :
    IsNilpotent (Ideal.Quotient.mk (Locale.I K f₀) (X i)) :=
  ⟨(f₀ i).s, by rw [← map_pow]; exact Locale.mk_X_pow f₀ i le_rfl⟩

/-- `∏ (C a_i + X_i) - ∏ a_i` è nilpotente nell'anello locale. -/
lemma nil_prod (f₀ : Fin d → Factor) (a : Fin d → K) (S : Finset (Fin d)) :
    IsNilpotent (Ideal.Quotient.mk (Locale.I K f₀) (∏ i ∈ S, (C (a i) + X i)) -
      algebraMap K _ (∏ i ∈ S, a i)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [prod_insert hj, prod_insert hj, map_mul, map_mul]
    set x := Ideal.Quotient.mk (Locale.I K f₀) (C (a j) + X j)
    set y := Ideal.Quotient.mk (Locale.I K f₀) (∏ i ∈ S, (C (a i) + X i))
    have hx : IsNilpotent (x - algebraMap K _ (a j)) := by
      have hC : Ideal.Quotient.mk (Locale.I K f₀) (C (a j)) = algebraMap K _ (a j) := rfl
      have : x - algebraMap K _ (a j) = Ideal.Quotient.mk (Locale.I K f₀) (X j) := by
        simp only [x, map_add, hC]; ring
      rw [this]; exact nil_X f₀ j
    have e : x * y - algebraMap K _ (a j) * algebraMap K _ (∏ i ∈ S, a i) =
        (x - algebraMap K _ (a j)) * y +
          algebraMap K _ (a j) * (y - algebraMap K _ (∏ i ∈ S, a i)) := by ring
    rw [e]
    exact (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_mul_right hx)
      ((Commute.all _ _).isNilpotent_mul_left ih)

end SigmaMeno.Globale
