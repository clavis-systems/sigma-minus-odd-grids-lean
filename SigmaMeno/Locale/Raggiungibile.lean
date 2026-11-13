import SigmaMeno.Locale.Testimone

/-!
# Il problema locale: la parte "raggiungibile" e il teorema locale (vicinato edge)

* Lemma D (dimezzamento), con la sostituzione `X_i ↦ X_i^2`;
* Lemma E (livelli `≤ 1`);
* Lemma F (coppie in cima);
* induzione sul livello più alto;
* **teorema locale**: `Reach f (uE F ι) ↔ Cond f`.
-/

namespace SigmaMeno.Locale

open MvPolynomial Finset Factor

/-! ### Fatti sui livelli -/

namespace Factor

lemma level_half : ∀ x : Factor, x.half.level = x.level - 1
  | Z 0 => rfl
  | Z (_ + 1) => rfl
  | N 0 => rfl
  | N (_ + 1) => rfl

lemma s_le_of_level_lt (x : Factor) (T : ℕ) (h : x.level < T) : x.s ≤ 2 ^ T := by
  cases x with
  | Z b =>
    simp only [level] at h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show b + 1 ≤ T by omega)
    simp only [s]; rw [pow_succ] at this; omega
  | N a =>
    simp only [level] at h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show a + 1 ≤ T by omega)
    simp only [s]; rw [pow_succ] at this; omega

lemma level_le_of_ne (x : Factor) (T : ℕ) (h : x.level ≤ T + 1) (hZ : x ≠ Z (T + 1))
    (hN : x ≠ N T) : x.level ≤ T := by
  cases x with
  | Z b =>
    simp only [level] at h ⊢
    have : b ≠ T + 1 := fun hb => hZ (by rw [hb])
    omega
  | N a =>
    simp only [level] at h ⊢
    have : a ≠ T := fun ha => hN (by rw [ha])
    omega

lemma level_le_one_cases (x : Factor) (h : x.level ≤ 1) : x = Z 0 ∨ x = Z 1 ∨ x = N 0 := by
  cases x with
  | Z b =>
    simp only [level] at h
    interval_cases b <;> simp
  | N a =>
    simp only [level] at h
    have : a = 0 := by omega
    simp [this]

end Factor

variable {F : Type*} [Field F] [CharP F 2] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharP F 2] in
/-- Se fuori da `S` tutti i fattori sono banali, `c` è il prodotto su `S`. -/
lemma cc_eq_prod (f : ι → Factor) (S : Finset ι) (hS : ∀ l ∉ S, f l = Z 0) :
    cc F f = ∏ l ∈ S, X l ^ (f l).j := by
  rw [cc_split f S, cc_triv]
  have : ∏ i ∈ univ.filter (· ∉ S), (X i ^ (f i).j : MvPolynomial ι F) = 1 :=
    prod_eq_one fun i hi => by
      have hi' : i ∉ S := by simpa using hi
      simp [hS i hi', Factor.j]
  rw [this, mul_one]

omit [CharP F 2] in
/-- Se fuori da `S` tutti i fattori sono banali, nel quoziente `u` è la somma su `S`. -/
lemma mk_uE_eq (f : ι → Factor) (S : Finset ι) (hS : ∀ l ∉ S, f l = Z 0) :
    Ideal.Quotient.mk (I F f) (uE F ι) = Ideal.Quotient.mk (I F f) (∑ l ∈ S, X l) := by
  rw [uE_split S, map_add, add_eq_left, map_sum]
  refine sum_eq_zero fun l hl => ?_
  have hl' : l ∉ S := by simpa using hl
  have := mk_X_pow (F := F) f l (n := 1) (by rw [hS l hl']; rfl)
  rwa [pow_one] at this

/-- **Lemma C nel quoziente** per un insieme pari di fattori `Z b` (`2^b = n + 2`). -/
lemma lemmaC_mk (f : ι → Factor) (S : Finset ι) {b n : ℕ} (hq : 2 ^ b = n + 2)
    (hS : ∀ l ∈ S, f l = Z b) (hev : Even S.card) :
    ∃ e Y : MvPolynomial ι F ⧸ I F f,
      Ideal.Quotient.mk (I F f) (∏ l ∈ S, X l ^ (n + 1)) =
        e + Ideal.Quotient.mk (I F f) (∑ l ∈ S, X l) ^ (n + 2) * Y ∧
      Ideal.Quotient.mk (I F f) (∑ l ∈ S, X l) * e = 0 := by
  have h2 : (2 : MvPolynomial ι F ⧸ I F f) = 0 := two_eq_zero_alg (F := F) _
  have hx : ∀ l ∈ S, (Ideal.Quotient.mk (I F f) (X l)) ^ (2 * n + 3) = 0 := by
    intro l hl
    rw [← map_pow]
    exact mk_X_pow f l (by rw [hS l hl]; simp only [Factor.s]; omega)
  obtain ⟨e, Y, h1, h2'⟩ := lemmaC h2 (fun l => Ideal.Quotient.mk (I F f) (X l)) n b hq S hev hx
  refine ⟨e, Y, ?_, ?_⟩
  · rw [map_prod, map_sum]; simpa using h1
  · rw [map_sum]; exact h2'

/-! ### Lemma D: il dimezzamento -/

/-- **Lemma D.** Se l'istanza dimezzata è raggiungibile, lo è anche l'istanza. -/
lemma lemmaD (f : ι → Factor) (h : Reach (fun l => (f l).half) (uE F ι)) :
    Reach f (uE F ι) := by
  obtain ⟨y, hy⟩ := h
  set Φ : MvPolynomial ι F →ₐ[F] MvPolynomial ι F := aeval fun l => X l ^ 2 with hΦ
  set P : MvPolynomial ι F := ∏ l, X l ^ (f l).par with hP
  have key : ∀ p ∈ I F (fun l => (f l).half), P * Φ p ∈ I F f := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      have e : P * Φ (X l ^ (f l).half.s) =
          X l ^ ((f l).par + 2 * (f l).half.s) * ∏ m ∈ univ.erase l, X m ^ (f m).par := by
        rw [hP, ← mul_prod_erase univ _ (mem_univ l), map_pow, hΦ, aeval_X]
        ring
      rw [e]
      exact Ideal.mul_mem_right _ _
        (X_pow_mem_of_le f l (by have := Factor.s_le_half (f l); omega))
    | zero => simp
    | add x z _ _ hx hz => rw [map_add, mul_add]; exact add_mem hx hz
    | smul a x _ hx =>
      rw [smul_eq_mul, map_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hx
  have hc : cc F f = P * Φ (cc F (fun l => (f l).half)) := by
    rw [hP, cc, cc, map_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun l _ => ?_
    rw [map_pow, hΦ, aeval_X, ← pow_mul, ← pow_add, Factor.j_half (f l)]
    ring_nf
  have hu : Φ (uE F ι) = uE F ι ^ 2 := by
    have h2 : (2 : MvPolynomial ι F) = 0 := two_eq_zero_alg (F := F) _
    have := frob_sum h2 univ (fun l => (X l : MvPolynomial ι F)) 1
    rw [uE, map_sum, hΦ]
    simp only [aeval_X, pow_one] at this ⊢
    exact this.symm
  refine ⟨uE F ι * P * Φ y, ?_⟩
  have := key _ hy
  rw [map_sub, map_mul, hu] at this
  convert this using 1
  rw [hc]
  ring

/-! ### Lemma F: le coppie in cima -/

/-- **Lemma F.** Al livello più alto `T + 1` ci sono solo fattori `Z`, in numero pari; se
l'istanza senza di loro è raggiungibile, lo è anche l'istanza. -/
lemma lemmaF (f : ι → Factor) (T n : ℕ) (hq : 2 ^ (T + 1) = n + 2)
    (hlev : ∀ l, (f l).level ≤ T + 1) (hN : ∀ l, f l ≠ N T)
    (hev : Even (univ.filter (fun l => f l = Z (T + 1))).card)
    (hR : Reach (triv f (univ.filter (fun l => f l = Z (T + 1)))) (uE F ι)) :
    Reach f (uE F ι) := by
  set B := univ.filter (fun l => f l = Z (T + 1)) with hB
  have h2 : (2 : MvPolynomial ι F ⧸ I F f) = 0 := two_eq_zero_alg (F := F) _
  obtain ⟨y, hy⟩ := lift_reach hR
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul] at hy
  have hSB : ∀ l ∈ B, f l = Z (T + 1) := fun l hl => by simpa [hB] using hl
  obtain ⟨e, Y, hc, hue⟩ := lemmaC_mk (F := F) f B hq hSB hev
  -- le variabili fuori da `B` hanno `X ^ q = 0`
  have hR0 : (Ideal.Quotient.mk (I F f) (∑ l ∈ univ.filter (· ∉ B), X l)) ^ (n + 2) = 0 := by
    rw [← hq, map_sum, frob_sum h2]
    refine sum_eq_zero fun l hl => ?_
    have hl' : l ∉ B := by simpa using hl
    have hZ : f l ≠ Z (T + 1) := fun h => hl' (by simp [hB, h])
    have hlt : (f l).level < T + 1 :=
      Nat.lt_succ_of_le (Factor.level_le_of_ne _ T (hlev l) hZ (hN l))
    rw [← map_pow]
    exact mk_X_pow f l (Factor.s_le_of_level_lt _ _ hlt)
  have hfrob : (Ideal.Quotient.mk (I F f) (∑ l ∈ B, X l)
      + Ideal.Quotient.mk (I F f) (∑ l ∈ univ.filter (· ∉ B), X l)) ^ (n + 2) =
      (Ideal.Quotient.mk (I F f) (∑ l ∈ B, X l)) ^ (n + 2)
      + (Ideal.Quotient.mk (I F f) (∑ l ∈ univ.filter (· ∉ B), X l)) ^ (n + 2) := by
    rw [← hq]; exact frob_add h2 _ _ _
  have hcB : (∏ i ∈ B, (X i ^ (f i).j : MvPolynomial ι F)) = ∏ l ∈ B, X l ^ (n + 1) :=
    prod_congr rfl fun l hl => by
      rw [hSB l hl]; simp only [Factor.j]; congr 1; omega
  rw [reach_iff_mk]
  refine ⟨Ideal.Quotient.mk (I F f) y * e
    + (Ideal.Quotient.mk (I F f) (∑ l ∈ B, X l)
      + Ideal.Quotient.mk (I F f) (∑ l ∈ univ.filter (· ∉ B), X l)) ^ (n + 1)
      * Ideal.Quotient.mk (I F f) (∑ l ∈ univ.filter (· ∉ B), X l)
      * Ideal.Quotient.mk (I F f) y * Y, ?_⟩
  rw [cc_split f B, uE_split B, hcB, map_mul, map_add]
  linear_combination
    (Ideal.Quotient.mk (I F f) (∏ l ∈ B, X l ^ (n + 1))) * hy
    + (Ideal.Quotient.mk (I F f) (∑ l ∈ univ.filter (· ∉ B), X l)
      * Ideal.Quotient.mk (I F f) y) * hc
    - Ideal.Quotient.mk (I F f) y * hue
    - (Ideal.Quotient.mk (I F f) (∑ l ∈ univ.filter (· ∉ B), X l)
      * Ideal.Quotient.mk (I F f) y * Y) * hfrob
    - (Ideal.Quotient.mk (I F f) (∑ l ∈ univ.filter (· ∉ B), X l)
      * Ideal.Quotient.mk (I F f) y * Y) * hR0

/-! ### Lemma E: i livelli `≤ 1` -/

/-- Lemma E, caso senza fattori `N`: un numero dispari di fattori `Z_2`. -/
lemma lemmaE_odd (f : ι → Factor) (hlev : ∀ l, (f l).level ≤ 1) (hno : ∀ l, f l ≠ N 0)
    (hodd : Odd (univ.filter (fun l => f l = Z 1)).card) : Reach f (uE F ι) := by
  set Sz := univ.filter (fun l => f l = Z 1) with hSz
  have h2 : (2 : MvPolynomial ι F ⧸ I F f) = 0 := two_eq_zero_alg (F := F) _
  have hSzZ : ∀ l ∈ Sz, f l = Z 1 := fun l hl => by simpa [hSz] using hl
  have hout : ∀ l ∉ Sz, f l = Z 0 := by
    intro l hl
    rcases Factor.level_le_one_cases _ (hlev l) with h | h | h
    · exact h
    · exact absurd (by simp [hSz, h]) hl
    · exact absurd h (hno l)
  obtain ⟨i, hi⟩ : Sz.Nonempty := card_pos.1 (by obtain ⟨r, hr⟩ := hodd; omega)
  have hev : Even (Sz.erase i).card := by
    rw [card_erase_of_mem hi]; obtain ⟨r, hr⟩ := hodd; exact ⟨r, by omega⟩
  obtain ⟨e, Y, hc, hue⟩ := lemmaC_mk (F := F) f (Sz.erase i) (b := 1) (n := 0) rfl
    (fun l hl => hSzZ l (mem_of_mem_erase hl)) hev
  have hx3 : (Ideal.Quotient.mk (I F f) (X i)) ^ 3 = 0 := by
    rw [← map_pow]; exact mk_X_pow f i (by rw [hSzZ i hi]; rfl)
  rw [reach_iff_mk, cc_eq_prod f Sz hout, mk_uE_eq f Sz hout]
  have hcS : (∏ l ∈ Sz, (X l ^ (f l).j : MvPolynomial ι F)) =
      X i * ∏ l ∈ Sz.erase i, X l ^ (0 + 1) := by
    rw [← mul_prod_erase Sz _ hi, hSzZ i hi]
    congr 1
    · simp [Factor.j]
    · exact prod_congr rfl fun l hl => by rw [hSzZ l (mem_of_mem_erase hl)]; rfl
  rw [hcS, ← add_sum_erase Sz _ hi]
  simp only [map_mul, map_add]
  refine ⟨e + (Ideal.Quotient.mk (I F f) (X i)
    + Ideal.Quotient.mk (I F f) (∑ l ∈ Sz.erase i, X l)) * Ideal.Quotient.mk (I F f) (X i) * Y,
    ?_⟩
  linear_combination Ideal.Quotient.mk (I F f) (X i) * hc - hue - Y * hx3
    - ((Ideal.Quotient.mk (I F f) (X i)) ^ 2
      * Ideal.Quotient.mk (I F f) (∑ l ∈ Sz.erase i, X l) * Y) * h2

/-- **Lemma E.** Con tutti i livelli `≤ 1` e il livello 1 buono, l'istanza è raggiungibile. -/
lemma lemmaE (f : ι → Factor) (hlev : ∀ l, (f l).level ≤ 1) (hg : Good f 1) :
    Reach f (uE F ι) := by
  suffices H : ∀ m : ℕ, ∀ f : ι → Factor, (∀ l, (f l).level ≤ 1) → Good f 1 →
      (univ.filter (fun l => f l = N 0)).card ≤ m → Reach f (uE F ι) from
    H _ f hlev hg le_rfl
  intro m
  induction m with
  | zero =>
    intro f hlev hg hm
    have hno : ∀ l, f l ≠ N 0 := fun l hl => by
      have : l ∈ univ.filter (fun l => f l = N 0) := by simp [hl]
      have := card_pos.2 ⟨l, this⟩
      omega
    rcases hg with ⟨l, hl⟩ | ho
    · exact absurd hl (hno l)
    · exact lemmaE_odd f hlev hno ho
  | succ m ih =>
    intro f hlev hg hm
    by_cases hex : ∃ i, f i = N 0
    swap
    · push_neg at hex
      rcases hg with ⟨l, hl⟩ | ho
      · exact absurd hl (hex l)
      · exact lemmaE_odd f hlev hex ho
    obtain ⟨i, hi⟩ := hex
    have h2 : (2 : MvPolynomial ι F ⧸ I F f) = 0 := two_eq_zero_alg (F := F) _
    have hη2 : (Ideal.Quotient.mk (I F f) (X i)) ^ 2 = 0 := by
      rw [← map_pow]; exact mk_X_pow f i (by rw [hi]; rfl)
    have hcc : cc F f = X i * cc F (triv f {i}) := by
      rw [cc_split f {i}, prod_singleton, hi]; simp [Factor.j]
    have hgl : ∀ l, (triv f {i} l).level ≤ 1 := fun l => by
      simp only [triv]; split_ifs
      · simp [Factor.level]
      · exact hlev l
    have hZsame : univ.filter (fun l => triv f {i} l = Z 1) =
        univ.filter (fun l => f l = Z 1) := by
      ext l
      simp only [mem_filter, mem_univ, true_and]
      simp only [triv, mem_singleton]
      split_ifs with h
      · subst h; simp [hi]
      · rfl
    by_cases hgg : Good (triv f {i}) 1
    · -- caso (a): l'istanza senza `η` è raggiungibile
      have hcard : (univ.filter (fun l => triv f {i} l = N 0)).card ≤ m := by
        have hsub : univ.filter (fun l => triv f {i} l = N 0) ⊆
            (univ.filter (fun l => f l = N 0)).erase i := by
          intro l hl
          simp only [mem_filter, mem_univ, true_and, mem_erase] at hl ⊢
          simp only [triv, mem_singleton] at hl
          split_ifs at hl with h
          exact ⟨h, hl⟩
        have hle := card_le_card hsub
        rw [card_erase_of_mem (by simp [hi])] at hle
        omega
      obtain ⟨y, hy⟩ := lift_reach (ih _ hgl hgg hcard)
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul] at hy
      rw [reach_iff_mk, hcc, uE_split {i}, sum_singleton]
      refine ⟨Ideal.Quotient.mk (I F f) (X i) * Ideal.Quotient.mk (I F f) y, ?_⟩
      simp only [map_mul, map_add]
      linear_combination Ideal.Quotient.mk (I F f) (X i) * hy
        - Ideal.Quotient.mk (I F f) y * hη2
    · -- caso (b): senza `η` restano solo coppie di `Z_2`
      have hno : ∀ l, l ≠ i → f l ≠ N 0 := by
        intro l hl hfl
        apply hgg
        left
        exact ⟨l, by simp [triv, hl, hfl]⟩
      have hev : Even (univ.filter (fun l => f l = Z 1)).card := by
        rw [← hZsame]
        rcases Nat.even_or_odd (univ.filter (fun l => triv f {i} l = Z 1)).card with he | ho
        · exact he
        · exact absurd (Or.inr ho) hgg
      set Sz := univ.filter (fun l => f l = Z 1) with hSz
      have hSzZ : ∀ l ∈ Sz, f l = Z 1 := fun l hl => by simpa [hSz] using hl
      have hiS : i ∉ Sz := by simp [hSz, hi]
      have hout : ∀ l ∉ insert i Sz, f l = Z 0 := by
        intro l hl
        rw [mem_insert, not_or] at hl
        rcases Factor.level_le_one_cases _ (hlev l) with h | h | h
        · exact h
        · exact absurd (by simp [hSz, h]) hl.2
        · exact absurd h (hno l hl.1)
      obtain ⟨e, Y, hc, hue⟩ := lemmaC_mk (F := F) f Sz (b := 1) (n := 0) rfl hSzZ hev
      rw [reach_iff_mk, cc_eq_prod f (insert i Sz) hout, mk_uE_eq f (insert i Sz) hout,
        prod_insert hiS, sum_insert hiS, hi]
      have hcS : (∏ l ∈ Sz, (X l ^ (f l).j : MvPolynomial ι F)) = ∏ l ∈ Sz, X l ^ (0 + 1) :=
        prod_congr rfl fun l hl => by rw [hSzZ l hl]; rfl
      rw [hcS]
      simp only [map_mul, map_add, map_pow]
      refine ⟨e + Ideal.Quotient.mk (I F f) (X i)
        * Ideal.Quotient.mk (I F f) (∑ l ∈ Sz, X l) * Y, ?_⟩
      have hj : (N 0).j = 1 := rfl
      rw [hj, pow_one]
      linear_combination Ideal.Quotient.mk (I F f) (X i) * hc
        - Ideal.Quotient.mk (I F f) (∑ l ∈ Sz, X l) * Y * hη2 - hue

/-! ### Il teorema locale -/

lemma good_half (f : ι → Factor) (T : ℕ) (hT : 1 ≤ T) :
    Good (fun l => (f l).half) T ↔ Good f (T + 1) := by
  unfold Good
  have hfilt : univ.filter (fun l => (f l).half = Z T) = univ.filter (fun l => f l = Z (T + 1)) := by
    ext l; simp [Factor.half_eq_Z_iff _ _ hT]
  rw [hfilt]
  simp only [Factor.half_eq_N_iff, Nat.add_sub_cancel]
  have : T - 1 + 1 = T := by omega
  rw [this]

/-- **Parte "raggiungibile" del teorema locale (edge).** -/
theorem reach_of_cond (f : ι → Factor) (h : Cond f) : Reach f (uE F ι) := by
  suffices H : ∀ T : ℕ, ∀ f : ι → Factor, (∀ l, (f l).level ≤ T) → Cond f →
      Reach f (uE F ι) from
    H _ f (fun l => le_sup (f := fun l => (f l).level) (mem_univ l)) h
  intro T
  induction T with
  | zero =>
    intro f hlev ⟨ℓ, hℓ, hg⟩
    exfalso
    rcases hg with ⟨l, hl⟩ | ho
    · have := hlev l; rw [hl] at this; simp [Factor.level] at this
    · have hempty : univ.filter (fun l => f l = Z ℓ) = ∅ := by
        ext l; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hl; have := hlev l; rw [hl] at this; simp [Factor.level] at this; omega
      rw [hempty] at ho; simp at ho
  | succ T ih =>
    intro f hlev hc
    by_cases hgT : Good f (T + 1)
    · rcases Nat.eq_zero_or_pos T with hT | hT
      · subst hT; exact lemmaE f hlev hgT
      · apply lemmaD
        apply ih
        · intro l; rw [Factor.level_half]; have := hlev l; omega
        · exact ⟨T, hT, (good_half f T hT).2 hgT⟩
    · obtain ⟨ℓ, hℓ, hg⟩ := hc
      have hℓT : ℓ ≤ T := by
        by_contra hcon
        rcases Nat.lt_or_ge (T + 1) ℓ with hlt | hge
        · rcases hg with ⟨l, hl⟩ | ho
          · have := hlev l; rw [hl] at this; simp [Factor.level] at this; omega
          · have hempty : univ.filter (fun l => f l = Z ℓ) = ∅ := by
              ext l; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
              intro hl; have := hlev l; rw [hl] at this; simp [Factor.level] at this; omega
            rw [hempty] at ho; simp at ho
        · have : ℓ = T + 1 := by omega
          exact hgT (this ▸ hg)
      have hN : ∀ l, f l ≠ N T := fun l hl => hgT (Or.inl ⟨l, by simp [hl]⟩)
      have hev : Even (univ.filter (fun l => f l = Z (T + 1))).card := by
        rcases Nat.even_or_odd (univ.filter (fun l => f l = Z (T + 1))).card with he | ho
        · exact he
        · exact absurd (Or.inr ho) hgT
      have h2T : 2 ≤ 2 ^ (T + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (T + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine lemmaF f T (2 ^ (T + 1) - 2) (by omega) hlev hN hev (ih _ ?_ ?_)
      · intro l
        simp only [triv, mem_filter, mem_univ, true_and]
        split_ifs with h
        · simp [Factor.level]
        · exact Factor.level_le_of_ne _ T (hlev l) h (hN l)
      · refine ⟨ℓ, hℓ, ?_⟩
        have hfilt : univ.filter
            (fun l => triv f (univ.filter (fun l => f l = Z (T + 1))) l = Z ℓ) =
            univ.filter (fun l => f l = Z ℓ) := by
          ext l
          simp only [mem_filter, mem_univ, true_and]
          simp only [triv, mem_filter, mem_univ, true_and]
          split_ifs with h
          · rw [h]; simp only [Factor.Z.injEq]; omega
          · rfl
        unfold Good
        rw [hfilt]
        rcases hg with ⟨l, hl⟩ | ho
        · left
          refine ⟨l, ?_⟩
          simp only [triv, mem_filter, mem_univ, true_and]
          split_ifs with h
          · rw [hl] at h; exact absurd h (by simp)
          · exact hl
        · exact Or.inr ho

/-- **Il teorema locale, vicinato edge.** -/
theorem local_theorem_edge (f : ι → Factor) : Reach f (uE F ι) ↔ Cond f := by
  constructor
  · intro hr
    by_contra hc
    exact not_reach_of_witness (witness_of_not_cond f hc) hr
  · exact reach_of_cond f

end SigmaMeno.Locale
