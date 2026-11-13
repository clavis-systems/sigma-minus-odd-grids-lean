import SigmaMeno.Locale.Base

/-!
# Il problema locale: la parte "non raggiungibile"

Se nessun livello `≥ 1` è buono, i fattori non banali sono tutti `Z_q` e a ogni livello sono in
numero pari: si possono accoppiare. Il testimone è il prodotto dei testimoni delle coppie
(`hh y z (2q-2)` per ogni coppia), costruito togliendo una coppia alla volta.
È la parte "non raggiungibile" del teorema locale (Lemmi A e B della nota).
-/

namespace SigmaMeno.Locale

open MvPolynomial Finset Factor

variable {F : Type*} [Field F] [CharP F 2] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharP F 2] in
/-- Il testimone quando tutti i fattori sono banali: `k = 1`. -/
lemma witness_trivial (f : ι → Factor) (hf : ∀ i, f i = Z 0) : Witness f (uE F ι) := by
  refine ⟨1, ?_, ?_⟩
  · rw [mul_one, uE]
    refine sum_mem fun i _ => ?_
    have h := X_pow_mem (F := F) f i
    have h1 : (f i).s = 1 := by rw [hf i]; rfl
    rwa [h1, pow_one] at h
  · have hc : cc F f = 1 := prod_eq_one fun i _ => by simp [hf i, Factor.j]
    have ht : top F f = 1 := prod_eq_one fun i _ => by simp [hf i, Factor.s]
    rw [hc, ht, mul_one, sub_self]
    exact zero_mem _

/-- Aggiungere una coppia `Z_q ⊗ Z_q` a un'istanza con testimone. -/
lemma witness_step {f : ι → Factor} {i i' : ι} (hii : i ≠ i') {b n : ℕ} (hq : 2 ^ b = n + 2)
    (hfi : f i = Z b) (hfi' : f i' = Z b)
    (hW : Witness (triv f {i, i'}) (uE F ι)) : Witness f (uE F ι) := by
  obtain ⟨k, hk1, hk2⟩ := hW
  have m1 := map_sig_I f {i, i'} hk1
  rw [map_mul, sig_uE] at m1
  have m2 := map_sig_I f {i, i'} hk2
  rw [map_sub, map_mul, sig_cc, sig_top] at m2
  rw [← Ideal.Quotient.eq_zero_iff_mem] at m1 m2
  have h2 : (2 : MvPolynomial ι F ⧸ I F f) = 0 := two_eq_zero_alg (F := F) _
  have hs : (Z b).s = 2 * n + 3 := by simp only [Factor.s]; omega
  have hj : (Z b).j = n + 1 := by simp only [Factor.j]; omega
  have hs1 : (Z b).s - 1 = 2 * n + 2 := by omega
  have hy : (Ideal.Quotient.mk (I F f) (X i)) ^ (2 * n + 3) = 0 := by
    rw [← map_pow]; exact mk_X_pow f i (by rw [hfi, hs])
  have hz : (Ideal.Quotient.mk (I F f) (X i')) ^ (2 * n + 3) = 0 := by
    rw [← map_pow]; exact mk_X_pow f i' (by rw [hfi', hs])
  obtain ⟨-, hwe, -, hP4⟩ := coppia h2 _ _ n b hq hy hz
  refine ⟨sig F {i, i'} k * hh (X i) (X i') (2 * n + 2), ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, uE_split {i, i'}, sum_pair hii]
    simp only [map_mul, map_add, map_hh] at m1 ⊢
    linear_combination (hh (Ideal.Quotient.mk (I F f) (X i))
      (Ideal.Quotient.mk (I F f) (X i')) (2 * n + 2)) * m1
      + (Ideal.Quotient.mk (I F f) (sig F {i, i'} k)) * hwe
  · rw [← Ideal.Quotient.eq_zero_iff_mem, cc_split f {i, i'}, top_split f {i, i'},
      prod_pair hii, prod_pair hii, hfi, hfi', hj, hs1]
    simp only [map_mul, map_sub, map_pow, map_hh] at m2 ⊢
    linear_combination
      ((Ideal.Quotient.mk (I F f) (X i) * Ideal.Quotient.mk (I F f) (X i')) ^ (n + 1)
        * hh (Ideal.Quotient.mk (I F f) (X i)) (Ideal.Quotient.mk (I F f) (X i')) (2 * n + 2))
        * m2
      + Ideal.Quotient.mk (I F f) (top F (triv f {i, i'})) * hP4

/-- **Parte "non raggiungibile" del teorema locale (edge).** -/
theorem witness_of_not_cond (f : ι → Factor) (h : ¬ Cond f) : Witness f (uE F ι) := by
  suffices H : ∀ m : ℕ, ∀ f : ι → Factor,
      (univ.filter (fun i => f i ≠ Z 0)).card ≤ m → ¬ Cond f → Witness f (uE F ι) from
    H _ f le_rfl h
  intro m
  induction m with
  | zero =>
    intro f hm _
    apply witness_trivial
    intro i
    by_contra hi
    have hmem : i ∈ univ.filter (fun i => f i ≠ Z 0) := by simp [hi]
    have := card_pos.2 ⟨i, hmem⟩
    omega
  | succ m ih =>
    intro f hm hc
    by_cases hall : ∀ i, f i = Z 0
    · exact witness_trivial f hall
    push_neg at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨b, hb, hfi⟩ : ∃ b, 1 ≤ b ∧ f i = Z b := by
      cases hfi : f i with
      | Z b =>
        refine ⟨b, ?_, rfl⟩
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · subst h0; exact absurd hfi hi
        · exact h0
      | N a => exact absurd ⟨a + 1, by omega, Or.inl ⟨i, by simp [hfi]⟩⟩ hc
    have h2b : 2 ≤ 2 ^ b := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    have hq : 2 ^ b = (2 ^ b - 2) + 2 := by omega
    have hiS : i ∈ univ.filter (fun l => f l = Z b) := by simp [hfi]
    have hev : ¬ Odd (univ.filter (fun l => f l = Z b)).card :=
      fun ho => hc ⟨b, hb, Or.inr ho⟩
    have hcard2 : 2 ≤ (univ.filter (fun l => f l = Z b)).card := by
      have h1 : 0 < (univ.filter (fun l => f l = Z b)).card := card_pos.2 ⟨i, hiS⟩
      rcases Nat.even_or_odd (univ.filter (fun l => f l = Z b)).card with he | ho
      · obtain ⟨r, hr⟩ := he; omega
      · exact absurd ho hev
    obtain ⟨i', hi'⟩ : ((univ.filter (fun l => f l = Z b)).erase i).Nonempty := by
      rw [← card_pos, card_erase_of_mem hiS]; omega
    have hii : i ≠ i' := fun h => by simp [h] at hi'
    have hfi' : f i' = Z b := by simpa using mem_of_mem_erase hi'
    have hgm : (univ.filter (fun l => triv f {i, i'} l ≠ Z 0)).card ≤ m := by
      have hsub : univ.filter (fun l => triv f {i, i'} l ≠ Z 0) ⊆
          (univ.filter (fun l => f l ≠ Z 0)).erase i := by
        intro l hl
        simp only [triv, mem_filter, mem_univ, true_and, mem_erase, mem_insert,
          mem_singleton] at hl ⊢
        by_cases h1 : l = i ∨ l = i'
        · simp [h1] at hl
        · push_neg at h1
          simp only [h1, or_self, if_false] at hl
          exact ⟨h1.1, hl⟩
      have hle := card_le_card hsub
      have hmem : i ∈ univ.filter (fun l => f l ≠ Z 0) := by simp [hi]
      rw [card_erase_of_mem hmem] at hle
      omega
    have hgc : ¬ Cond (triv f {i, i'}) := by
      rintro ⟨ℓ, hℓ, hgood⟩
      apply hc
      refine ⟨ℓ, hℓ, ?_⟩
      rcases hgood with ⟨l, hl⟩ | ho
      · left
        refine ⟨l, ?_⟩
        simp only [triv] at hl
        split_ifs at hl
        exact hl
      · right
        by_cases hℓb : ℓ = b
        · rw [hℓb] at ho
          have heq : univ.filter (fun l => triv f {i, i'} l = Z b) =
              ((univ.filter (fun l => f l = Z b)).erase i).erase i' := by
            ext l
            simp only [mem_filter, mem_univ, true_and, mem_erase, mem_insert, mem_singleton]
            simp only [triv, mem_insert, mem_singleton]
            by_cases h1 : l = i <;> by_cases h2 : l = i' <;> simp [h1, h2] <;> omega
          rw [heq, card_erase_of_mem hi', card_erase_of_mem hiS] at ho
          rw [hℓb, Nat.odd_iff]
          rw [Nat.odd_iff] at ho
          omega
        · have heq : univ.filter (fun l => triv f {i, i'} l = Z ℓ) =
              univ.filter (fun l => f l = Z ℓ) := by
            ext l
            simp only [mem_filter, mem_univ, true_and]
            simp only [triv]
            split_ifs with h1
            · have hfl : f l = Z b := by
                rcases mem_insert.1 h1 with rfl | h
                · exact hfi
                · rw [mem_singleton.1 h]; exact hfi'
              rw [hfl]
              simp only [Factor.Z.injEq]
              omega
            · rfl
          rwa [heq] at ho
    exact witness_step hii hq hfi hfi' (ih _ hgm hgc)

end SigmaMeno.Locale
