import Mathlib

/-!
# Algebra di base per il problema locale

Lemmi astratti in un anello commutativo `A` dove `2 = 0`:
* Frobenius: `(a + b) ^ (2 ^ n) = a ^ (2 ^ n) + b ^ (2 ^ n)` e lo stesso per le somme finite;
* i polinomi omogenei completi `hh y z k = ∑_{a ≤ k} y^a z^(k-a)` e l'identità della coppia;
* **Lemma B (una coppia, vicinato edge)** e **Lemma C (coppie uguali)** della nota.

Convenzione: `q = n + 2 = 2 ^ b` con `b ≥ 1`, così `q - 1 = n + 1`, `2q - 1 = 2n + 3`, `2q - 2 = 2n + 2`
e `q - 2 = n` senza sottrazioni tra naturali.
-/

namespace SigmaMeno.Locale

open Finset

section Frobenius

variable {A : Type*} [CommRing A]

lemma frob_add (h2 : (2 : A) = 0) (a b : A) (n : ℕ) :
    (a + b) ^ (2 ^ n) = a ^ (2 ^ n) + b ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih]
    linear_combination (a ^ 2 ^ n * b ^ 2 ^ n) * h2

lemma frob_sum (h2 : (2 : A) = 0) {κ : Type*} [DecidableEq κ] (s : Finset κ) (g : κ → A)
    (n : ℕ) : (∑ i ∈ s, g i) ^ (2 ^ n) = ∑ i ∈ s, g i ^ (2 ^ n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, frob_add h2, ih]

end Frobenius

section Omogenei

/-- Il polinomio omogeneo completo di grado `k` in due elementi. -/
def hh {A : Type*} [CommRing A] (y z : A) (k : ℕ) : A :=
  ∑ a ∈ range (k + 1), y ^ a * z ^ (k - a)

lemma hh_mul {A : Type*} [CommRing A] (y z : A) (k : ℕ) :
    hh y z k * (y - z) = y ^ (k + 1) - z ^ (k + 1) := by
  have := (Commute.all y z).geom_sum₂_mul (k + 1)
  simpa [hh] using this

lemma map_hh {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (y z : A) (k : ℕ) :
    φ (hh y z k) = hh (φ y) (φ z) k := by
  simp [hh, map_sum, map_mul, map_pow]

/-- L'identità della coppia, prima in un dominio con `y ≠ z`. -/
lemma hh_ident_dom {A : Type*} [CommRing A] [IsDomain A] (y z : A) (hyz : y ≠ z) (n : ℕ) :
    hh y z (2 * n + 2) = (y * z) ^ (n + 1) + (y ^ (n + 2) + z ^ (n + 2)) * hh y z n := by
  have hne : y - z ≠ 0 := sub_ne_zero.2 hyz
  apply mul_right_cancel₀ hne
  have e1 := hh_mul y z (2 * n + 2)
  have e2 := hh_mul y z n
  linear_combination e1 - (y ^ (n + 2) + z ^ (n + 2)) * e2

/-- L'identità della coppia in ogni anello commutativo (si ottiene da `ℤ[a, b]`). -/
lemma hh_ident {A : Type*} [CommRing A] (y z : A) (n : ℕ) :
    hh y z (2 * n + 2) = (y * z) ^ (n + 1) + (y ^ (n + 2) + z ^ (n + 2)) * hh y z n := by
  have h := hh_ident_dom (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) (MvPolynomial.X 1)
    (fun h => by simpa using MvPolynomial.X_injective h) n
  have h' := congrArg (MvPolynomial.aeval (R := ℤ) ![y, z]).toRingHom h
  simpa [map_hh, map_add, map_mul, map_pow] using h'

end Omogenei

section Coppia

variable {A : Type*} [CommRing A] (h2 : (2 : A) = 0)

include h2 in
/-- **Lemma B, vicinato edge.** Per una coppia `Z_q ⊗ Z_q` (`q = n + 2 = 2^b`), con `y^(2q-1) = 0`
e `z^(2q-1) = 0`, e con `e = hh y z (2q-2)`, `G = hh y z (q-2)`, `w = y + z`:
`c = e + w^q G`, `w e = 0`, `w^(2q) = 0`, e `c · e = (y z)^(2q-2)` (il monomio di vertice). -/
lemma coppia (y z : A) (n b : ℕ) (hq : 2 ^ b = n + 2)
    (hy : y ^ (2 * n + 3) = 0) (hz : z ^ (2 * n + 3) = 0) :
    (y * z) ^ (n + 1) = hh y z (2 * n + 2) + (y + z) ^ (n + 2) * hh y z n ∧
    (y + z) * hh y z (2 * n + 2) = 0 ∧
    (y + z) ^ (2 * n + 4) = 0 ∧
    (y * z) ^ (n + 1) * hh y z (2 * n + 2) = (y * z) ^ (2 * n + 2) := by
  have hfrob : (y + z) ^ (n + 2) = y ^ (n + 2) + z ^ (n + 2) := by
    rw [← hq]; exact frob_add h2 y z b
  have ident := hh_ident y z n
  have hmul := hh_mul y z (2 * n + 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-1 : A) * ident - hh y z n * hfrob
      - (y ^ (n + 2) + z ^ (n + 2)) * hh y z n * h2
  · linear_combination hmul + hy - hz + z * hh y z (2 * n + 2) * h2
  · linear_combination ((y + z) ^ (n + 2) + y ^ (n + 2) + z ^ (n + 2)) * hfrob
      + y * hy + z * hz + y ^ (n + 2) * z ^ (n + 2) * h2
  · linear_combination (y * z) ^ (n + 1) * ident + z ^ (n + 1) * hh y z n * hy
      + y ^ (n + 1) * hh y z n * hz

include h2 in
/-- **Lemma C (coppie uguali).** Se `S` ha un numero pari di elementi, tutti con
`x ^ (2q - 1) = 0`, allora `∏ x^(q-1) = e + u^q X` con `u e = 0`, dove `u = ∑ x`. -/
lemma lemmaC {κ : Type*} [DecidableEq κ] (x : κ → A) (n b : ℕ) (hq : 2 ^ b = n + 2)
    (S : Finset κ) (hS : Even S.card) (hx : ∀ l ∈ S, x l ^ (2 * n + 3) = 0) :
    ∃ e X : A, ∏ l ∈ S, x l ^ (n + 1) = e + (∑ l ∈ S, x l) ^ (n + 2) * X ∧
      (∑ l ∈ S, x l) * e = 0 := by
  obtain ⟨m, hm⟩ := hS
  induction m generalizing S with
  | zero =>
    have : S = ∅ := card_eq_zero.1 (by omega)
    subst this
    exact ⟨1, 0, by simp, by simp⟩
  | succ m ih =>
    have hpos : 0 < S.card := by omega
    obtain ⟨i, hi⟩ := card_pos.1 hpos
    have h1 : (S.erase i).card = 2 * m + 1 := by rw [card_erase_of_mem hi]; omega
    obtain ⟨i', hi'⟩ := card_pos.1 (by omega : 0 < (S.erase i).card)
    set S2 := (S.erase i).erase i' with hS2
    have h2c : S2.card = m + m := by rw [hS2, card_erase_of_mem hi']; omega
    have hx2 : ∀ l ∈ S2, x l ^ (2 * n + 3) = 0 := fun l hl =>
      hx l (mem_of_mem_erase (mem_of_mem_erase hl))
    obtain ⟨e', X', hc', hue⟩ := ih S2 hx2 h2c
    have hi'S : i' ∈ S := mem_of_mem_erase hi'
    obtain ⟨hP, hwe, hw2, -⟩ := coppia h2 (x i) (x i') n b hq (hx i hi) (hx i' hi'S)
    set y := x i
    set z := x i'
    set u' := ∑ l ∈ S2, x l
    set G := hh y z n
    set eP := hh y z (2 * n + 2)
    have hprod : ∏ l ∈ S, x l ^ (n + 1) = (y * z) ^ (n + 1) * ∏ l ∈ S2, x l ^ (n + 1) := by
      rw [← mul_prod_erase S _ hi, ← mul_prod_erase (S.erase i) _ hi', mul_pow]; ring
    have hsum : ∑ l ∈ S, x l = u' + (y + z) := by
      rw [← add_sum_erase S _ hi, ← add_sum_erase (S.erase i) _ hi']; ring
    have hfrob : (u' + (y + z)) ^ (n + 2) = u' ^ (n + 2) + (y + z) ^ (n + 2) := by
      rw [← hq]; exact frob_add h2 u' (y + z) b
    refine ⟨e' * eP, e' * G + X' * eP + X' * (y + z) ^ (n + 2) * G, ?_, ?_⟩
    · rw [hprod, hsum]
      linear_combination (e' + u' ^ (n + 2) * X') * hP + ((y * z) ^ (n + 1)) * hc'
        - (e' * G + X' * eP + X' * (y + z) ^ (n + 2) * G) * hfrob
        - u' ^ (n + 1) * G * hue - (y + z) ^ (n + 1) * X' * hwe - X' * G * hw2
    · rw [hsum]
      linear_combination eP * hue + e' * hwe

end Coppia

end SigmaMeno.Locale
