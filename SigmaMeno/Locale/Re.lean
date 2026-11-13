import SigmaMeno.Locale.Raggiungibile

/-!
# Il problema locale per il vicinato king

Per il vicinato king `u = ∏ (1 + X_i) - 1`. Con la sostituzione `ψ : X_l ↦ X_l · U_l`, dove ogni
`U_l` è un prodotto di fattori `(1 + X_m)` scelto in modo che `∑ X_l U_l = ∏ (1 + X_l) - 1`
(telescopio), l'operatore edge `∑ X_l` va esattamente nell'operatore king. Ogni `(1 + X_m)` è
invertibile nell'anello locale, quindi `c` cambia solo per un'unità e il monomio di vertice non
cambia. Per questo il teorema locale king segue da quello edge.

Questa via è diversa da quella della nota (che rifà i Lemmi B-F per king con l'algebra di gruppo):
il teorema è lo stesso, la prova è più corta.
-/

namespace SigmaMeno.Locale

open MvPolynomial Finset Factor

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Il telescopio: `∑_{l ∈ S} X_l ∏_{m ∈ T l} (1 + X_m) = ∏_{l ∈ S} (1 + X_l) - 1`. -/
lemma telescope (S : Finset ι) : ∃ T : ι → Finset ι,
    ∑ l ∈ S, (X l : MvPolynomial ι F) * ∏ m ∈ T l, (1 + X m) = ∏ l ∈ S, (1 + X l) - 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅, by simp⟩
  | insert a S ha ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨fun l => if l = a then S else T l, ?_⟩
    rw [sum_insert ha, prod_insert ha]
    beta_reduce
    rw [if_pos rfl]
    have : ∑ l ∈ S, (X l : MvPolynomial ι F) * ∏ m ∈ (if l = a then S else T l), (1 + X m) =
        ∑ l ∈ S, X l * ∏ m ∈ T l, (1 + X m) :=
      sum_congr rfl fun l hl => by
        have hla : l ≠ a := fun h => ha (h ▸ hl)
        rw [if_neg hla]
    rw [this, hT]
    ring

/-- Il sottomonoide generato dagli elementi `1 + X_m`. -/
noncomputable def UnoPiu (F : Type*) [Field F] (ι : Type*) : Submonoid (MvPolynomial ι F) :=
  Submonoid.closure (Set.range fun m => (1 + X m : MvPolynomial ι F))

omit [Fintype ι] [DecidableEq ι] in
lemma prod_mem_UnoPiu (T : Finset ι) : (∏ m ∈ T, (1 + X m) : MvPolynomial ι F) ∈ UnoPiu F ι :=
  Submonoid.prod_mem _ fun m _ => Submonoid.subset_closure ⟨m, rfl⟩

/-- Gli elementi di `UnoPiu` sono invertibili nell'anello locale. -/
lemma isUnit_mk (f : ι → Factor) {W : MvPolynomial ι F} (hW : W ∈ UnoPiu F ι) :
    IsUnit (Ideal.Quotient.mk (I F f) W) := by
  induction hW using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    rw [map_add, map_one]
    exact IsNilpotent.isUnit_one_add ⟨(f m).s, by rw [← map_pow]; exact mk_X_pow f m le_rfl⟩
  | one => rw [map_one]; exact isUnit_one
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

/-- Moltiplicare il monomio di vertice per un elemento di `UnoPiu` non lo cambia (modulo `I`). -/
lemma top_mul_mem (f : ι → Factor) {W : MvPolynomial ι F} (hW : W ∈ UnoPiu F ι) :
    top F f * W - top F f ∈ I F f := by
  induction hW using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    have e : top F f * (1 + X m) - top F f =
        X m ^ ((f m).s - 1 + 1) * ∏ l ∈ univ.erase m, X l ^ ((f l).s - 1) := by
      rw [top, ← mul_prod_erase univ _ (mem_univ m)]
      ring
    rw [e]
    exact Ideal.mul_mem_right _ _ (X_pow_mem_of_le f m (by omega))
  | one => simp
  | mul x y _ _ hx hy =>
    have e : top F f * (x * y) - top F f = (top F f * x - top F f) * y + (top F f * y - top F f) := by
      ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hx) hy

/-- La sostituzione `X_l ↦ X_l · ∏_{m ∈ T l} (1 + X_m)`. -/
noncomputable def psi (T : ι → Finset ι) : MvPolynomial ι F →ₐ[F] MvPolynomial ι F :=
  aeval fun l => X l * ∏ m ∈ T l, (1 + X m)

lemma psi_mem (f : ι → Factor) (T : ι → Finset ι) {p : MvPolynomial ι F} (hp : p ∈ I F f) :
    psi T p ∈ I F f := by
  have : I F f ≤ Ideal.comap (psi T) (I F f) := by
    unfold I
    rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, psi, aeval_X, mul_pow]
    exact Ideal.mul_mem_right _ _ (X_pow_mem f l)
  exact this hp

lemma psi_cc (f : ι → Factor) (T : ι → Finset ι) :
    psi T (cc F f) = cc F f * ∏ l, (∏ m ∈ T l, (1 + X m)) ^ (f l).j := by
  simp only [cc, map_prod, map_pow, psi, aeval_X, mul_pow, prod_mul_distrib]

lemma psi_top (f : ι → Factor) (T : ι → Finset ι) :
    psi T (top F f) = top F f * ∏ l, (∏ m ∈ T l, (1 + X m)) ^ ((f l).s - 1) := by
  simp only [top, map_prod, map_pow, psi, aeval_X, mul_pow, prod_mul_distrib]

lemma prodpow_mem (T : ι → Finset ι) (e : ι → ℕ) :
    (∏ l, (∏ m ∈ T l, (1 + X m)) ^ e l : MvPolynomial ι F) ∈ UnoPiu F ι :=
  Submonoid.prod_mem _ fun l _ => Submonoid.pow_mem _ (prod_mem_UnoPiu _) _

/-- Raggiungibile per edge ⇒ raggiungibile per king. -/
lemma reach_king_of_edge (f : ι → Factor) (h : Reach f (uE F ι)) : Reach f (uK F ι) := by
  obtain ⟨T, hT⟩ := telescope (F := F) (univ : Finset ι)
  obtain ⟨y, hy⟩ := h
  have hψ := psi_mem f T hy
  have hu : psi T (uE F ι) = uK F ι := by
    rw [uE, uK, map_sum, ← hT]
    simp [psi]
  rw [map_sub, map_mul, psi_cc, hu, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul,
    map_mul, sub_eq_zero] at hψ
  obtain ⟨v, hv⟩ := isUnit_mk f (prodpow_mem (F := F) T fun l => (f l).j)
  rw [reach_iff_mk]
  refine ⟨Ideal.Quotient.mk (I F f) (psi T y) * ↑v⁻¹, ?_⟩
  calc Ideal.Quotient.mk (I F f) (cc F f)
      = Ideal.Quotient.mk (I F f) (cc F f) * (↑v * ↑v⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = (Ideal.Quotient.mk (I F f) (cc F f) * ↑v) * ↑v⁻¹ := by ring
    _ = _ := by rw [hv, hψ]; ring

/-- Un testimone per edge dà un testimone per king. -/
lemma witness_king_of_edge (f : ι → Factor) (h : Witness f (uE F ι)) : Witness f (uK F ι) := by
  obtain ⟨T, hT⟩ := telescope (F := F) (univ : Finset ι)
  obtain ⟨k, hk1, hk2⟩ := h
  have hu : psi T (uE F ι) = uK F ι := by
    rw [uE, uK, map_sum, ← hT]
    simp [psi]
  refine ⟨(∏ l, (∏ m ∈ T l, (1 + X m)) ^ (f l).j) * psi T k, ?_, ?_⟩
  · have := psi_mem f T hk1
    rw [map_mul, hu] at this
    have e : uK F ι * ((∏ l, (∏ m ∈ T l, (1 + X m)) ^ (f l).j) * psi T k) =
        (∏ l, (∏ m ∈ T l, (1 + X m)) ^ (f l).j) * (uK F ι * psi T k) := by ring
    rw [e]
    exact Ideal.mul_mem_left _ _ this
  · have h1 := psi_mem f T hk2
    rw [map_sub, map_mul, psi_cc, psi_top] at h1
    have h2 := top_mul_mem f (prodpow_mem (F := F) T fun l => (f l).s - 1)
    have e : cc F f * ((∏ l, (∏ m ∈ T l, (1 + X m)) ^ (f l).j) * psi T k) - top F f =
        (cc F f * (∏ l, (∏ m ∈ T l, (1 + X m)) ^ (f l).j) * psi T k
          - top F f * ∏ l, (∏ m ∈ T l, (1 + X m)) ^ ((f l).s - 1))
        + (top F f * (∏ l, (∏ m ∈ T l, (1 + X m)) ^ ((f l).s - 1)) - top F f) := by ring
    rw [e]
    exact add_mem h1 h2

/-- **Il teorema locale, vicinato king.** -/
theorem local_theorem_king [CharP F 2] (f : ι → Factor) : Reach f (uK F ι) ↔ Cond f := by
  constructor
  · intro hr
    by_contra hc
    exact not_reach_of_witness (witness_king_of_edge f (witness_of_not_cond f hc)) hr
  · intro hc
    exact reach_king_of_edge f (reach_of_cond f hc)

end SigmaMeno.Locale
