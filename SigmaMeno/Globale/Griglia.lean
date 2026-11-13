import SigmaMeno.Cammino
import SigmaMeno.Locale.Re
import SigmaMeno.Globale.Molteplicita

/-!
# La griglia come anello di polinomi

`Φ(w) = ∑_ξ w(ξ) ∏_i Q_{ξ_i}(X_i)` manda le configurazioni della griglia in
`F[X_1..X_d] / (Q_{n_i}(X_i))`. Premere (vicinato edge) diventa la moltiplicazione per `∑ X_i`;
premere (vicinato king) diventa la moltiplicazione per `∏ (1 + X_i) - 1`; "tutte accese" va in
`∏ f_{n_i}(X_i)`.
-/

namespace SigmaMeno.Globale

open MvPolynomial Finset

/-- `press` per valori in un campo qualsiasi (per `ZMod 2` coincide con `SigmaMeno.press`). -/
def pressF {F : Type*} [Field F] {V : Type*} [Fintype V] (adj : V → V → Prop) [DecidableRel adj]
    (w : V → F) : V → F :=
  fun ξ => ∑ η ∈ univ.filter (fun η => adj ξ η), w η

section Cammino

variable {R : Type*} [CommRing R]

/-- Somma sulle vicine nel cammino `0..N-1`, per una successione con la ricorrenza di `Q`. -/
lemma path_rec (h2 : (2 : R) = 0) (x : R) (q : ℕ → R) (h0 : q 0 = 1) (h1 : q 1 = x)
    (hss : ∀ m, q (m + 2) = x * q (m + 1) + q m) (N k : ℕ) (hk : k < N) :
    ∑ s ∈ range N, (if (((k : ℤ) - (s : ℤ)).natAbs = 1) then q s else 0) =
      x * q k + (if k + 1 = N then q N else 0) := by
  have hpt : ∀ s : ℕ, (if (((k : ℤ) - (s : ℤ)).natAbs = 1) then q s else 0) =
      (if s = k + 1 then q s else 0) + (if 0 < k then (if s = k - 1 then q s else 0) else 0) := by
    intro s
    simp only [SigmaMeno.natAbs_sub_eq_one_iff]
    split_ifs <;> first | omega | simp
  rw [sum_congr rfl (fun s _ => hpt s), sum_add_distrib, sum_ite_eq' (range N) (k + 1) q]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [lt_irrefl, if_false, sum_const_zero, add_zero, mem_range, h1, h0, mul_one, zero_add]
    by_cases hN : 1 < N
    · rw [if_pos hN, if_neg (by omega), add_zero]
    · have : N = 1 := by omega
      subst this
      rw [if_neg (lt_irrefl 1), if_pos rfl, h1]
      linear_combination (-x) * h2
  · simp only [if_pos hk0]
    rw [sum_ite_eq' (range N) (k - 1) q]
    simp only [mem_range]
    rw [if_pos (by omega : k - 1 < N)]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk2 := hss k'
    rw [Nat.add_sub_cancel]
    by_cases hN : k' + 1 + 1 < N
    · rw [if_pos hN, if_neg (by omega), show k' + 1 + 1 = k' + 2 from rfl, hk2]
      linear_combination q k' * h2
    · have hN' : k' + 1 + 1 = N := by omega
      rw [if_neg hN, if_pos hN', ← hN', show k' + 1 + 1 = k' + 2 from rfl, hk2]
      linear_combination (-(x * q (k' + 1))) * h2

/-- Somma sul vicinato chiuso nel cammino. -/
lemma path_rec_closed (h2 : (2 : R) = 0) (x : R) (q : ℕ → R) (h0 : q 0 = 1) (h1 : q 1 = x)
    (hss : ∀ m, q (m + 2) = x * q (m + 1) + q m) (N k : ℕ) (hk : k < N) :
    ∑ s ∈ range N, (if (((k : ℤ) - (s : ℤ)).natAbs ≤ 1) then q s else 0) =
      (1 + x) * q k + (if k + 1 = N then q N else 0) := by
  have hpt : ∀ s : ℕ, (if (((k : ℤ) - (s : ℤ)).natAbs ≤ 1) then q s else 0) =
      (if s = k then q s else 0) + (if (((k : ℤ) - (s : ℤ)).natAbs = 1) then q s else 0) := by
    intro s
    simp only [SigmaMeno.natAbs_sub_eq_one_iff, SigmaMeno.natAbs_sub_le_one_iff]
    split_ifs <;> first | omega | simp
  rw [sum_congr rfl (fun s _ => hpt s), sum_add_distrib, sum_ite_eq' (range N) k q,
    path_rec h2 x q h0 h1 hss N k hk]
  simp only [mem_range, if_pos hk]
  ring

end Cammino

variable {F : Type*} [Field F] {d : ℕ} {n : Fin d → ℕ}

/-- `Q_k(X_i)`. -/
noncomputable def qq (F : Type*) [Field F] {d : ℕ} (i : Fin d) (k : ℕ) : MvPolynomial (Fin d) F :=
  Polynomial.aeval (X i : MvPolynomial (Fin d) F) (Q F k)

lemma qq_zero (i : Fin d) : qq F i 0 = 1 := by simp [qq]
lemma qq_one (i : Fin d) : qq F i 1 = X i := by simp [qq]
lemma qq_ss (i : Fin d) (m : ℕ) : qq F i (m + 2) = X i * qq F i (m + 1) + qq F i m := by
  simp [qq, Q_ss]

/-- L'ideale `(Q_{n_i}(X_i))`. -/
noncomputable def Jid (F : Type*) [Field F] {d : ℕ} (n : Fin d → ℕ) : Ideal (MvPolynomial (Fin d) F) :=
  Ideal.span (Set.range fun i => qq F i (n i))

/-- Il polinomio della cella `ξ`. -/
noncomputable def Pc (F : Type*) [Field F] {d : ℕ} {n : Fin d → ℕ} (ξ : SigmaMeno.Cell n) :
    MvPolynomial (Fin d) F :=
  ∏ i, qq F i (ξ i : ℕ)

/-- La mappa `Φ`. -/
noncomputable def Phi (F : Type*) [Field F] {d : ℕ} {n : Fin d → ℕ}
    (w : SigmaMeno.Cell n → F) : MvPolynomial (Fin d) F :=
  ∑ ξ, C (w ξ) * Pc F ξ

lemma mk_qq_n (i : Fin d) : Ideal.Quotient.mk (Jid F n) (qq F i (n i)) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)

lemma Pc_eq (ξ : SigmaMeno.Cell n) (i : Fin d) :
    Pc F ξ = qq F i (ξ i : ℕ) * ∏ j ∈ univ.erase i, qq F j (ξ j : ℕ) :=
  (mul_prod_erase univ _ (mem_univ i)).symm

lemma Pc_update (ξ : SigmaMeno.Cell n) (i : Fin d) (k : Fin (n i)) :
    Pc F (Function.update ξ i k) = qq F i (k : ℕ) * ∏ j ∈ univ.erase i, qq F j (ξ j : ℕ) := by
  rw [Pc, ← mul_prod_erase univ _ (mem_univ i), Function.update_self]
  congr 1
  exact prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]

section CarDue

variable [CharP F 2]

lemma line_sum (ξ : SigmaMeno.Cell n) (i : Fin d) :
    ∑ k ∈ univ.filter (fun k : Fin (n i) => (((ξ i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs = 1),
      qq F i (k : ℕ) = X i * qq F i (ξ i : ℕ) + (if (ξ i : ℕ) + 1 = n i then qq F i (n i) else 0) := by
  rw [sum_filter, Fin.sum_univ_eq_sum_range
    (fun s => if (((ξ i : ℕ) : ℤ) - (s : ℤ)).natAbs = 1 then qq F i s else 0) (n i)]
  exact path_rec (SigmaMeno.Locale.two_eq_zero_alg (F := F) _) (X i) (qq F i) (qq_zero i)
    (qq_one i) (qq_ss i) (n i) (ξ i) (ξ i).isLt

lemma closed_sum (ξ : SigmaMeno.Cell n) (i : Fin d) :
    ∑ k ∈ univ.filter (fun k : Fin (n i) => (((ξ i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs ≤ 1),
      qq F i (k : ℕ) =
        (1 + X i) * qq F i (ξ i : ℕ) + (if (ξ i : ℕ) + 1 = n i then qq F i (n i) else 0) := by
  rw [sum_filter, Fin.sum_univ_eq_sum_range
    (fun s => if (((ξ i : ℕ) : ℤ) - (s : ℤ)).natAbs ≤ 1 then qq F i s else 0) (n i)]
  exact path_rec_closed (SigmaMeno.Locale.two_eq_zero_alg (F := F) _) (X i) (qq F i) (qq_zero i)
    (qq_one i) (qq_ss i) (n i) (ξ i) (ξ i).isLt

/-- Le vicine edge di `ξ` sono le `update ξ i k` con `|ξ_i - k| = 1`. -/
lemma edge_sum (ξ : SigmaMeno.Cell n) :
    ∑ η ∈ univ.filter (fun η => SigmaMeno.EdgeAdj ξ η), Pc F η =
      ∑ i, ∑ k ∈ univ.filter (fun k : Fin (n i) => (((ξ i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs = 1),
        Pc F (Function.update ξ i k) := by
  rw [Finset.sum_sigma']
  symm
  refine sum_bij (fun p _ => Function.update ξ p.1 p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨i, k⟩ hp
    simp only [mem_sigma, mem_univ, mem_filter, true_and] at hp ⊢
    refine ⟨i, by rw [Function.update_self]; exact hp, fun j hj => ?_⟩
    rw [Function.update_of_ne hj]
  · rintro ⟨i, k⟩ hp ⟨i', k'⟩ hp' h
    dsimp only at h
    simp only [mem_sigma, mem_univ, mem_filter, true_and] at hp hp'
    by_cases hii : i = i'
    · subst hii
      have := congrFun h i
      simp only [Function.update_self] at this
      rw [this]
    · exfalso
      have := congrFun h i
      rw [Function.update_self, Function.update_of_ne hii] at this
      rw [this] at hp
      simp at hp
  · intro η hη
    simp only [mem_filter, mem_univ, true_and] at hη
    obtain ⟨i, hi, hj⟩ := hη
    refine ⟨⟨i, η i⟩, by simp [hi], ?_⟩
    funext j
    by_cases hji : j = i
    · subst hji; simp
    · rw [Function.update_of_ne hji]; exact hj j hji

/-- **Edge, una cella:** la somma sulle vicine è `(∑ X_i) · P(ξ)` modulo l'ideale. -/
lemma edge_cell (ξ : SigmaMeno.Cell n) :
    Ideal.Quotient.mk (Jid F n) (∑ η ∈ univ.filter (fun η => SigmaMeno.EdgeAdj ξ η), Pc F η) =
      Ideal.Quotient.mk (Jid F n) (∑ i, X i) * Ideal.Quotient.mk (Jid F n) (Pc F ξ) := by
  rw [edge_sum]
  simp_rw [Pc_update, ← sum_mul, line_sum]
  rw [map_sum, map_sum, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [Pc_eq ξ i]
  split_ifs <;> simp [map_add, map_mul, mk_qq_n] <;> ring

/-- Le vicine king di `ξ` sono il box meno `ξ`. -/
lemma king_filter (ξ : SigmaMeno.Cell n) :
    univ.filter (fun η => SigmaMeno.KingAdj ξ η) =
      (Fintype.piFinset fun i => univ.filter
        (fun k : Fin (n i) => (((ξ i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs ≤ 1)).erase ξ := by
  ext η
  simp only [mem_filter, mem_univ, true_and, mem_erase, Fintype.mem_piFinset]
  simp only [SigmaMeno.KingAdj]
  constructor
  · rintro ⟨hne, h⟩; exact ⟨Ne.symm hne, h⟩
  · rintro ⟨hne, h⟩; exact ⟨Ne.symm hne, h⟩

/-- **King, una cella:** la somma sulle vicine è `(∏ (1 + X_i) - 1) · P(ξ)` modulo l'ideale. -/
lemma king_cell (ξ : SigmaMeno.Cell n) :
    Ideal.Quotient.mk (Jid F n) (∑ η ∈ univ.filter (fun η => SigmaMeno.KingAdj ξ η), Pc F η) =
      Ideal.Quotient.mk (Jid F n) (∏ i, (1 + X i) - 1) *
        Ideal.Quotient.mk (Jid F n) (Pc F ξ) := by
  have hmem : ξ ∈ Fintype.piFinset fun i => univ.filter
      (fun k : Fin (n i) => (((ξ i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs ≤ 1) := by
    simp [Fintype.mem_piFinset]
  rw [king_filter, sum_erase_eq_sub hmem]
  unfold Pc
  rw [← prod_univ_sum (fun i => univ.filter
      (fun k : Fin (n i) => (((ξ i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs ≤ 1))
    (fun i (k : Fin (n i)) => qq F i (k : ℕ))]
  simp_rw [closed_sum]
  rw [map_sub, map_prod, map_sub, map_prod, map_one, map_prod, sub_mul, one_mul, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  split_ifs <;> simp [map_add, map_mul, mk_qq_n]

lemma edgeAdj_symm' (ξ η : SigmaMeno.Cell n) :
    SigmaMeno.EdgeAdj ξ η → SigmaMeno.EdgeAdj η ξ := SigmaMeno.edgeAdj_symm ξ η

lemma kingAdj_symm (ξ η : SigmaMeno.Cell n) :
    SigmaMeno.KingAdj ξ η → SigmaMeno.KingAdj η ξ := by
  rintro ⟨hne, h⟩
  refine ⟨Ne.symm hne, fun i => ?_⟩
  have := h i
  rw [SigmaMeno.natAbs_sub_le_one_iff] at this ⊢
  omega

end CarDue

/-- Premere e poi applicare `Φ`: lo scambio delle somme (serve la simmetria). -/
lemma Phi_press (adj : SigmaMeno.Cell n → SigmaMeno.Cell n → Prop) [DecidableRel adj]
    (hsymm : ∀ ξ η, adj ξ η → adj η ξ) (w : SigmaMeno.Cell n → F) :
    Phi F (pressF adj w) = ∑ ξ, C (w ξ) * ∑ η ∈ univ.filter (fun η => adj ξ η), Pc F η := by
  simp only [Phi, pressF, map_sum, sum_mul, mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun η _ => sum_congr rfl fun ξ _ => ?_
  by_cases h : adj ξ η
  · simp [h, hsymm _ _ h]
  · have h' : ¬ adj η ξ := fun h' => h (hsymm _ _ h')
    simp [h, h']

/-- `Φ` di "tutte accese" è `∏ f_{n_i}(X_i)`. -/
lemma Phi_allOn : Phi F (fun _ : SigmaMeno.Cell n => (1 : F)) =
    ∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) F) (f F (n i)) := by
  have h1 : ∀ i, Polynomial.aeval (X i : MvPolynomial (Fin d) F) (f F (n i)) =
      ∑ k ∈ (univ : Finset (Fin (n i))), qq F i (k : ℕ) := by
    intro i
    rw [f, map_sum, ← Fin.sum_univ_eq_sum_range (fun k => Polynomial.aeval (X i) (Q F k)) (n i)]
    rfl
  simp_rw [h1]
  rw [prod_univ_sum, Fintype.piFinset_univ, Phi]
  simp [Pc]

section CarDue2

variable [CharP F 2]

/-- **Edge:** `Φ(press w) = (∑ X_i) Φ(w)` modulo l'ideale. -/
theorem mk_Phi_edge (w : SigmaMeno.Cell n → F) :
    Ideal.Quotient.mk (Jid F n) (Phi F (pressF SigmaMeno.EdgeAdj w)) =
      Ideal.Quotient.mk (Jid F n) (∑ i, X i) * Ideal.Quotient.mk (Jid F n) (Phi F w) := by
  have e : Ideal.Quotient.mk (Jid F n) (Phi F w) =
      ∑ ξ, Ideal.Quotient.mk (Jid F n) (C (w ξ) * Pc F ξ) := map_sum _ _ _
  rw [Phi_press _ edgeAdj_symm', e, map_sum, mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [map_mul, edge_cell, map_mul]
  ring

/-- **King:** `Φ(press w) = (∏ (1 + X_i) - 1) Φ(w)` modulo l'ideale. -/
theorem mk_Phi_king (w : SigmaMeno.Cell n → F) :
    Ideal.Quotient.mk (Jid F n) (Phi F (pressF SigmaMeno.KingAdj w)) =
      Ideal.Quotient.mk (Jid F n) (∏ i, (1 + X i) - 1) * Ideal.Quotient.mk (Jid F n) (Phi F w) := by
  have e : Ideal.Quotient.mk (Jid F n) (Phi F w) =
      ∑ ξ, Ideal.Quotient.mk (Jid F n) (C (w ξ) * Pc F ξ) := map_sum _ _ _
  rw [Phi_press _ kingAdj_symm, e, map_sum, mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [map_mul, king_cell, map_mul]
  ring

end CarDue2

end SigmaMeno.Globale
