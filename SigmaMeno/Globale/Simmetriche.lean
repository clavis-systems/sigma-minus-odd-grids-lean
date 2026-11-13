import SigmaMeno.Globale.Riflessione

/-!
# Le configurazioni completamente simmetriche e il teorema principale completo

Le celle si raggruppano per "fibre" `∏_i {ξ_i, n_i - 1 - ξ_i}` (con `ξ` nel dominio
fondamentale). Una configurazione completamente simmetrica è costante sulle fibre, e la somma dei
`P_η` su una fibra è `∏_i (Q_{ξ_i} + Q_{n_i-1-ξ_i})(X_i) ≡ ∏_i g_i(X_i) · c`. Quindi
`Φ(x) ≡ p · c`, e se "tutte accese" è raggiungibile lo è anche `x` (con `Ψ`).
-/

namespace SigmaMeno.Globale

open MvPolynomial Finset

variable {d : ℕ} {n : Fin d → ℕ}

/-- Ripiegamento di una coordinata nel dominio fondamentale. -/
def foldv {N : ℕ} (t : Fin N) : Fin N := if 2 * (t : ℕ) + 1 ≤ N then t else Fin.rev t

/-- Il dominio fondamentale di una coordinata. -/
def Dset (N : ℕ) : Finset (Fin N) := univ.filter (fun t : Fin N => 2 * (t : ℕ) + 1 ≤ N)

lemma foldv_mem {N : ℕ} (t : Fin N) : foldv t ∈ Dset N := by
  have h1 := Fin.val_rev t
  have h2 := t.isLt
  unfold foldv Dset
  split_ifs with h
  · simp only [mem_filter, mem_univ, true_and]; exact h
  · simp only [mem_filter, mem_univ, true_and, h1]; omega

lemma foldv_eq_iff {N : ℕ} (t a : Fin N) (ha : a ∈ Dset N) :
    foldv t = a ↔ t ∈ ({a, Fin.rev a} : Finset (Fin N)) := by
  simp only [Dset, mem_filter, mem_univ, true_and] at ha
  have h1 := Fin.val_rev t
  have h2 := Fin.val_rev a
  have h3 := t.isLt
  have h4 := a.isLt
  rw [mem_insert, mem_singleton]
  unfold foldv
  split_ifs with h
  · simp only [Fin.ext_iff, h2]
    constructor
    · intro e; left; exact e
    · rintro (e | e) <;> omega
  · simp only [Fin.ext_iff, h1, h2]
    constructor
    · intro e; right; omega
    · rintro (e | e) <;> omega

/-- Ripiegamento di una cella. -/
def fold (η : SigmaMeno.Cell n) : SigmaMeno.Cell n := fun i => foldv (η i)

/-- Riflessione delle coordinate in `S`. -/
def flipS (S : Finset (Fin d)) (η : SigmaMeno.Cell n) : SigmaMeno.Cell n :=
  fun i => if i ∈ S then Fin.rev (η i) else η i

lemma cs_flip (x : SigmaMeno.Cell n → ZMod 2) (hx : SigmaMeno.CompletelySymmetric x)
    (η : SigmaMeno.Cell n) (S : Finset (Fin d)) : x (flipS S η) = x η := by
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih =>
    have e : flipS (insert a S) η = SigmaMeno.reflect a (flipS S η) := by
      funext i
      by_cases hia : i = a
      · subst hia; simp [flipS, SigmaMeno.reflect, ha]
      · simp [flipS, SigmaMeno.reflect, Function.update_of_ne hia, mem_insert, hia]
    rw [e, hx a, ih]

lemma cs_fold (x : SigmaMeno.Cell n → ZMod 2) (hx : SigmaMeno.CompletelySymmetric x)
    (η : SigmaMeno.Cell n) : x (fold η) = x η := by
  have e : fold η = flipS (univ.filter (fun i => ¬ 2 * ((η i : Fin (n i)) : ℕ) + 1 ≤ n i)) η := by
    funext i
    simp only [fold, foldv, flipS, mem_filter, mem_univ, true_and]
    split_ifs <;> simp_all
  rw [e, cs_flip x hx]

/-- Le celle si dividono in fibre. -/
lemma fiber_sum {M : Type*} [AddCommMonoid M] (G : SigmaMeno.Cell n → M) :
    ∑ η, G η = ∑ ξ ∈ Fintype.piFinset (fun i => Dset (n i)),
      ∑ η ∈ Fintype.piFinset (fun i => ({ξ i, Fin.rev (ξ i)} : Finset (Fin (n i)))), G η := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := Fintype.piFinset (fun i => Dset (n i)))
    (g := fold) (fun η _ => Fintype.mem_piFinset.2 fun i => foldv_mem (η i))]
  refine sum_congr rfl fun ξ hξ => ?_
  congr 1
  ext η
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rw [funext_iff]
  exact forall_congr' fun i => foldv_eq_iff (η i) (ξ i) (Fintype.mem_piFinset.1 hξ i)

/-- **Simmetriche:** `Φ(x) ≡ p · c`. -/
lemma Phi_cs (hn : ∀ i, Odd (n i)) (x : SigmaMeno.Cell n → ZMod 2)
    (hx : SigmaMeno.CompletelySymmetric x) :
    ∃ p, Ideal.Quotient.mk (Jid (ZMod 2) n) (Phi (ZMod 2) x) =
      Ideal.Quotient.mk (Jid (ZMod 2) n) p *
        Ideal.Quotient.mk (Jid (ZMod 2) n)
          (∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) (ZMod 2)) (f (ZMod 2) (n i))) := by
  choose g hg using fun i (t : Fin (n i)) => fibra (F := ZMod 2) (n i) (hn i) t
  refine ⟨∑ ξ ∈ Fintype.piFinset (fun i => Dset (n i)),
    C (x ξ) * ∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) (ZMod 2)) (g i (ξ i)), ?_⟩
  have hfac : ∀ i (t : Fin (n i)),
      Ideal.Quotient.mk (Jid (ZMod 2) n)
        (∑ s ∈ ({t, Fin.rev t} : Finset (Fin (n i))), qq (ZMod 2) i (s : ℕ)) =
      Ideal.Quotient.mk (Jid (ZMod 2) n) (Polynomial.aeval (X i) (g i t)) *
        Ideal.Quotient.mk (Jid (ZMod 2) n) (Polynomial.aeval (X i) (f (ZMod 2) (n i))) := by
    intro i t
    obtain ⟨r, hr⟩ := hg i t
    rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have e : (∑ s ∈ ({t, Fin.rev t} : Finset (Fin (n i))), qq (ZMod 2) i (s : ℕ)) -
        Polynomial.aeval (X i) (g i t) * Polynomial.aeval (X i) (f (ZMod 2) (n i)) =
        qq (ZMod 2) i (n i) * Polynomial.aeval (X i) r := by
      have hs : ∑ s ∈ ({t, Fin.rev t} : Finset (Fin (n i))), qq (ZMod 2) i (s : ℕ) =
          Polynomial.aeval (X i) (∑ s ∈ ({t, Fin.rev t} : Finset (Fin (n i))), Q (ZMod 2) (s : ℕ)) := by
        rw [map_sum]; rfl
      rw [hs, ← map_mul, ← map_sub, hr, map_mul]
      rfl
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hsum : Phi (ZMod 2) x = ∑ ξ ∈ Fintype.piFinset (fun i => Dset (n i)),
      C (x ξ) * ∏ i, ∑ s ∈ ({ξ i, Fin.rev (ξ i)} : Finset (Fin (n i))), qq (ZMod 2) i (s : ℕ) := by
    rw [Phi, fiber_sum]
    refine sum_congr rfl fun ξ hξ => ?_
    rw [prod_univ_sum, mul_sum]
    refine sum_congr rfl fun η hη => ?_
    have hfold : fold η = ξ := by
      funext i
      exact (foldv_eq_iff (η i) (ξ i) (Fintype.mem_piFinset.1 hξ i)).2
        (Fintype.mem_piFinset.1 hη i)
    rw [← cs_fold x hx η, hfold, Pc]
  rw [hsum, map_sum, map_sum, sum_mul]
  refine sum_congr rfl fun ξ _ => ?_
  rw [map_mul, map_mul, map_prod, map_prod, map_prod]
  simp_rw [hfac]
  rw [prod_mul_distrib]
  ring

/-- Se "tutte accese" è raggiungibile, ogni configurazione completamente simmetrica lo è. -/
lemma reach_cs (hn : ∀ i, Odd (n i)) (adj : SigmaMeno.Cell n → SigmaMeno.Cell n → Prop)
    [DecidableRel adj] (m : MvPolynomial (Fin d) (ZMod 2))
    (hm : ∀ w, Ideal.Quotient.mk (Jid (ZMod 2) n) (Phi (ZMod 2) (pressF adj w)) =
      Ideal.Quotient.mk (Jid (ZMod 2) n) m * Ideal.Quotient.mk (Jid (ZMod 2) n) (Phi (ZMod 2) w))
    (w0 : SigmaMeno.Cell n → ZMod 2) (hw0 : pressF adj w0 = fun _ => 1)
    (x : SigmaMeno.Cell n → ZMod 2) (hx : SigmaMeno.CompletelySymmetric x) :
    ∃ w, pressF adj w = x := by
  have hpos := hpos_of_odd n hn
  obtain ⟨p, hp⟩ := Phi_cs hn x hx
  have hY := hm w0
  rw [hw0, Phi_allOn] at hY
  refine ⟨Psi hpos (p * Phi (ZMod 2) w0), ?_⟩
  have h : Phi (ZMod 2) (pressF adj (Psi hpos (p * Phi (ZMod 2) w0)) - x) ∈ Jid (ZMod 2) n := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Phi_sub, map_sub, hm, Phi_Psi, hp, hY, map_mul]
    ring
  have := Psi_Jid hpos h
  rw [Psi_Phi] at this
  exact sub_eq_zero.1 this

/-- **Il teorema principale della nota, completo.** -/
theorem teorema_principale : SigmaMeno.TeoremaPrincipale := by
  intro d n hn
  have hall : SigmaMeno.CompletelySymmetric (SigmaMeno.allOn : SigmaMeno.Cell n → ZMod 2) :=
    fun _ _ => rfl
  refine ⟨principale_edge n hn, ⟨fun h => (principale_edge n hn).1 (h _ hall), fun h3 x hx => ?_⟩,
    principale_king n hn, ⟨fun h => (principale_king n hn).1 (h _ hall), fun h3 x hx => ?_⟩⟩
  · obtain ⟨w0, hw0⟩ := (principale_edge n hn).2 h3
    exact reach_cs hn SigmaMeno.EdgeAdj (∑ i, X i) (mk_Phi_edge (F := ZMod 2)) w0 hw0 x hx
  · obtain ⟨w0, hw0⟩ := (principale_king n hn).2 h3
    exact reach_cs hn SigmaMeno.KingAdj (∏ i, (1 + X i) - 1) (mk_Phi_king (F := ZMod 2)) w0 hw0 x hx

end SigmaMeno.Globale
