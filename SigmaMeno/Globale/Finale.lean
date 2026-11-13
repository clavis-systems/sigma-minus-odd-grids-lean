import SigmaMeno.Globale.Incolla

/-!
# Teorema principale: (1) ⇔ (3) per entrambi i vicinati

* metà "raggiungibile ⇒ condizione 3": `Necessaria.lean`, su `F_2`;
* metà "condizione 3 ⇒ raggiungibile": ogni blocco su `K = AlgebraicClosure (ZMod 2)` è
  raggiungibile, si incolla (`Incolla.lean`), si torna alla griglia con `Ψ` (`Inversa.lean`) e
  infine da `K` a `F_2` con la dualità (un certificato su `F_2` sarebbe un certificato su `K`).
-/

namespace SigmaMeno.Globale

open MvPolynomial Finset SigmaMeno.Locale

/-! ### Da `K` a `F_2` -/

/-- Lo scambio delle somme per una relazione simmetrica. -/
lemma press_pairing {F : Type*} [Field F] {V : Type*} [Fintype V] (adj : V → V → Prop)
    [DecidableRel adj] (hsymm : ∀ ξ η, adj ξ η → adj η ξ) (a b : V → F) :
    ∑ ξ, a ξ * pressF adj b ξ = ∑ η, b η * pressF adj a η := by
  simp only [pressF, mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun η _ => sum_congr rfl fun ξ _ => ?_
  by_cases h : adj ξ η
  · simp [h, hsymm _ _ h, mul_comm]
  · have h' : ¬ adj η ξ := fun h' => h (hsymm _ _ h')
    simp [h, h']

/-- Se "tutte accese" si ottiene su un'estensione `K` di `F_2`, si ottiene anche su `F_2`. -/
lemma descend {V : Type*} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
    (hsymm : ∀ ξ η, adj ξ η → adj η ξ) (K : Type*) [Field K] [Algebra (ZMod 2) K]
    (hK : ∃ w : V → K, pressF adj w = fun _ => 1) :
    ∃ w : V → ZMod 2, pressF adj w = fun _ => 1 := by
  by_contra hno
  let L : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    { toFun := pressF adj
      map_add' := fun v w => by funext ξ; simp [pressF, sum_add_distrib]
      map_smul' := fun a w => by funext ξ; simp [pressF, mul_sum] }
  have h1 : (fun _ => (1 : ZMod 2)) ∉ LinearMap.range L := by
    rintro ⟨w, hw⟩; exact hno ⟨w, hw⟩
  obtain ⟨φ, hφ1, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h1 inferInstance
  set k : V → ZMod 2 := fun ξ => φ (fun j => if ξ = j then 1 else 0) with hkdef
  have hφv : ∀ v : V → ZMod 2, φ v = ∑ ξ, v ξ * k ξ := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ v]
    simp [map_sum, map_smul, hkdef]
  have hk : ∀ η, pressF adj k η = 0 := by
    intro η
    have h0 : φ (L (fun j => if η = j then 1 else 0)) = 0 := by
      have hm := Submodule.mem_map_of_mem (f := φ)
        (LinearMap.mem_range_self L (fun j => if η = j then (1 : ZMod 2) else 0))
      rw [hφ] at hm
      exact (Submodule.mem_bot _).1 hm
    rw [hφv] at h0
    have e : ∑ ξ, L (fun j => if η = j then (1 : ZMod 2) else 0) ξ * k ξ = pressF adj k η := by
      have := press_pairing adj hsymm k (fun j => if η = j then (1 : ZMod 2) else 0)
      simp only [mul_comm (k _)] at this
      show ∑ ξ, pressF adj (fun j => if η = j then (1 : ZMod 2) else 0) ξ * k ξ = _
      rw [this]
      simp
    rw [e] at h0
    exact h0
  have hsum : ∑ ξ, k ξ ≠ 0 := by
    have := hφ1
    rw [hφv] at this
    simpa using this
  obtain ⟨w, hw⟩ := hK
  set kK : V → K := fun ξ => algebraMap (ZMod 2) K (k ξ) with hkK
  have hpK : ∀ η, pressF adj kK η = 0 := by
    intro η
    have : pressF adj kK η = algebraMap (ZMod 2) K (pressF adj k η) := by
      simp [pressF, hkK, map_sum]
    rw [this, hk η, map_zero]
  have key : ∑ ξ, kK ξ = 0 := by
    calc ∑ ξ, kK ξ = ∑ ξ, kK ξ * pressF adj w ξ := by rw [hw]; simp
      _ = ∑ η, w η * pressF adj kK η := press_pairing adj hsymm kK w
      _ = 0 := by simp [hpK]
  apply hsum
  have : algebraMap (ZMod 2) K (∑ ξ, k ξ) = 0 := by rw [map_sum]; exact key
  exact (injective_iff_map_eq_zero _).1 (algebraMap (ZMod 2) K).injective _ this

/-! ### Ogni blocco è raggiungibile -/

variable {K : Type*} [Field K] [IsAlgClosed K] [CharP K 2] [DecidableEq K] {d : ℕ}

lemma cond_fl (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (h3 : SigmaMeno.Condition3 n)
    (lv : Fin d → K) : Cond (fl n lv) := by
  by_cases hall : ∀ i, lv i = 0
  · have : fl n lv = fZ n := by funext i; simp [fl, fZ, hall i]
    rw [this]
    exact (cond_fZ_iff n hn).2 h3
  · push_neg at hall
    obtain ⟨i, hi⟩ := hall
    refine ⟨SigmaMeno.a (n i) + 1, by omega, Or.inl ⟨i, ?_⟩⟩
    simp [fl, hi]

lemma block_edge (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (h3 : SigmaMeno.Condition3 n)
    (lv : Fin d → K) (hlv : lv ∈ Fintype.piFinset (fun i => Lam K (n i))) :
    ∃ y, (∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) K) (f K (n i))) -
      (∑ i, X i) * y ∈ Ib n lv := by
  have hα : ∀ i : Fin d, (fun _ => (1 : K)) i ≠ 0 := fun _ => one_ne_zero
  apply block_of_local n hn lv (fun _ => 1) hα hlv
  have hshift : rhoP lv (fun _ => (1 : K)) (∑ i, X i) = ∑ i, X i + C (∑ i, lv i) := by
    simp only [rhoP, map_sum, aeval_X, C_1, one_mul, sum_add_distrib, map_sum]
  by_cases hs : ∑ i, lv i = 0
  · rw [hs, C_0, add_zero] at hshift
    exact shifted_of_reach n hn lv _ hα hlv _ (uE K (Fin d)) hshift
      ((local_theorem_edge (fl n lv)).2 (cond_fl n hn h3 lv))
  · apply shifted_of_unit
    rw [hshift, map_add, add_comm]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ (Commute.all _ _)
    · rw [map_sum]
      exact isNilpotent_sum fun i _ => nil_X (fl n lv) i
    · exact (isUnit_iff_ne_zero.2 hs).map
        (algebraMap K (MvPolynomial (Fin d) K ⧸ Locale.I K (fl n lv)))

lemma block_king (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) (h3 : SigmaMeno.Condition3 n)
    (lv : Fin d → K) (hlv : lv ∈ Fintype.piFinset (fun i => Lam K (n i))) :
    ∃ y, (∏ i, Polynomial.aeval (X i : MvPolynomial (Fin d) K) (f K (n i))) -
      (∏ i, (1 + X i) - 1) * y ∈ Ib n lv := by
  by_cases hp : ∏ i, (1 + lv i) = 1
  · have hμ : ∀ i, 1 + lv i ≠ 0 := by
      intro i h0
      rw [prod_eq_zero (mem_univ i) h0] at hp
      exact zero_ne_one hp
    apply block_of_local n hn lv (fun i => 1 + lv i) hμ hlv
    have hshift : rhoP lv (fun i => 1 + lv i) (∏ i, (1 + X i) - 1) = uK K (Fin d) := by
      have e : ∀ i, rhoP lv (fun i => 1 + lv i) (1 + X i) = C (1 + lv i) * (1 + X i) := by
        intro i
        simp only [rhoP, map_add, map_one, aeval_X, C_add, C_1]
        ring
      rw [map_sub, map_one, map_prod]
      simp_rw [e]
      rw [prod_mul_distrib, ← map_prod, hp, C_1, one_mul, uK]
    exact shifted_of_reach n hn lv _ hμ hlv _ (uK K (Fin d)) hshift
      ((local_theorem_king (fl n lv)).2 (cond_fl n hn h3 lv))
  · have hα : ∀ i : Fin d, (fun _ => (1 : K)) i ≠ 0 := fun _ => one_ne_zero
    apply block_of_local n hn lv (fun _ => 1) hα hlv
    apply shifted_of_unit
    have e : rhoP lv (fun _ => (1 : K)) (∏ i, (1 + X i) - 1) =
        ∏ i, (C (1 + lv i) + X i) - 1 := by
      rw [map_sub, map_one, map_prod]
      refine congrArg (· - 1) (prod_congr rfl fun i _ => ?_)
      simp only [rhoP, map_add, map_one, aeval_X, C_add, C_1, one_mul]
      ring
    rw [e, map_sub, map_one]
    have hsplit : Ideal.Quotient.mk (Locale.I K (fl n lv)) (∏ i, (C (1 + lv i) + X i)) - 1 =
        algebraMap K _ (∏ i, (1 + lv i) - 1) +
          (Ideal.Quotient.mk (Locale.I K (fl n lv)) (∏ i, (C (1 + lv i) + X i)) -
            algebraMap K _ (∏ i, (1 + lv i))) := by
      rw [map_sub, map_one]; ring
    rw [hsplit]
    exact IsNilpotent.isUnit_add_left_of_commute (nil_prod (fl n lv) (fun i => 1 + lv i) univ)
      ((isUnit_iff_ne_zero.2 (sub_ne_zero.2 hp)).map
        (algebraMap K (MvPolynomial (Fin d) K ⧸ Locale.I K (fl n lv)))) (Commute.all _ _)

/-! ### Il teorema principale, (1) ⇔ (3) -/

lemma hpos_of_odd {d : ℕ} (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) : ∀ i, 0 < n i :=
  fun i => (hn i).pos

/-- **Teorema principale, vicinato edge: (1) ⇔ (3).** -/
theorem principale_edge {d : ℕ} (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) :
    SigmaMeno.Reachable (SigmaMeno.EdgeAdj (n := n)) SigmaMeno.allOn ↔ SigmaMeno.Condition3 n := by
  classical
  refine ⟨necessaria_edge n hn, fun h3 => ?_⟩
  let K := AlgebraicClosure (ZMod 2)
  obtain ⟨Y, hY⟩ := glue (K := K) n hn _ _ (block_edge n hn h3)
  have hY' : Ideal.Quotient.mk (Jid K n) (Phi K (fun _ : SigmaMeno.Cell n => (1 : K))) =
      Ideal.Quotient.mk (Jid K n) (∑ i, X i) * Ideal.Quotient.mk (Jid K n) Y := by
    rw [Phi_allOn, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hY
  have hw := grid_of_ring (F := K) (hpos_of_odd n hn) SigmaMeno.EdgeAdj (∑ i, X i)
    (mk_Phi_edge (F := K)) Y hY'
  obtain ⟨w, hw'⟩ := descend SigmaMeno.EdgeAdj edgeAdj_symm' K ⟨_, hw⟩
  exact ⟨w, hw'⟩

/-- **Teorema principale, vicinato king: (1) ⇔ (3).** -/
theorem principale_king {d : ℕ} (n : Fin d → ℕ) (hn : ∀ i, Odd (n i)) :
    SigmaMeno.Reachable (SigmaMeno.KingAdj (n := n)) SigmaMeno.allOn ↔ SigmaMeno.Condition3 n := by
  classical
  refine ⟨necessaria_king n hn, fun h3 => ?_⟩
  let K := AlgebraicClosure (ZMod 2)
  obtain ⟨Y, hY⟩ := glue (K := K) n hn _ _ (block_king n hn h3)
  have hY' : Ideal.Quotient.mk (Jid K n) (Phi K (fun _ : SigmaMeno.Cell n => (1 : K))) =
      Ideal.Quotient.mk (Jid K n) (∏ i, (1 + X i) - 1) * Ideal.Quotient.mk (Jid K n) Y := by
    rw [Phi_allOn, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hY
  have hw := grid_of_ring (F := K) (hpos_of_odd n hn) SigmaMeno.KingAdj (∏ i, (1 + X i) - 1)
    (mk_Phi_king (F := K)) Y hY'
  obtain ⟨w, hw'⟩ := descend SigmaMeno.KingAdj kingAdj_symm K ⟨_, hw⟩
  exact ⟨w, hw'⟩

end SigmaMeno.Globale
