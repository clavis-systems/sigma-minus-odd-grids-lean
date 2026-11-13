import SigmaMeno.Globale.Necessaria

/-!
# La mappa inversa: dall'anello alla griglia

`J_i` è l'adiacenza del cammino nella direzione `i`. Gli operatori `J_i` commutano, quindi la
sottoalgebra che generano è commutativa e `Ψ(p) = p(J_1, …, J_d) · e_0` è ben definita.
Risultati: `Ψ(Φ(w)) = w`, `Φ(Ψ(p)) ≡ p` e `Ψ` si annulla sull'ideale `(Q_{n_i}(X_i))`.
Ne segue: se `c ≡ m · Y` nell'anello, allora "tutte accese" è raggiungibile sulla griglia.
-/

namespace SigmaMeno.Globale

open MvPolynomial Finset

variable {F : Type*} [Field F] {d : ℕ} {n : Fin d → ℕ}

/-- Vicine nella direzione `i`. -/
def DirAdj (i : Fin d) (ξ η : SigmaMeno.Cell n) : Prop :=
  (((ξ i : ℕ) : ℤ) - ((η i : ℕ) : ℤ)).natAbs = 1 ∧ ∀ j, j ≠ i → ξ j = η j

instance (i : Fin d) : DecidableRel (DirAdj (n := n) i) := fun ξ η => by
  unfold DirAdj; infer_instance

lemma dirAdj_symm (i : Fin d) (ξ η : SigmaMeno.Cell n) : DirAdj i ξ η → DirAdj i η ξ := by
  rintro ⟨h, hj⟩
  refine ⟨?_, fun j hji => (hj j hji).symm⟩
  rw [SigmaMeno.natAbs_sub_eq_one_iff] at h ⊢
  omega

/-- Le vicine nella direzione `i` sono le `update ξ i k`. -/
lemma dir_sum {M : Type*} [AddCommMonoid M] (i : Fin d) (ξ : SigmaMeno.Cell n)
    (G : SigmaMeno.Cell n → M) :
    ∑ η ∈ univ.filter (fun η => DirAdj i ξ η), G η =
      ∑ k ∈ univ.filter (fun k : Fin (n i) => (((ξ i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs = 1),
        G (Function.update ξ i k) := by
  symm
  refine sum_bij (fun k _ => Function.update ξ i k) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    refine ⟨by rw [Function.update_self]; exact hk, fun j hj => ?_⟩
    rw [Function.update_of_ne hj]
  · intro k _ k' _ h
    have := congrFun h i
    simpa using this
  · intro η hη
    simp only [mem_filter, mem_univ, true_and] at hη
    obtain ⟨hi, hj⟩ := hη
    refine ⟨η i, by simp [hi], ?_⟩
    funext j
    by_cases hji : j = i
    · subst hji; simp
    · rw [Function.update_of_ne hji]; exact hj j hji

/-- L'operatore `J_i`. -/
noncomputable def Jop (F : Type*) [Field F] {d : ℕ} {n : Fin d → ℕ} (i : Fin d) :
    Module.End F (SigmaMeno.Cell n → F) where
  toFun w := pressF (DirAdj i) w
  map_add' v w := by funext ξ; simp [pressF, sum_add_distrib]
  map_smul' a w := by funext ξ; simp [pressF, mul_sum]

lemma Jop_apply (i : Fin d) (w : SigmaMeno.Cell n → F) (ξ : SigmaMeno.Cell n) :
    Jop F i w ξ = ∑ k ∈ univ.filter
      (fun k : Fin (n i) => (((ξ i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs = 1),
        w (Function.update ξ i k) := by
  show pressF (DirAdj i) w ξ = _
  rw [pressF, dir_sum]

/-- Gli operatori `J_i` commutano. -/
lemma Jop_comm (i j : Fin d) : Jop F (n := n) i * Jop F j = Jop F j * Jop F i := by
  by_cases hij : i = j
  · subst hij; rfl
  refine LinearMap.ext fun w => funext fun ξ => ?_
  simp only [Module.End.mul_apply, Jop_apply]
  have e1 : ∀ k : Fin (n i), (Function.update ξ i k) j = ξ j := fun k =>
    Function.update_of_ne (Ne.symm hij) _ _
  have e2 : ∀ l : Fin (n j), (Function.update ξ j l) i = ξ i := fun l =>
    Function.update_of_ne hij _ _
  simp_rw [e1, e2]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => sum_congr rfl fun k _ => ?_
  rw [Function.update_comm hij]

section CarDue

variable [CharP F 2]

lemma mk_Phi_dir (i : Fin d) (w : SigmaMeno.Cell n → F) :
    Ideal.Quotient.mk (Jid F n) (Phi F (Jop F i w)) =
      Ideal.Quotient.mk (Jid F n) (X i) * Ideal.Quotient.mk (Jid F n) (Phi F w) := by
  have e : Ideal.Quotient.mk (Jid F n) (Phi F w) =
      ∑ ξ, Ideal.Quotient.mk (Jid F n) (C (w ξ) * Pc F ξ) := map_sum _ _ _
  show Ideal.Quotient.mk (Jid F n) (Phi F (pressF (DirAdj i) w)) = _
  rw [Phi_press _ (dirAdj_symm i), e, map_sum, mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [map_mul, dir_sum, map_mul]
  simp_rw [Pc_update, ← sum_mul, line_sum]
  rw [Pc_eq ξ i]
  split_ifs <;> simp [map_add, map_mul, mk_qq_n] <;> ring

end CarDue

/-! ### La sottoalgebra commutativa e `Ψ` -/

section Psi

open IsMulCommutative

/-- La sottoalgebra generata dai `J_i`. -/
noncomputable abbrev Aop (F : Type*) [Field F] {d : ℕ} (n : Fin d → ℕ) :
    Subalgebra F (Module.End F (SigmaMeno.Cell n → F)) :=
  Algebra.adjoin F (Set.range fun i => Jop F (n := n) i)

instance : IsMulCommutative (Aop F n) :=
  Algebra.isMulCommutative_adjoin F (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact Jop_comm i j)

/-- `p ↦ p(J_1, …, J_d)`. -/
noncomputable def evalA : MvPolynomial (Fin d) F →ₐ[F] Aop F n :=
  aeval fun i => ⟨Jop F i, Algebra.subset_adjoin ⟨i, rfl⟩⟩

/-- La cella `0`. -/
def zc (hpos : ∀ i, 0 < n i) : SigmaMeno.Cell n := fun i => ⟨0, hpos i⟩

/-- Il vettore che vale `1` solo nella cella `ζ`. -/
def ev (ζ : SigmaMeno.Cell n) : SigmaMeno.Cell n → F := fun ξ => if ξ = ζ then 1 else 0

/-- `Ψ(p) = p(J) · e_0`. -/
noncomputable def Psi (hpos : ∀ i, 0 < n i) (p : MvPolynomial (Fin d) F) :
    SigmaMeno.Cell n → F :=
  (Aop F n).val (evalA (n := n) p) (ev (zc hpos))

variable (hpos : ∀ i, 0 < n i)

lemma Psi_add (p q : MvPolynomial (Fin d) F) : Psi hpos (p + q) = Psi hpos p + Psi hpos q := by
  simp [Psi, map_add]

lemma Psi_mul (p q : MvPolynomial (Fin d) F) :
    Psi hpos (p * q) = (Aop F n).val (evalA (n := n) p) (Psi hpos q) := by
  simp only [Psi, map_mul, Module.End.mul_apply]

lemma Psi_C_mul (a : F) (p : MvPolynomial (Fin d) F) :
    Psi hpos (C a * p) = a • Psi hpos p := by
  rw [Psi_mul]
  simp [evalA, MvPolynomial.aeval_C]

lemma Psi_X_mul (i : Fin d) (p : MvPolynomial (Fin d) F) :
    Psi hpos (X i * p) = Jop F i (Psi hpos p) := by
  rw [Psi_mul]
  simp [evalA]

lemma Psi_mul_X (i : Fin d) (p : MvPolynomial (Fin d) F) :
    Psi hpos (p * X i) = Jop F i (Psi hpos p) := by
  rw [mul_comm, Psi_X_mul]

/-- `evalA (Q_k(X_i)) = Q_k(J_i)`. -/
lemma evalA_qq (i : Fin d) (k : ℕ) :
    (Aop F n).val (evalA (n := n) (qq F i k)) = Polynomial.aeval (Jop F i) (Q F k) := by
  rw [qq, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
  simp [evalA]

/-- I vettori sulla retta per `η` nella direzione `i`. -/
def Lv (η : SigmaMeno.Cell n) (i : Fin d) (k : ℕ) : SigmaMeno.Cell n → F :=
  fun ξ => if (∀ j, j ≠ i → ξ j = η j) ∧ (ξ i : ℕ) = k then 1 else 0

lemma Lv_ge (η : SigmaMeno.Cell n) (i : Fin d) (k : ℕ) (hk : n i ≤ k) : Lv (F := F) η i k = 0 := by
  funext ξ
  have := (ξ i).isLt
  simp only [Lv, Pi.zero_apply]
  rw [if_neg (by omega)]

variable [CharP F 2]

/-- `J_i` su una retta: `J L_k = L_{k+1} + L_{k-1}`. -/
lemma Jop_Lv (η : SigmaMeno.Cell n) (i : Fin d) (k : ℕ) (hk : k < n i) :
    Jop F i (Lv η i k) = Lv η i (k + 1) + (if 0 < k then Lv η i (k - 1) else 0) := by
  funext ξ
  rw [Jop_apply]
  by_cases hl : ∀ j, j ≠ i → ξ j = η j
  · have hterm : ∀ k' : Fin (n i), Lv (F := F) η i k (Function.update ξ i k') =
        if (k' : ℕ) = k then 1 else 0 := by
      intro k'
      unfold Lv
      rw [Function.update_self]
      congr 1
      apply propext
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨fun j hj => ?_, h⟩
        rw [Function.update_of_ne hj]
        exact hl j hj
    simp_rw [hterm]
    rw [sum_filter, Fin.sum_univ_eq_sum_range (fun s => if (((ξ i : ℕ) : ℤ) - (s : ℤ)).natAbs = 1
      then (if s = k then (1 : F) else 0) else 0) (n i)]
    have hpt : ∀ s : ℕ, (if (((ξ i : ℕ) : ℤ) - (s : ℤ)).natAbs = 1 then
        (if s = k then (1 : F) else 0) else 0) =
        if s = k then (if (((ξ i : ℕ) : ℤ) - (k : ℤ)).natAbs = 1 then 1 else 0) else 0 := by
      intro s; by_cases hs : s = k <;> simp [hs]
    rw [sum_congr rfl fun s _ => hpt s, sum_ite_eq']
    have hl' : (∀ j, j ≠ i → ξ j = η j) = True := eq_true hl
    simp only [mem_range, if_pos hk, SigmaMeno.natAbs_sub_eq_one_iff, Pi.add_apply, ite_apply,
      Pi.zero_apply, Lv, hl', true_and]
    split_ifs <;> first | omega | simp
  · have h0 : ∀ k' : Fin (n i), Lv (F := F) η i k (Function.update ξ i k') = 0 := by
      intro k'
      unfold Lv
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hl fun j hj => by have := h j hj; rwa [Function.update_of_ne hj] at this
    simp only [h0, sum_const_zero, Pi.add_apply]
    split_ifs <;> simp [Lv, hl]

/-- `Q_k(J_i)` manda `L_0` in `L_k`, per `k ≤ n_i`. -/
lemma aeval_Q_Lv (η : SigmaMeno.Cell n) (i : Fin d) (k : ℕ) (hk : k ≤ n i) :
    Polynomial.aeval (Jop F i) (Q F k) (Lv η i 0) = Lv η i k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp only [Q_one, Polynomial.aeval_X]
    rw [Jop_Lv η i 0 (by omega)]
    simp
  | more k ih1 ih2 =>
    rw [Q_ss, map_add, map_mul, Polynomial.aeval_X, LinearMap.add_apply, Module.End.mul_apply,
      ih2 (by omega), ih1 (by omega), Jop_Lv η i (k + 1) (by omega)]
    simp only [show 0 < k + 1 from by omega, if_true, Nat.add_sub_cancel]
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    funext ξ
    simp only [Pi.add_apply]
    linear_combination (Lv η i k ξ) * h2

lemma Psi_qq_n (i : Fin d) : Psi hpos (qq F i (n i)) = 0 := by
  have hL : ev (zc hpos) = Lv (F := F) (zc hpos) i 0 := by
    funext ξ
    simp only [ev, Lv]
    by_cases h : ξ = zc hpos
    · subst h; simp [zc]
    · rw [if_neg h, if_neg]
      rintro ⟨hj, hi⟩
      apply h
      funext j
      by_cases hji : j = i
      · subst hji; exact Fin.ext hi
      · exact hj j hji
  rw [Psi, evalA_qq, hL, aeval_Q_Lv _ i (n i) le_rfl, Lv_ge _ i _ le_rfl]

/-- `Ψ` si annulla sull'ideale. -/
lemma Psi_Jid {p : MvPolynomial (Fin d) F} (hp : p ∈ Jid F n) : Psi hpos p = 0 := by
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Psi_qq_n hpos i
  | zero => simp [Psi]
  | add x y _ _ hx hy => rw [Psi_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, Psi_mul, hx, map_zero]

/-- La cella `ξ` ristretta a `S` (zero fuori da `S`). -/
def restr (ξ : SigmaMeno.Cell n) (S : Finset (Fin d)) : SigmaMeno.Cell n :=
  fun j => if j ∈ S then ξ j else ⟨0, hpos j⟩

lemma Psi_Pc_aux (ξ : SigmaMeno.Cell n) (S : Finset (Fin d)) :
    (Aop F n).val (∏ i ∈ S, evalA (n := n) (qq F i (ξ i : ℕ))) (ev (zc hpos)) =
      ev (restr hpos ξ S) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [prod_empty, map_one, Module.End.one_apply]
    congr 1
  | insert a S ha ih =>
    rw [prod_insert ha, map_mul, Module.End.mul_apply, ih, evalA_qq]
    have hL : ev (restr hpos ξ S) = Lv (F := F) (restr hpos ξ S) a 0 := by
      funext ζ
      simp only [ev, Lv]
      by_cases h : ζ = restr hpos ξ S
      · subst h; simp [restr, ha]
      · rw [if_neg h, if_neg]
        rintro ⟨hj, hi⟩
        apply h
        funext j
        by_cases hja : j = a
        · subst hja; simp only [restr, if_neg ha]; exact Fin.ext hi
        · exact hj j hja
    rw [hL, aeval_Q_Lv _ a _ (ξ a).isLt.le]
    funext ζ
    simp only [ev, Lv]
    congr 1
    apply propext
    constructor
    · rintro ⟨hj, hi⟩
      funext j
      by_cases hja : j = a
      · subst hja; simp only [restr, mem_insert, true_or, if_true]; exact Fin.ext hi
      · rw [hj j hja]; simp [restr, mem_insert, hja]
    · rintro rfl
      refine ⟨fun j hja => ?_, by simp [restr]⟩
      simp [restr, mem_insert, hja]

/-- `Ψ(P_ξ) = e_ξ`. -/
lemma Psi_Pc (ξ : SigmaMeno.Cell n) : Psi hpos (Pc F ξ) = ev ξ := by
  rw [Psi, Pc, map_prod, Psi_Pc_aux]
  congr 1
  funext j
  simp [restr]

/-- `Ψ(Φ(w)) = w`. -/
lemma Psi_Phi (w : SigmaMeno.Cell n → F) : Psi hpos (Phi F w) = w := by
  rw [Phi]
  have : ∀ s : Finset (SigmaMeno.Cell n),
      Psi hpos (∑ ξ ∈ s, C (w ξ) * Pc F ξ) = ∑ ξ ∈ s, w ξ • ev ξ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Psi]
    | insert a s ha ih => rw [sum_insert ha, sum_insert ha, Psi_add, ih, Psi_C_mul, Psi_Pc]
  rw [this]
  funext ζ
  simp [ev]

lemma Phi_add (v w : SigmaMeno.Cell n → F) : Phi F (v + w) = Phi F v + Phi F w := by
  simp [Phi, map_add, add_mul, sum_add_distrib]

lemma Phi_sub (v w : SigmaMeno.Cell n → F) : Phi F (v - w) = Phi F v - Phi F w := by
  simp [Phi, map_sub, sub_mul, sum_sub_distrib]

lemma Phi_smul (a : F) (v : SigmaMeno.Cell n → F) : Phi F (a • v) = C a * Phi F v := by
  simp [Phi, mul_sum, map_mul, mul_assoc]

/-- `Φ(Ψ(p)) ≡ p`. -/
lemma Phi_Psi (p : MvPolynomial (Fin d) F) :
    Ideal.Quotient.mk (Jid F n) (Phi F (Psi hpos p)) = Ideal.Quotient.mk (Jid F n) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h1 : Psi hpos (C a : MvPolynomial (Fin d) F) = a • ev (zc hpos) := by
      have := Psi_C_mul hpos a 1
      rw [mul_one] at this
      rw [this]
      simp [Psi]
    rw [h1, Phi_smul]
    have h2 : Phi F (ev (zc hpos) : SigmaMeno.Cell n → F) = 1 := by
      rw [Phi, sum_eq_single (zc hpos)]
      · simp [ev, Pc, zc, qq_zero]
      · intro b _ hb; simp [ev, hb]
      · simp
    rw [h2, mul_one]
  | add p q hp hq => rw [Psi_add, Phi_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [Psi_mul_X, mk_Phi_dir, hp, map_mul, mul_comm]

/-- **Dall'anello alla griglia.** Se `c ≡ m Y` e `m` agisce come la pressione, la configurazione
"tutte accese" si ottiene premendo `Ψ(Y)`. -/
lemma grid_of_ring (adj : SigmaMeno.Cell n → SigmaMeno.Cell n → Prop) [DecidableRel adj]
    (m : MvPolynomial (Fin d) F)
    (hm : ∀ w, Ideal.Quotient.mk (Jid F n) (Phi F (pressF adj w)) =
      Ideal.Quotient.mk (Jid F n) m * Ideal.Quotient.mk (Jid F n) (Phi F w))
    (Y : MvPolynomial (Fin d) F)
    (hY : Ideal.Quotient.mk (Jid F n) (Phi F (fun _ : SigmaMeno.Cell n => (1 : F))) =
      Ideal.Quotient.mk (Jid F n) m * Ideal.Quotient.mk (Jid F n) Y) :
    pressF adj (Psi hpos Y) = fun _ : SigmaMeno.Cell n => (1 : F) := by
  have h : Phi F (pressF adj (Psi hpos Y) - fun _ : SigmaMeno.Cell n => (1 : F)) ∈ Jid F n := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Phi_sub, map_sub, hm, Phi_Psi, hY, sub_self]
  have := Psi_Jid hpos h
  rw [Psi_Phi] at this
  exact sub_eq_zero.1 this

end Psi

end SigmaMeno.Globale
