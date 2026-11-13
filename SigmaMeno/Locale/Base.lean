import SigmaMeno.Locale.Algebra

/-!
# Il problema locale: definizioni

Un'istanza è una funzione `f : ι → Factor` (`ι` finito). Il fattore `Z b` è il fattore `Z_q` della
nota con `q = 2^b` (taglia `s = 2q - 1`, esponente `j = q - 1`, livello `b`); il fattore `N a` è
`N_p` con `p = 2^a` (taglia `2p`, esponente `p`, livello `a + 1`). `Z 0` è il fattore banale.

L'anello locale è `F[X_i] / (X_i ^ s_i)`; qui lavoriamo con i polinomi e con l'ideale `I F f`.
`Reach f u` dice che `c = ∏ X_i ^ j_i` sta in `u · L` (modulo l'ideale).
Per il vicinato edge `u = ∑ X_i`, per il vicinato king `u = ∏ (1 + X_i) - 1`.
-/

namespace SigmaMeno.Locale

open MvPolynomial Finset

/-- I fattori del problema locale. -/
inductive Factor
  | Z (b : ℕ)
  | N (a : ℕ)
  deriving DecidableEq

namespace Factor

/-- La taglia del blocco. -/
def s : Factor → ℕ
  | Z b => 2 * 2 ^ b - 1
  | N a => 2 * 2 ^ a

/-- L'esponente della componente di "tutte accese". -/
def j : Factor → ℕ
  | Z b => 2 ^ b - 1
  | N a => 2 ^ a

/-- Il livello. -/
def level : Factor → ℕ
  | Z b => b
  | N a => a + 1

/-- Il dimezzamento del Lemma D. -/
def half : Factor → Factor
  | Z 0 => Z 0
  | Z (b + 1) => Z b
  | N 0 => Z 0
  | N (a + 1) => N a

/-- La parità dell'esponente `j` (serve al dimezzamento). -/
def par : Factor → ℕ
  | Z 0 => 0
  | Z (_ + 1) => 1
  | N 0 => 1
  | N (_ + 1) => 0

lemma one_le_s : ∀ x : Factor, 1 ≤ x.s
  | Z b => by
      have : 0 < 2 ^ b := by positivity
      simp only [s]; omega
  | N a => by
      have : 0 < 2 ^ a := by positivity
      simp only [s]; omega

lemma j_half : ∀ x : Factor, x.j = 2 * x.half.j + x.par
  | Z 0 => rfl
  | Z (b + 1) => by
      have : 0 < 2 ^ b := by positivity
      simp only [j, half, par, pow_succ]; omega
  | N 0 => rfl
  | N (a + 1) => by simp only [j, half, par, pow_succ]; omega

lemma s_le_half : ∀ x : Factor, x.s ≤ 2 * x.half.s + x.par
  | Z 0 => by simp [s, half, par]
  | Z (b + 1) => by
      have : 0 < 2 ^ b := by positivity
      simp only [s, half, par, pow_succ]; omega
  | N 0 => by simp [s, half, par]
  | N (a + 1) => by simp only [s, half, par, pow_succ]; omega

lemma half_eq_N_iff (x : Factor) (a : ℕ) : x.half = N a ↔ x = N (a + 1) := by
  cases x with
  | Z b => cases b <;> simp [half]
  | N a' => cases a' <;> simp [half]

lemma half_eq_Z_iff (x : Factor) (b : ℕ) (hb : 1 ≤ b) : x.half = Z b ↔ x = Z (b + 1) := by
  cases x with
  | Z b' => cases b' <;> simp [half] <;> omega
  | N a' => cases a' <;> simp [half] <;> omega

end Factor

open Factor

/-- L'ideale `(X_i ^ s_i)`. -/
noncomputable def I (F : Type*) [Field F] {ι : Type*} (f : ι → Factor) : Ideal (MvPolynomial ι F) :=
  Ideal.span (Set.range fun i => (X i ^ (f i).s : MvPolynomial ι F))

/-- La componente di "tutte accese": `c = ∏ X_i ^ j_i`. -/
noncomputable def cc (F : Type*) [Field F] {ι : Type*} [Fintype ι] (f : ι → Factor) : MvPolynomial ι F :=
  ∏ i, X i ^ (f i).j

/-- Il monomio di vertice `∏ X_i ^ (s_i - 1)`. -/
noncomputable def top (F : Type*) [Field F] {ι : Type*} [Fintype ι] (f : ι → Factor) : MvPolynomial ι F :=
  ∏ i, X i ^ ((f i).s - 1)

/-- L'operatore del vicinato edge: `u = ∑ X_i`. -/
noncomputable def uE (F : Type*) [Field F] (ι : Type*) [Fintype ι] : MvPolynomial ι F := ∑ i, X i

/-- L'operatore del vicinato king: `u = ∏ (1 + X_i) - 1`. -/
noncomputable def uK (F : Type*) [Field F] (ι : Type*) [Fintype ι] : MvPolynomial ι F := ∏ i, (1 + X i) - 1

/-- L'istanza è raggiungibile: `c ∈ u · L`. -/
def Reach {F : Type*} [Field F] {ι : Type*} [Fintype ι] (f : ι → Factor)
    (u : MvPolynomial ι F) : Prop :=
  ∃ y : MvPolynomial ι F, cc F f - u * y ∈ I F f

/-- Un testimone di non raggiungibilità: `u k = 0` e `c k = monomio di vertice` in `L`. -/
def Witness {F : Type*} [Field F] {ι : Type*} [Fintype ι] (f : ι → Factor)
    (u : MvPolynomial ι F) : Prop :=
  ∃ k : MvPolynomial ι F, u * k ∈ I F f ∧ cc F f * k - top F f ∈ I F f

/-- Il livello `ℓ` è "buono": contiene un fattore `N`, o un numero dispari di fattori `Z`. -/
def Good {ι : Type*} [Fintype ι] (f : ι → Factor) (ℓ : ℕ) : Prop :=
  (∃ i, f i = N (ℓ - 1)) ∨ Odd (univ.filter (fun i => f i = Z ℓ)).card

/-- La condizione del teorema locale: qualche livello `≥ 1` è buono. -/
def Cond {ι : Type*} [Fintype ι] (f : ι → Factor) : Prop := ∃ ℓ, 1 ≤ ℓ ∧ Good f ℓ

/-- L'istanza con i fattori di `B` resi banali. -/
def triv {ι : Type*} [DecidableEq ι] (f : ι → Factor) (B : Finset ι) : ι → Factor :=
  fun i => if i ∈ B then Z 0 else f i

/-- La sostituzione che manda a zero le variabili di `B`. -/
noncomputable def sig (F : Type*) [Field F] {ι : Type*} [DecidableEq ι] (B : Finset ι) :
    MvPolynomial ι F →ₐ[F] MvPolynomial ι F :=
  aeval fun i => if i ∈ B then 0 else X i

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma X_pow_mem (f : ι → Factor) (i : ι) : (X i ^ (f i).s : MvPolynomial ι F) ∈ I F f :=
  Ideal.subset_span ⟨i, rfl⟩

lemma X_pow_mem_of_le (f : ι → Factor) (i : ι) {n : ℕ} (h : (f i).s ≤ n) :
    (X i ^ n : MvPolynomial ι F) ∈ I F f := by
  rw [← Nat.add_sub_cancel' h, pow_add]
  exact Ideal.mul_mem_right _ _ (X_pow_mem f i)

/-- Il monomio di vertice non sta nell'ideale. -/
lemma top_not_mem (f : ι → Factor) : top F f ∉ I F f := by
  intro h
  have hI : I F f = Ideal.span ((fun m => monomial m (1 : F)) ''
      Set.range (fun i => Finsupp.single i (f i).s)) := by
    unfold I
    rw [← Set.range_comp]
    congr 1
    ext p
    simp [X_pow_eq_monomial]
  have htop : top F f = monomial (∑ i, Finsupp.single i ((f i).s - 1)) 1 := by
    rw [monomial_sum_one]
    simp [top, X_pow_eq_monomial]
  rw [hI, htop, mem_ideal_span_monomial_image] at h
  have hm : (∑ i, Finsupp.single i ((f i).s - 1)) ∈
      (monomial (∑ i, Finsupp.single i ((f i).s - 1)) (1 : F)).support := by
    simp [mem_support_iff, coeff_monomial]
  obtain ⟨_, ⟨i, rfl⟩, hle⟩ := h _ hm
  have hi := hle i
  rw [Finsupp.single_eq_same, Finsupp.finset_sum_apply] at hi
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hi
  have := Factor.one_le_s (f i)
  omega

/-- Un testimone esclude la raggiungibilità. -/
lemma not_reach_of_witness {f : ι → Factor} {u : MvPolynomial ι F} (hw : Witness f u) :
    ¬ Reach f u := by
  rintro ⟨y, hy⟩
  obtain ⟨k, hk1, hk2⟩ := hw
  apply top_not_mem (F := F) f
  have e : top F f = -(cc F f * k - top F f) + (cc F f - u * y) * k + y * (u * k) := by ring
  rw [e]
  exact add_mem (add_mem (neg_mem hk2) (Ideal.mul_mem_right _ _ hy)) (Ideal.mul_mem_left _ _ hk1)

lemma two_eq_zero_alg [CharP F 2] (A : Type*) [CommRing A] [Algebra F A] : (2 : A) = 0 := by
  have h : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have : (2 : A) = algebraMap F A 2 := (map_ofNat (algebraMap F A) 2).symm
  rw [this, h, map_zero]

lemma reach_iff_mk (f : ι → Factor) (u : MvPolynomial ι F) :
    Reach f u ↔ ∃ y : MvPolynomial ι F ⧸ I F f,
      Ideal.Quotient.mk (I F f) (cc F f) = Ideal.Quotient.mk (I F f) u * y := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Ideal.Quotient.mk _ y, ?_⟩
    rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hy
  · rintro ⟨y, hy⟩
    obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨y', ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, sub_self]

lemma mk_X_pow (f : ι → Factor) (i : ι) {n : ℕ} (h : (f i).s ≤ n) :
    Ideal.Quotient.mk (I F f) (X i ^ n) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (X_pow_mem_of_le f i h)

/-! ### Rendere banali alcuni fattori -/

lemma sig_X (B : Finset ι) (i : ι) :
    sig F B (X i) = if i ∈ B then 0 else X i := by
  simp [sig]

lemma map_sig_I (f : ι → Factor) (B : Finset ι) {p : MvPolynomial ι F}
    (hp : p ∈ I F (triv f B)) : sig F B p ∈ I F f := by
  have : I F (triv f B) ≤ Ideal.comap (sig F B) (I F f) := by
    unfold I
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, sig_X, triv]
    split_ifs with hi
    · simp [Factor.s]
    · exact X_pow_mem f i
  exact this hp

lemma cc_triv (f : ι → Factor) (B : Finset ι) :
    cc F (triv f B) = ∏ i ∈ univ.filter (· ∉ B), X i ^ (f i).j := by
  have : cc F (triv f B) = ∏ i, (if i ∈ B then 1 else (X i ^ (f i).j : MvPolynomial ι F)) :=
    prod_congr rfl fun i _ => by by_cases h : i ∈ B <;> simp [triv, h, Factor.j]
  rw [this, prod_ite]
  simp

lemma top_triv (f : ι → Factor) (B : Finset ι) :
    top F (triv f B) = ∏ i ∈ univ.filter (· ∉ B), X i ^ ((f i).s - 1) := by
  have : top F (triv f B) =
      ∏ i, (if i ∈ B then 1 else (X i ^ ((f i).s - 1) : MvPolynomial ι F)) :=
    prod_congr rfl fun i _ => by by_cases h : i ∈ B <;> simp [triv, h, Factor.s]
  rw [this, prod_ite]
  simp

lemma filter_mem_univ (B : Finset ι) : univ.filter (· ∈ B) = B := by
  ext; simp

lemma cc_split (f : ι → Factor) (B : Finset ι) :
    cc F f = (∏ i ∈ B, X i ^ (f i).j) * cc F (triv f B) := by
  rw [cc_triv, cc, ← prod_filter_mul_prod_filter_not univ (· ∈ B), filter_mem_univ]

lemma top_split (f : ι → Factor) (B : Finset ι) :
    top F f = (∏ i ∈ B, X i ^ ((f i).s - 1)) * top F (triv f B) := by
  rw [top_triv, top, ← prod_filter_mul_prod_filter_not univ (· ∈ B), filter_mem_univ]

lemma uE_split (B : Finset ι) :
    uE F ι = ∑ i ∈ B, X i + ∑ i ∈ univ.filter (· ∉ B), X i := by
  rw [uE, ← sum_filter_add_sum_filter_not univ (· ∈ B), filter_mem_univ]

lemma sig_cc (f : ι → Factor) (B : Finset ι) :
    sig F B (cc F (triv f B)) = cc F (triv f B) := by
  rw [cc_triv, map_prod]
  refine prod_congr rfl fun i hi => ?_
  have hi' : i ∉ B := by simpa using hi
  simp [sig_X, hi']

lemma sig_top (f : ι → Factor) (B : Finset ι) :
    sig F B (top F (triv f B)) = top F (triv f B) := by
  rw [top_triv, map_prod]
  refine prod_congr rfl fun i hi => ?_
  have hi' : i ∉ B := by simpa using hi
  simp [sig_X, hi']

lemma sig_uE (B : Finset ι) :
    sig F B (uE F ι) = ∑ i ∈ univ.filter (· ∉ B), X i := by
  rw [uE, map_sum, sum_filter]
  exact sum_congr rfl fun i _ => by by_cases h : i ∈ B <;> simp [sig_X, h]

/-- Se l'istanza con `B` banale è raggiungibile, lo è anche dentro l'anello di `f`, con
l'operatore ristretto alle variabili fuori da `B`. -/
lemma lift_reach {f : ι → Factor} {B : Finset ι} (h : Reach (triv f B) (uE F ι)) :
    ∃ y : MvPolynomial ι F,
      cc F (triv f B) - (∑ i ∈ univ.filter (· ∉ B), X i) * y ∈ I F f := by
  obtain ⟨y, hy⟩ := h
  refine ⟨sig F B y, ?_⟩
  have := map_sig_I f B hy
  rwa [map_sub, map_mul, sig_cc, sig_uE] at this

end SigmaMeno.Locale
