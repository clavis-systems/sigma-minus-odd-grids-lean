import SigmaMeno.Certificato

/-!
# Il caso d = 1 (il cammino), dimostrato per ogni lato dispari

In dimensione 1 i due vicinati coincidono: le vicine di `t` sono `t - 1` e `t + 1`.
Teorema: per `n` dispari, tutte accese è raggiungibile ⇔ `n % 4 = 3` ⇔ `Condition3`.

Prova con due vettori espliciti:
* se `n % 4 = 3`, si premono le celle `t` con `t % 4 ∈ {1, 2}`;
* se `n % 4 = 1`, il vettore `k` (uno sulle celle pari) ha `A·k = 0` e somma `(n+1)/2`, dispari:
  è un certificato di non raggiungibilità (`Certificato.lean`).
-/

namespace SigmaMeno

open Finset

lemma natAbs_sub_eq_one_iff (t s : ℕ) :
    (((t : ℤ) - (s : ℤ)).natAbs = 1) ↔ (s = t + 1 ∨ s + 1 = t) := by
  rw [Int.natAbs_eq_iff]
  push_cast
  omega

lemma natAbs_sub_le_one_iff (t s : ℕ) :
    (((t : ℤ) - (s : ℤ)).natAbs ≤ 1) ↔ (s ≤ t + 1 ∧ t ≤ s + 1) := by
  have h : (((t : ℤ) - (s : ℤ)).natAbs ≤ 1) ↔ |(t : ℤ) - (s : ℤ)| ≤ 1 := by
    rw [Int.abs_eq_natAbs]
    norm_cast
  rw [h, abs_le]
  omega

/-- Il vicinato edge è simmetrico, in ogni dimensione. -/
lemma edgeAdj_symm {d : ℕ} {n : Fin d → ℕ} (ξ η : Cell n) : EdgeAdj ξ η → EdgeAdj η ξ := by
  rintro ⟨i, h, hj⟩
  refine ⟨i, ?_, fun j hji => (hj j hji).symm⟩
  rw [natAbs_sub_eq_one_iff] at h ⊢
  omega

/-- Somma sulle vicine nel cammino `0, …, n-1`. -/
lemma path_sum (n t : ℕ) (g : ℕ → ZMod 2) :
    ∑ s ∈ range n, (if (((t : ℤ) - (s : ℤ)).natAbs = 1) then g s else 0)
      = (if t + 1 < n then g (t + 1) else 0)
        + (if 0 < t then (if t - 1 < n then g (t - 1) else 0) else 0) := by
  have hpt : ∀ s : ℕ, (if (((t : ℤ) - (s : ℤ)).natAbs = 1) then g s else 0)
      = (if s = t + 1 then g s else 0)
        + (if 0 < t then (if s = t - 1 then g s else 0) else 0) := by
    intro s
    simp only [natAbs_sub_eq_one_iff]
    split_ifs <;> first | omega | simp
  rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_add_distrib]
  congr 1
  · simp [Finset.sum_ite_eq', Finset.mem_range]
  · by_cases ht : 0 < t
    · simp only [ht, ite_true]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_range]
    · simp [ht]

section DimensioneUno

variable {n : ℕ}

/-- In dimensione 1 le celle sono i numeri `0, …, n-1`. -/
lemma sum_cell_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ η : Cell (fun _ : Fin 1 => n), f (η 0 : ℕ) = ∑ s ∈ range n, f s := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ _ (fun η => rfl)

lemma edgeAdj_one (ξ η : Cell (fun _ : Fin 1 => n)) :
    EdgeAdj ξ η ↔ (((ξ 0 : ℕ) : ℤ) - ((η 0 : ℕ) : ℤ)).natAbs = 1 := by
  constructor
  · rintro ⟨i, h, -⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h
  · intro h
    exact ⟨0, h, fun j hj => absurd (Subsingleton.elim j 0) hj⟩

lemma kingAdj_one (ξ η : Cell (fun _ : Fin 1 => n)) :
    KingAdj ξ η ↔ (((ξ 0 : ℕ) : ℤ) - ((η 0 : ℕ) : ℤ)).natAbs = 1 := by
  simp only [KingAdj, natAbs_sub_eq_one_iff, natAbs_sub_le_one_iff]
  constructor
  · rintro ⟨hne, hle⟩
    have h0 := hle 0
    have hne0 : (ξ 0 : ℕ) ≠ (η 0 : ℕ) := fun h => hne (funext fun i => by
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact Fin.ext h)
    omega
  · intro h
    refine ⟨fun he => ?_, fun i => ?_⟩
    · rw [he] at h
      omega
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      omega

lemma press_one {adj : Cell (fun _ : Fin 1 => n) → Cell (fun _ : Fin 1 => n) → Prop}
    [DecidableRel adj]
    (hadj : ∀ ξ η, adj ξ η ↔ (((ξ 0 : ℕ) : ℤ) - ((η 0 : ℕ) : ℤ)).natAbs = 1)
    (g : ℕ → ZMod 2) (ξ : Cell (fun _ : Fin 1 => n)) :
    press adj (fun η => g (η 0 : ℕ)) ξ
      = (if (ξ 0 : ℕ) + 1 < n then g ((ξ 0 : ℕ) + 1) else 0)
        + (if 0 < (ξ 0 : ℕ) then
            (if (ξ 0 : ℕ) - 1 < n then g ((ξ 0 : ℕ) - 1) else 0) else 0) := by
  rw [← path_sum]
  simp only [press, Finset.sum_filter, hadj]
  exact sum_cell_one (fun s => if (((ξ 0 : ℕ) : ℤ) - (s : ℤ)).natAbs = 1 then g s else 0)

/-- Le celle da premere quando `n % 4 = 3`. -/
def pat3 (t : ℕ) : ZMod 2 := if t % 4 = 1 ∨ t % 4 = 2 then 1 else 0

/-- Il certificato quando `n % 4 = 1`: uno sulle celle pari. -/
def ker1 (t : ℕ) : ZMod 2 := if t % 2 = 0 then 1 else 0

lemma sum_ker1 (m : ℕ) : ∑ s ∈ range m, ker1 s = (((m + 1) / 2 : ℕ) : ZMod 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, ker1]
    split_ifs with h
    · rw [show (m + 1 + 1) / 2 = (m + 1) / 2 + 1 by omega]
      push_cast
      ring
    · rw [show (m + 1 + 1) / 2 = (m + 1) / 2 by omega]
      simp

lemma reachable_one_of_mod3 {adj : Cell (fun _ : Fin 1 => n) → Cell (fun _ : Fin 1 => n) → Prop}
    [DecidableRel adj]
    (hadj : ∀ ξ η, adj ξ η ↔ (((ξ 0 : ℕ) : ℤ) - ((η 0 : ℕ) : ℤ)).natAbs = 1)
    (h3 : n % 4 = 3) : Reachable adj allOn := by
  refine ⟨fun η => pat3 (η 0 : ℕ), ?_⟩
  funext ξ
  rw [press_one hadj]
  have ht : (ξ 0 : ℕ) < n := (ξ 0).isLt
  simp only [allOn, pat3]
  generalize ((ξ 0 : ℕ)) = t at ht ⊢
  split_ifs <;> first | omega | decide

lemma not_reachable_one_of_mod1
    {adj : Cell (fun _ : Fin 1 => n) → Cell (fun _ : Fin 1 => n) → Prop} [DecidableRel adj]
    (hadj : ∀ ξ η, adj ξ η ↔ (((ξ 0 : ℕ) : ℤ) - ((η 0 : ℕ) : ℤ)).natAbs = 1)
    (h1 : n % 4 = 1) : ¬ Reachable adj allOn := by
  have hsymm : ∀ ξ η, adj ξ η → adj η ξ := by
    intro ξ η h
    rw [hadj, natAbs_sub_eq_one_iff] at h ⊢
    omega
  apply not_reachable_allOn_of_certificate adj hsymm (fun η => ker1 (η 0 : ℕ))
  · funext ξ
    rw [press_one hadj]
    have ht : (ξ 0 : ℕ) < n := (ξ 0).isLt
    simp only [Pi.zero_apply, ker1]
    generalize ((ξ 0 : ℕ)) = t at ht ⊢
    split_ifs <;> first | omega | decide
  · rw [sum_cell_one ker1, sum_ker1, ZMod.natCast_eq_one_iff_odd]
    exact ⟨(n + 1) / 4, by omega⟩

/-- Il cammino: per `n` dispari, tutte accese è raggiungibile ⇔ `n % 4 = 3`. -/
lemma path_iff {adj : Cell (fun _ : Fin 1 => n) → Cell (fun _ : Fin 1 => n) → Prop}
    [DecidableRel adj]
    (hadj : ∀ ξ η, adj ξ η ↔ (((ξ 0 : ℕ) : ℤ) - ((η 0 : ℕ) : ℤ)).natAbs = 1)
    (hn : Odd n) : Reachable adj allOn ↔ n % 4 = 3 := by
  by_cases h : n % 4 = 3
  · exact ⟨fun _ => h, fun _ => reachable_one_of_mod3 hadj h⟩
  · have h1 : n % 4 = 1 := by
      obtain ⟨m, rfl⟩ := hn
      omega
    exact ⟨fun hr => absurd hr (not_reachable_one_of_mod1 hadj h1), fun h' => absurd h' h⟩

end DimensioneUno

/-- La condizione 3 in dimensione 1: `a(n) ≥ 2`, cioè `n % 4 = 3`. -/
lemma condition3_one (m : ℕ) : Condition3 (fun _ : Fin 1 => m) ↔ m % 4 = 3 := by
  constructor
  · rintro ⟨k, hk, hodd⟩
    have hak : a m = k := by
      by_contra hne
      have hempty : (univ.filter (fun _ : Fin 1 => a m = k)) = ∅ := by
        simp [hne]
      rw [hempty] at hodd
      simp at hodd
    rw [← hak] at hk
    have h4 : 2 ^ 2 ∣ m + 1 := (padicValNat_dvd_iff_le (by omega)).2 hk
    norm_num at h4
    omega
  · intro h
    refine ⟨a m, ?_, ?_⟩
    · have h4 : 2 ^ 2 ∣ m + 1 := by
        norm_num
        omega
      exact (padicValNat_dvd_iff_le (by omega)).1 h4
    · simp

/-- **Il teorema principale nel caso d = 1**, parte (1) ⇔ (3), per entrambi i vicinati. -/
theorem teorema_dim_uno (n : Fin 1 → ℕ) (hn : ∀ i, Odd (n i)) :
    (Reachable (EdgeAdj (n := n)) allOn ↔ Condition3 n) ∧
    (Reachable (KingAdj (n := n)) allOn ↔ Condition3 n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = fun _ => m :=
    ⟨n 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hm : Odd m := hn 0
  rw [condition3_one]
  exact ⟨path_iff edgeAdj_one hm, path_iff kingAdj_one hm⟩

end SigmaMeno
