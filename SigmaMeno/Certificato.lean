import SigmaMeno.Enunciato

/-!
# Il certificato di non raggiungibilità

Se la relazione di vicinato è simmetrica e esiste `k` con `press adj k = 0` (cioè `A·k = 0`) e
somma dei `k` uguale a `1`, allora la configurazione tutte accese non è raggiungibile.
Motivo: se `A·w = 1`, allora `1 = Σ k·(A·w) = Σ w·(A·k) = 0`.
-/

namespace SigmaMeno

open Finset

/-- Lemma dei certificati: un vettore `k` del nucleo con somma `1` impedisce di accendere tutto. -/
theorem not_reachable_allOn_of_certificate {V : Type*} [Fintype V]
    (adj : V → V → Prop) [DecidableRel adj] (hsymm : ∀ ξ η, adj ξ η → adj η ξ)
    (k : V → ZMod 2) (hk : press adj k = 0) (hsum : ∑ ξ, k ξ = 1) :
    ¬ Reachable adj allOn := by
  rintro ⟨w, hw⟩
  have h1 : ∑ ξ, k ξ * press adj w ξ = 1 := by
    simp [hw, allOn, hsum]
  have h2 : ∑ ξ, k ξ * press adj w ξ = ∑ η, w η * press adj k η := by
    simp only [press, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun η _ => Finset.sum_congr rfl (fun ξ _ => ?_))
    by_cases h : adj ξ η
    · simp [h, hsymm _ _ h, mul_comm]
    · have h' : ¬ adj η ξ := fun h' => h (hsymm _ _ h')
      simp [h, h']
  have h3 : ∑ η, w η * press adj k η = 0 := by
    simp [hk]
  rw [h2, h3] at h1
  exact zero_ne_one h1

end SigmaMeno
