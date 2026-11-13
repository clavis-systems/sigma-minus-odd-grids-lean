import SigmaMeno

/-! Check: which axioms the proved results use. Only the three standard axioms of Lean and
mathlib (`propext`, `Classical.choice`, `Quot.sound`) should appear: no `sorryAx`, and no added
axioms. Run it with `lake env lean Verifica.lean`. -/

#check @SigmaMeno.TeoremaPrincipale
#print axioms SigmaMeno.not_reachable_allOn_of_certificate
#print axioms SigmaMeno.teorema_dim_uno
#check @SigmaMeno.Locale.local_theorem_edge
#check @SigmaMeno.Locale.local_theorem_king
#print axioms SigmaMeno.Locale.local_theorem_edge
#print axioms SigmaMeno.Locale.local_theorem_king
#check @SigmaMeno.Globale.f_odd
#check @SigmaMeno.Globale.mult_data
#print axioms SigmaMeno.Globale.mult_data
#check @SigmaMeno.Globale.necessaria_edge
#check @SigmaMeno.Globale.necessaria_king
#print axioms SigmaMeno.Globale.necessaria_edge
#print axioms SigmaMeno.Globale.necessaria_king
#check @SigmaMeno.Globale.principale_edge
#check @SigmaMeno.Globale.principale_king
#print axioms SigmaMeno.Globale.principale_edge
#print axioms SigmaMeno.Globale.principale_king
-- The full main theorem: `TeoremaPrincipale` (Enunciato.lean) is proved.
example : SigmaMeno.TeoremaPrincipale := SigmaMeno.Globale.teorema_principale
#print axioms SigmaMeno.Globale.teorema_principale
