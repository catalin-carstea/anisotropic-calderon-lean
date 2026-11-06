import Mathlib.Tactic

set_option autoImplicit false
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
lemma eq_add_of_eq_add_add_zero {x p d z : ℝ}
    (h : x=p+(d+z)) (hz : z=0) : x=p+d := by
  exact h.trans ((congrArg (fun t : ℝ => p+(d+t)) hz).trans (congrArg (fun t : ℝ => p+t) (add_zero d)))

lemma eq_add_add_of_eq_add_add_of_eq {x p d m e : ℝ}
    (h : x=p+(d+m)) (hd : d=e) : x=p+(e+m) :=
  h.trans (congrArg (fun t : ℝ => p+(t+m)) hd)

lemma eq_adjoint_energy_of_principal_drift_mass
    (f fT fP fO fM eP eT eO eA d : ℝ)
    (hSum : f=fT+(fP-fO)+fM) (hP : fP=eP) (hPT : fT=eT)
    (hO : fO=eO) (hOrig : eO=eP+d) (hAdj : eA=eT+(-d+fM)) : f=eA := by
  linarith

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eq_add_of_eq_add_add_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eq_add_add_of_eq_add_add_of_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eq_adjoint_energy_of_principal_drift_mass
