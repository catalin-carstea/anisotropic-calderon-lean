import Calderon.NativePrincipalOperatorOrderCoherence
import Calderon.StrongHarmonicProjection

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge DirichletFamily

/-- The order-four strong harmonic correction lowers to the actual order-three
correction for the same coefficient values and same Sobolev datum. -/
theorem lowerOrder_strongHarmonicProjectionL_four_three
    (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 4) (G : SmoothCoefficientMatrix 3)
    (hFG : ∀ i j, coefficientValue 4 (F i j) = coefficientValue 3 (G i j))
    (hi4 : ((ordinaryPrincipalL hcalc 2 F).comp
      (strongDirichletSubmodule 2).toSubmodule.subtypeL).IsInvertible)
    (hi3 : ((ordinaryPrincipalL hcalc 1 G).comp
      (strongDirichletSubmodule 1).toSubmodule.subtypeL).IsInvertible)
    (E : BallSobolev 4) :
    TauCeti.Wkp.lowerOrder 3
      (strongHarmonicProjectionL 2 (ordinaryPrincipalL hcalc 2 F) E) =
    strongHarmonicProjectionL 1 (ordinaryPrincipalL hcalc 1 G)
      (TauCeti.Wkp.lowerOrder 3 E) := by
  let H := strongHarmonicProjectionL 2 (ordinaryPrincipalL hcalc 2 F) E
  have hHarm : ordinaryPrincipalL hcalc 1 G (TauCeti.Wkp.lowerOrder 3 H) = 0 := by
    exact ordinaryPrincipalL_lowerOrder_strongHarmonicProjectionL_eq_zero
      hcalc 1 F G hFG hi4 E
  have hHighSub : E-H ∈ strongDirichletSubmodule 2 :=
    sub_strongHarmonicProjectionL_mem 2 (ordinaryPrincipalL hcalc 2 F) E
  have hLowSub : TauCeti.Wkp.lowerOrder 3 E - TauCeti.Wkp.lowerOrder 3 H ∈
      strongDirichletSubmodule 1 := by
    change TauCeti.Wkp.lowerOrderL 3 E - TauCeti.Wkp.lowerOrderL 3 H ∈
      strongDirichletSubmodule 1
    rw [← map_sub]
    change TauCeti.Wkp.firstOrder 2 (TauCeti.Wkp.lowerOrder 3 (E-H)) ∈
      TauCeti.w1p0Submodule volume ballOpens 2
    rw [← TauCeti.Wkp.firstOrder_succ 2 (E-H)]
    exact hHighSub
  exact (strongHarmonicProjectionL_eq_of_sub_mem 1 (ordinaryPrincipalL hcalc 1 G)
    hi3 (TauCeti.Wkp.lowerOrder 3 E) (TauCeti.Wkp.lowerOrder 3 H)
    hHarm hLowSub).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
