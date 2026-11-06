import Calderon.NativeH2CoefficientFluxGreen
import Calderon.NativeSmoothMultiplicationTrace
import Calderon.NativeCoordinateTraceVariation

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff Classical
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic

def coefficientSmoothData (F : SmoothCoefficientJets 2) : SmoothData :=
  ⟨coefficientValue 2 F,contDiff_coefficientValue 2 F⟩

lemma firstOrder_coefficientMultiplier_eq_contDiffSMulL
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 2)
    (u : BallSobolev 1) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coefficientSmoothData F).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coefficientSmoothData F).1 x‖ ≤ M) :
    TauCeti.Wkp.firstOrder 0 (coefficientMultiplier hcalc 1 F u) =
      TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
        (coefficientSmoothData F).1 (coefficientSmoothData F).2 hM hm hg (TauCeti.Wkp.firstOrder 0 u) := by
  rw [TauCeti.W1p.contDiffSMulL_apply]
  apply TauCeti.W1p.ext_value
  rw [TauCeti.Wkp.value_firstOrder]
  apply Lp.ext
  have hmul := TauCeti.W1p.value_contDiffSMul_ae (coefficientSmoothData F).2 hM hm hg
    (TauCeti.Wkp.firstOrder 0 u)
  rw [TauCeti.Wkp.value_firstOrder] at hmul
  filter_upwards [coefficientMultiplier_value_ae hcalc 1 F u,hmul] with x hL hR
  rw [hL,hR]
  rfl

lemma valueTraceL_firstOrder_coefficientMultiplier
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (u : BallSobolev 1) :
    τ0.valueTraceL (TauCeti.Wkp.firstOrder 0 (coefficientMultiplier hcalc 1 F u)) =
      sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F))
        (τ0.valueTraceL (TauCeti.Wkp.firstOrder 0 u)) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  rw [firstOrder_coefficientMultiplier_eq_contDiffSMulL hcalc F u hM hm hg]
  exact valueTraceL_contDiffSMulL τ0 (coefficientSmoothData F) hM hm hg _

lemma ordinaryConormalTraceL_eq_sphere_coefficient_trace
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2) :
    ordinaryConormalTraceL hcalc τ0 F U = ∑ i : Fin 3, ∑ j : Fin 3,
      sphereCoordinateMulL i (sphereContinuousScalarMulL
        (smoothSphereValue (coefficientSmoothData (F i j))) (strongCoordinateTraceL hcalc τ0 j U)) := by
  rw [ordinaryConormalTraceL_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [valueTraceL_firstOrder_coefficientMultiplier,strongCoordinateTraceL_apply]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientSmoothData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_coefficientMultiplier_eq_contDiffSMulL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.valueTraceL_firstOrder_coefficientMultiplier
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryConormalTraceL_eq_sphere_coefficient_trace
