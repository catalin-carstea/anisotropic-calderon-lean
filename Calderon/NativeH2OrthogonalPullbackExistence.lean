import Calderon.NativeH2CoordinateAssembly
import Calderon.NativeH2OrthogonalDerivativeComponents

/-! Expanded first in EXPANSION-native-H2-orthogonal-pullback-author-v001.json.
No second-order smooth density is used. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma nativeH2_firstOrder_injective :
    Function.Injective (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 1) := by
  intro U V h
  apply TauCeti.Wkp.ext 2
  simpa only [TauCeti.Wkp.value_firstOrder] using congrArg TauCeti.W1p.value h

lemma exists_nativeH2OrthogonalPullback
    (hcalc : FixedSobolevCalculus) (e : R3 ≃ₗᵢ[ℝ] R3) (U : BallSobolev 2) :
    ∃ V : BallSobolev 2, TauCeti.Wkp.firstOrder 1 V =
      nativeH1OrthogonalPullback e (TauCeti.Wkp.firstOrder 1 U) :=
  exists_nativeH2_of_coordinate_gradient_values
    (nativeH1OrthogonalPullback e (TauCeti.Wkp.firstOrder 1 U))
    (fun j => nativeH2OrthogonalDerivativeComponent hcalc e j U)
    (fun j => value_nativeH2OrthogonalDerivativeComponent hcalc e j U)

def nativeH2OrthogonalPullback
    (hcalc : FixedSobolevCalculus) (e : R3 ≃ₗᵢ[ℝ] R3) (U : BallSobolev 2) : BallSobolev 2 :=
  (exists_nativeH2OrthogonalPullback hcalc e U).choose

lemma firstOrder_nativeH2OrthogonalPullback
    (hcalc : FixedSobolevCalculus) (e : R3 ≃ₗᵢ[ℝ] R3) (U : BallSobolev 2) :
    TauCeti.Wkp.firstOrder 1 (nativeH2OrthogonalPullback hcalc e U) =
      nativeH1OrthogonalPullback e (TauCeti.Wkp.firstOrder 1 U) :=
  (exists_nativeH2OrthogonalPullback hcalc e U).choose_spec

lemma coordinateDerivative_nativeH2OrthogonalPullback
    (hcalc : FixedSobolevCalculus) (e : R3 ≃ₗᵢ[ℝ] R3) (U : BallSobolev 2) (j : Fin 3) :
    TauCeti.Wkp.firstOrder 0
      (unitBallCoordinateDerivativeL hcalc 1 j (nativeH2OrthogonalPullback hcalc e U)) =
      nativeH2OrthogonalDerivativeComponent hcalc e j U := by
  apply TauCeti.W1p.ext_value
  rw [TauCeti.Wkp.value_firstOrder,unitBallCoordinateDerivative_eq_coordinateGradient,
    firstOrder_nativeH2OrthogonalPullback]
  exact (value_nativeH2OrthogonalDerivativeComponent hcalc e j U).symm

lemma nativeH2OrthogonalPullback_symm_apply
    (hcalc : FixedSobolevCalculus) (e : R3 ≃ₗᵢ[ℝ] R3) (U : BallSobolev 2) :
    nativeH2OrthogonalPullback hcalc e.symm (nativeH2OrthogonalPullback hcalc e U) = U := by
  apply nativeH2_firstOrder_injective
  rw [firstOrder_nativeH2OrthogonalPullback,firstOrder_nativeH2OrthogonalPullback,
    nativeH1OrthogonalPullback_symm_apply]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2_firstOrder_injective
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeH2OrthogonalPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2OrthogonalPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_nativeH2OrthogonalPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateDerivative_nativeH2OrthogonalPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2OrthogonalPullback_symm_apply
