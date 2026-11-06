import Calderon.NativeH2OrthogonalPullbackExistence
import Calderon.NativeHalfTraceOrthogonalPullback
import Calderon.NativeFullHalfRadialTrace
import Calderon.SphereSobolevCoordinateOrthogonalCovariance
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeFullSharpHalfTrace NativeFullHalfRadialTrace

lemma continuousLinearMap_fin3_sum_smul_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) (c : Fin 3 → ℝ) (u : Fin 3 → V) :
    T (∑ i : Fin 3, c i • u i) = ∑ i : Fin 3, c i • T (u i) := by
  simp only [map_sum,map_smul]

lemma sum_sphereSobolevCoordinateMul_orthogonal_components
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : 0 ≤ s) (e : R3 ≃ₗᵢ[ℝ] R3) (v : Fin 3 → SphereSobolev s) :
    (∑ j : Fin 3, sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single j 1)
      (∑ i : Fin 3, (e (EuclideanSpace.single j 1)) i • sphereSobolevOrthogonalPullbackL s e (v i))) =
      sphereSobolevOrthogonalPullbackL s e
        (∑ i : Fin 3, sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1) (v i)) := by
  simp_rw [map_sum,map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact (sphereSobolevOrthogonalPullback_coordinateMul hF hO hD s hs e i (v i)).symm

lemma nativeHalfTrace_coordinateDerivative_nativeH2OrthogonalPullback
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (U : BallSobolev 2) (j : Fin 3) :
    nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 0
      (unitBallCoordinateDerivativeL hcalc 1 j (nativeH2OrthogonalPullback hcalc e U))) =
      ∑ i : Fin 3, (e (EuclideanSpace.single j 1)) i •
        sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e
          (nativeHalfTraceL hF hO hD τ0
            (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U))) := by
  have hg := continuousLinearMap_fin3_sum_smul_apply
    (V := BallH1) (W := SphereSobolev (1/2 : ℝ))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hg
  have hsum := hg (nativeHalfTraceL hF hO hD τ0)
    (fun i : Fin 3 => (e (EuclideanSpace.single j 1)) i)
    (fun i : Fin 3 => nativeH1OrthogonalPullback e
      (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U)))
  calc
    _ = nativeHalfTraceL hF hO hD τ0 (nativeH2OrthogonalDerivativeComponent hcalc e j U) :=
      congrArg (nativeHalfTraceL hF hO hD τ0)
        (coordinateDerivative_nativeH2OrthogonalPullback hcalc e U j)
    _ = ∑ i : Fin 3, (e (EuclideanSpace.single j 1)) i •
        nativeHalfTraceL hF hO hD τ0 (nativeH1OrthogonalPullback e
          (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U))) := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg ((e (EuclideanSpace.single j 1)) i • ·)
        (nativeHalfTraceL_nativeH1OrthogonalPullback hF hO hD τ0 e
          (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U)))

lemma nativeHalfOutwardTraceL_nativeH2OrthogonalPullback
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (U : BallSobolev 2) :
    nativeHalfOutwardTraceL hF hO hD hcalc τ0 (nativeH2OrthogonalPullback hcalc e U) =
      sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e
        (nativeHalfOutwardTraceL hF hO hD hcalc τ0 U) := by
  let v : Fin 3 → SphereSobolev (1/2 : ℝ) := fun i =>
    nativeHalfTraceL hF hO hD τ0
      (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U))
  calc
    _ = ∑ j : Fin 3, sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single j 1)
        (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 0
          (unitBallCoordinateDerivativeL hcalc 1 j (nativeH2OrthogonalPullback hcalc e U)))) :=
      nativeHalfOutwardTraceL_apply hF hO hD hcalc τ0 _
    _ = ∑ j : Fin 3, sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single j 1)
        (∑ i : Fin 3, (e (EuclideanSpace.single j 1)) i •
          sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e (v i)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single j 1))
        (nativeHalfTrace_coordinateDerivative_nativeH2OrthogonalPullback hF hO hD hcalc τ0 e U j)
    _ = sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e
        (∑ i : Fin 3, sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
          (EuclideanSpace.single i 1) (v i)) :=
      sum_sphereSobolevCoordinateMul_orthogonal_components hF hO hD (1/2 : ℝ) (by norm_num) e v
    _ = _ := congrArg (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e)
      (nativeHalfOutwardTraceL_apply hF hO hD hcalc τ0 U).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
