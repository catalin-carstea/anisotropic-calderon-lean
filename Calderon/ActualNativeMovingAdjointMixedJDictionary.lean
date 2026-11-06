import Calderon.ActualReferenceHighAdjointCoordinateZeroRaisingGraph
import Calderon.SphereSobolevAngularRaisingGraph
import Calderon.ActualNativeMovingAdjointCorrectionInclusion

/-! Upfront: actual-native-mixed-J-dictionary-author-oct16-v001/EXPANSION-v001.md.
Actual ordered mixed zero/first expression, same finite-J graph and bound. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic AngularShiftGraph
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointCoordinateBoundaryFamily
  sphereSobolevAngularCoordinateTransposeL referenceNativeMovingAdjointParametricCorrection
  referenceNativeMovingAdjointParametricJ referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint sphereSobolevInclusionL

lemma referenceHighAdjointCoordinateBoundaryFamily_zero_inclusion_one
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3) (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i u) =
      (sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) u)) := by
  let Z := sphereSobolevZeroEquiv hO hD
  let U := sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) u
  have hHigh := referenceHighAdjointCoordinateBoundaryFamily_zero_raisingGraph
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i u
  have hLow := sphereSobolevAngularCoordinateTransposeL_raisingGraph hF hO hD i U
  have hInput : sphereSobolevInclusionL 1 0 (by norm_num) U =
      sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) u := by
    have h := congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ]
      SphereSobolev 0 => T u)
        (sphereSobolevInclusionL_trans (3/2 : ℝ) 1 0 (by norm_num) (by norm_num))
    simpa (config := { instances := true }) only [ContinuousLinearMap.comp_apply,U] using h
  have hInputDecoded := congrArg Z.symm hInput
  have hLow' := (congrArg (fun v : SphereL2 =>
    (v,Z.symm (sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i U)) ∈ sphereRaisingGraph hF hO hD i) hInputDecoded).mp hLow
  exact Z.symm.injective
    (sphereRaisingGraph_output_unique hF hO hD i _ _ _ hHigh hLow')

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointCoordinateBoundaryFamily_zero_inclusion_one
