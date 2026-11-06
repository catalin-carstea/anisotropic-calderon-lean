import Calderon.ActualOriginalSourceMetricNativeEquation
import Calderon.ActualReferencePhysicalCoefficientNativeIdentity

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ConnectionError MetricVolume MetricOperator DirichletFamily.DriftBootstrap
  ExteriorSource SphereHarmonic ConformalDepth ReferenceWeightedApproximation

theorem original_source_model_principalCoefficient_eq_lambda_pullback
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (lam : ℝ) (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    principalCoefficient (originalSourcePacketMetricModel S L (cover.packet i) lam y r) z =
      lam • principalCoefficient (pullbackMetric (fun x => S.g1 (lam • x))
        (packetEndpoint S L (cover.packet i) lam y r)) z := by
  let P := cover.packet i
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩
  have hc : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hr : |r| ≤ 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact (hrceil.trans (cover.radius_room i)).le
  have hPhysical := principalCoefficient_referencePhysicalPullback_eq_pos_radius_smul_native
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    lam hq y hc r hr hrpos z hz
  have hA := nativePrincipal_eq_matrixPrincipal_on_doubleBall
    S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    lam hq y hc r hr z hz
  rw [hA] at hPhysical
  have hPhysicalB : principalCoefficient (pullbackMetric (fun x => S.g1 (lam • x))
      (packetEndpoint S L P lam y r)) z =
      r • referencePhysicalNormalizedPrincipalCoefficient S.g1 L P.Phi P.H (lam,(y,r)) z := by
    exact hPhysical
  rw [principalCoefficient_originalSourcePacketMetricModel S L P lam hlam y r hrpos z,
    hPhysicalB,mul_smul]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
