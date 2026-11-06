import Calderon.ActualFixedChartPhysicalHarmonicTransport
import Calderon.ActualMixedKernelKnownSideSource

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ConnectionError MetricOperator MetricVolume DirichletFamily.DriftBootstrap

theorem actual_packet_native_normalized_harmonic_of_physical
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling)
    (u : SmoothData)
    (hphysical : ∀ z ∈ ball (0 : R3) 1, coordinateFluxDivergence
      (metricDivergenceFlux (fun x => S.g1 (q • x)) u.1)
      (packetEndpoint S L (cover.packet i) q y r z) = 0) :
    ∀ z ∈ ball (0 : R3) 1, coordinateFluxDivergence (fun x => matrixOperatorMap
      (referencePhysicalNormalizedPrincipalCoefficient S.g1 L (cover.packet i).Phi
        (cover.packet i).H (q,(y,r)) x)
      (gradient (referencePhysicalPullbackData S.g1 S.g1_admissible L (cover.packet i).y0
        (cover.packet i).Phi (cover.packet i).B (cover.packet i).native_data.1.1.1 q y r u).1 x : R3)) z = 0 := by
  let P := cover.packet i
  have hq1 : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1,hq.2.trans cover.dilation_le_one⟩
  have hc : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hr : |r| ≤ 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact (hrceil.trans (cover.radius_room i)).le
  intro z hz
  have hz2 : z ∈ ball (0 : R3) 2 := ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz
  have hPositive := (referenceRescaledPositiveExpression_physical_pullback_zero_iff_on_doubleBall
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    q hq1 y hc r hr hrpos.ne' u z hz2).mpr (hphysical z hz)
  exact (coordinateFluxDivergence_referenceNormalizedCoefficient_zero_iff
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    q hq1 y hc r hr z (ball_subset_closedBall hz2)
    (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B P.native_data.1.1.1 q y r u)).mpr hPositive

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
