import Calderon.ActualOriginalSourceMetricGeometry
import Calderon.MetricPullbackComposition

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource ConnectionError MetricVolume MetricOperator ConformalDepth

theorem originalSourcePacketMetricModel_eq_scaled_physical_pullback
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (lam : ℝ) (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    originalSourcePacketMetricModel S L (cover.packet i) lam y r z =
      lam^2 • pullbackMetric (fun x => S.g1 (lam • x))
        (packetEndpoint S L (cover.packet i) lam y r) z := by
  let P := cover.packet i
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩
  have hc : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hr : |r| ≤ 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact (hrceil.trans (cover.radius_room i)).le
  change originalSourcePacketMetricModel S L P lam y r z =
    lam^2 • pullbackMetric (fun x => S.g1 (lam • x))
      (fun x => referenceFramedPhysicalEndpoint S.g1 L P.Phi (lam,((y,r),x))) z
  rw [pullbackMetric_referenceOriginal_eq_conformal S.g1 S.g1_admissible L P.y0 P.Phi P.B
    P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data lam hq y hc r hr hrpos.ne' z hz]
  let t := referenceRescaledDepth S.g1 L P.Phi (lam,(y,r)) z
  have hExpLam : Real.exp (2*Real.log lam) = lam^2 := by
    rw [two_mul,Real.exp_add,Real.exp_log hlam,← pow_two]
  have hExp : Real.exp (2*(Real.log (lam*r)+L*t)) =
      lam^2 * Real.exp (2*(Real.log |r|+L*t)) := by
    rw [Real.log_mul hlam.ne' hrpos.ne',abs_of_pos hrpos]
    rw [show 2*(Real.log lam+Real.log r+L*t) =
      2*Real.log lam+2*(Real.log r+L*t) by ring,Real.exp_add,hExpLam]
  change Real.exp (2*(Real.log (lam*r)+L*t)) • P.H ((lam,(y,r)),z) = _
  rw [hExp,mul_smul]
  rfl

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
