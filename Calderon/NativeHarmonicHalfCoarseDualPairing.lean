import Calderon.NativeHarmonicH1LiftTraceCompatibility
import Calderon.SphereSobolevPairing
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing
open SphereHarmonic SpectralWeightedGraph SpectralCoreRegularity EnergyBridge DirichletFamily
  NativeHarmonicH1LiftCompletion NativeHarmonicH1LiftTraceCompatibility

lemma sphereSobolevDualPairing_zero_inclusion (s : ℝ) (hs : 0 ≤ s)
    (u : SphereSobolev s) (v : SphereSobolev 0) :
    sphereSobolevDualPairing s u (sphereSobolevInclusionL 0 (-s) (neg_nonpos.mpr hs) v) =
      ⟪sphereSobolevInclusionL s 0 hs u,v⟫_ℝ := by
  rw [sphereSobolevDualPairing_eq_tsum,inner_sphereSobolev 0]
  simp only [sphereSobolevCoefficientL_inclusion,besselWeight_zero_order,one_pow,one_mul]

lemma sphereSobolevZeroEquiv_valueTrace_harmonicFirstOrderLift
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevZeroEquiv hO hD (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)) =
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) z := by
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_zeroEquiv,sphereSobolevCoefficientL_inclusion]
  exact sphereHarmonicCoordinate_valueTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0 k z

lemma sphereSobolevDualPairing_coarse_eq_halfLift_trace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (z : SphereSobolev (1/2:ℝ)) (b : SphereL2) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD b)) =
        ⟪b,τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)⟫_ℝ := by
  rw [sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num)]
  rw [← sphereSobolevZeroEquiv_valueTrace_harmonicFirstOrderLift hF hO hD τ0 z]
  exact ((sphereSobolevZeroEquiv hO hD).inner_map_map _ _).trans (real_inner_comm _ _)

end OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

#print axioms OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing.sphereSobolevDualPairing_zero_inclusion
#print axioms OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing.sphereSobolevZeroEquiv_valueTrace_harmonicFirstOrderLift
#print axioms OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing.sphereSobolevDualPairing_coarse_eq_halfLift_trace
