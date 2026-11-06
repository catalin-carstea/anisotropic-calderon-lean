import Calderon.ActualMixedKernelNativeFiveHalfDensity
import Calderon.ActualMixedKernelDensityPacketCoherence

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint

/-- Exact higher density coherence on packet overlaps for the SAME global
smooth kernel, obtained by injectivity of inclusion into the old density. -/
theorem nativeMixedKernelHighDensityFiveHalf_eq_on_overlap
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i j : Fin cover.count) (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers ∩ (cover.packet j).centers)
    (r : ℝ) (hr : 0 < r) (hrc : r < cover.radiusCeiling) :
    nativeMixedKernelHighDensityFiveHalf hcalc hF hO hD τ0 S L (cover.packet i)
      Gext hG (q,(y,r)) =
    nativeMixedKernelHighDensityFiveHalf hcalc hF hO hD τ0 S L (cover.packet j)
      Gext hG (q,(y,r)) := by
  apply sphereSobolevInclusionL_injective (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
  rw [sphereSobolevInclusionL_nativeMixedKernelHighDensityFiveHalf
      hcalc hreg hF hO hD τ0 S L (cover.packet i) Gext hG (q,(y,r)),
    sphereSobolevInclusionL_nativeMixedKernelHighDensityFiveHalf
      hcalc hreg hF hO hD τ0 S L (cover.packet j) Gext hG (q,(y,r))]
  exact nativeMixedKernelHighDensity_eq_on_overlap hcalc hF hO hD τ0 S L cover
    i j Gext hG q hq y hy r hr hrc

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
