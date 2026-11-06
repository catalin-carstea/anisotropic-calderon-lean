import Calderon.ActualReferenceGaugeFiveHalfConormalDensity
import Calderon.ActualMixedKernelNativeH3Datum

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint

/-- H5/2 density from the SAME smooth global kernel extension and H4 pullback. -/
def nativeMixedKernelHighDensityFiveHalf
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (v : ℝ × (R3 × ℝ)) : SphereSobolev (5/2 : ℝ) :=
  referencePhysicalGaugeConormalDensityFiveHalf S.g1 S.g1_admissible L
    P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    hcalc hF hO hD τ0
    (nativeMixedKernelPullbackHkDatum S L P Gext hG 4) v

/-- The high density includes exactly to the already used native density,
for the same Gext, packet and point. -/
theorem sphereSobolevInclusionL_nativeMixedKernelHighDensityFiveHalf
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (v : ℝ × (R3 × ℝ)) :
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (nativeMixedKernelHighDensityFiveHalf hcalc hF hO hD τ0 S L P Gext hG v) =
    nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L P Gext hG v := by
  let E4 := nativeMixedKernelPullbackHkDatum S L P Gext hG 4
  have hLow (q : ℝ × (R3 × ℝ)) : TauCeti.Wkp.lowerOrder 3 (E4 q) =
      nativeMixedKernelPullbackHkDatum S L P Gext hG 3 q := by
    change TauCeti.Wkp.lowerOrder 3
      (smoothBallSobolev 4 (nativeMixedKernelPullbackDatum S L P Gext hG q)) =
      smoothBallSobolev 3 (nativeMixedKernelPullbackDatum S L P Gext hG q)
    exact lowerOrder_smoothBallSobolev 3 _
  have hCore := sphereSobolevInclusionL_referencePhysicalGaugeConormalDensityFiveHalf
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    hcalc hreg hF hO hD τ0 E4 v
  simpa only [nativeMixedKernelHighDensityFiveHalf,nativeMixedKernelHighDensity,
    hLow,E4] using hCore

/-- Smooth base/parameter dependence of the same H5/2 native density. -/
theorem contDiff_nativeMixedKernelHighDensityFiveHalf
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext) :
    ContDiff ℝ ∞ (nativeMixedKernelHighDensityFiveHalf hcalc hF hO hD τ0 S L P Gext hG) := by
  have hE := contDiff_nativeMixedKernelPullbackHkDatum hcalc S L P Gext hG 4
  have hDens := contDiffOn_referencePhysicalGaugeConormalDensityFiveHalf
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    hcalc hreg hF hO hD τ0 (nativeMixedKernelPullbackHkDatum S L P Gext hG 4)
    Set.univ hE.contDiffOn
  exact contDiffOn_univ.mp hDens

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
