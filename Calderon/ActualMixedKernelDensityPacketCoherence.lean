import Calderon.ActualMixedKernelDensityPacketLocality
import Calderon.ActualMixedKernelNativeH3Datum
import Calderon.ActualReferencePhysicalCoefficientNativeIdentity
import Calderon.ActualReferencePhysicalOrientation

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  MetricOperator MetricVolume NativeH3CoefficientConormalTrace
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint

attribute [local irreducible] nativeMixedKernelHighDensity referencePhysicalGaugeConormalDensity
  referencePhysicalGaugeCoefficientJets ordinaryPrincipalL nativePrincipalHarmonicConormalDensity
  nativeThreeHalfCoefficientConormalTraceL strongHarmonicProjectionL coefficientMultiplier

/-- Exact high-density coherence on overlaps for ONE global smooth kernel datum. -/
theorem nativeMixedKernelHighDensity_eq_on_overlap
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i j : Fin cover.count) (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers ∩ (cover.packet j).centers)
    (r : ℝ) (hr : 0 < r) (hrc : r < cover.radiusCeiling) :
    nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG (q,(y,r)) =
      nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet j) Gext hG (q,(y,r)) := by
  let F (i : Fin cover.count) : SmoothCoefficientMatrix 3 :=
    referencePhysicalGaugeCoefficientJets S.g1 S.g1_admissible L (cover.packet i).y0
      (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo
      (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w
      (cover.packet i).native_data 3 (q,(y,r))
  have hFG : ∀ m n, coefficientValue 3 (F i m n) =ᵐ[(volume : Measure R3).restrict ballOpens]
      coefficientValue 3 (F j m n) := fun m n =>
    coefficientValue_packet_eq_ae_on_overlap S L cover i j 3 m n q hq y hy r hr hrc
  have hA : ordinaryPrincipalL hcalc 1 (F i) = ordinaryPrincipalL hcalc 1 (F j) :=
    ordinaryPrincipalL_eq_of_coefficientValue_ae hcalc 1 (F i) (F j) hFG
  have hC : nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 (F i) =
      nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 (F j) :=
    nativeThreeHalfCoefficientConormalTraceL_eq_of_coefficientValue_ae hcalc hF hO hD τ0
      (F i) (F j) hFG
  have hE := nativeMixedKernelPullbackHkDatum_eq_on_overlap S L cover i j Gext hG 3
    q hq y hy r hr hrc
  unfold nativeMixedKernelHighDensity referencePhysicalGaugeConormalDensity
  change nativePrincipalHarmonicConormalDensity hcalc hF hO hD τ0 r (F i)
      (nativeMixedKernelPullbackHkDatum S L (cover.packet i) Gext hG 3 (q,(y,r))) =
    nativePrincipalHarmonicConormalDensity hcalc hF hO hD τ0 r (F j)
      (nativeMixedKernelPullbackHkDatum S L (cover.packet j) Gext hG 3 (q,(y,r)))
  unfold nativePrincipalHarmonicConormalDensity
  rw [hA,hC,hE]


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
