import Calderon.ActualMixedKernelNativeFiveHalfPacketCoherence
import Calderon.ActualMixedKernelDensityProfileGluing

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint

/-- The five-half profile chooses a packet on the same open union of centers. -/
def nativeMixedKernelGluedFiveHalfDensityProfile
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext) (y : R3) : SphereSobolev (5/2 : ℝ) := by
  classical
  exact if h : ∃ i : Fin cover.count, y ∈ (cover.packet i).centers then
    nativeMixedKernelHighDensityFiveHalf hcalc hF hO hD τ0 S L (cover.packet (Classical.choose h))
      Gext hG (lam,(y,referenceRadius delta Rstar p L y)) else 0

lemma nativeMixedKernelGluedFiveHalfDensityProfile_eq_packet
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (i : Fin cover.count) (y : R3) (hy : y ∈ (cover.packet i).centers)
    (hRadius : referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    nativeMixedKernelGluedFiveHalfDensityProfile hcalc hF hO hD τ0 S L lam delta Rstar p cover Gext hG y =
      nativeMixedKernelHighDensityFiveHalf hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
        (lam,(y,referenceRadius delta Rstar p L y)) := by
  classical
  unfold nativeMixedKernelGluedFiveHalfDensityProfile
  split_ifs with h
  · exact nativeMixedKernelHighDensityFiveHalf_eq_on_overlap hcalc hreg hF hO hD τ0 S L cover
      (Classical.choose h) i Gext hG lam hLam y ⟨Classical.choose_spec h,hy⟩
      (referenceRadius delta Rstar p L y)
      (referenceRadius_pos delta Rstar p L y hdelta hRstar) hRadius
  · exact False.elim (h ⟨i,hy⟩)

lemma sphereSobolevInclusionL_nativeMixedKernelGluedFiveHalfDensityProfile
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext) (y : R3) :
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (nativeMixedKernelGluedFiveHalfDensityProfile hcalc hF hO hD τ0 S L lam delta Rstar p cover Gext hG y) =
    nativeMixedKernelGluedHighDensityProfile hcalc hF hO hD τ0 S L lam delta Rstar p cover Gext hG y := by
  classical
  unfold nativeMixedKernelGluedFiveHalfDensityProfile nativeMixedKernelGluedHighDensityProfile
  split_ifs with h
  · exact sphereSobolevInclusionL_nativeMixedKernelHighDensityFiveHalf
      hcalc hreg hF hO hD τ0 S L (cover.packet (Classical.choose h)) Gext hG
      (lam,(y,referenceRadius delta Rstar p L y))
  · exact map_zero _


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
