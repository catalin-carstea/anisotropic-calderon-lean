import Calderon.ActualMixedKernelFiveHalfDensityProfileAlgebra

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint

attribute [local irreducible] nativeMixedKernelHighDensityFiveHalf
  nativeMixedKernelPullbackHkDatum referencePhysicalGaugeConormalDensityFiveHalf
  referencePhysicalGaugeCoefficientJets

private lemma contDiff_nativeMixedKernelHighDensityFiveHalf_profile
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (P : NativeNormalPacket S L) (Gext : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ Gext) (hdelta : 0 < delta) (hRstar : 0 < Rstar) :
    ContDiff ℝ ∞ (fun y => nativeMixedKernelHighDensityFiveHalf hcalc hF hO hD τ0 S L P Gext hG
      (lam,(y,referenceRadius delta Rstar p L y))) := by
  have hDens : ContDiff ℝ ∞
      (nativeMixedKernelHighDensityFiveHalf hcalc hF hO hD τ0 S L P Gext hG) :=
    contDiff_nativeMixedKernelHighDensityFiveHalf hcalc hreg hF hO hD τ0 S L P Gext hG
  have hR : ContDiff ℝ ∞ (referenceRadius delta Rstar p L) :=
    contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar
  have hParam : ContDiff ℝ ∞ (fun y : R3 => (lam,(y,referenceRadius delta Rstar p L y))) :=
    contDiff_const.prodMk (contDiff_id.prodMk hR)
  exact hDens.comp hParam

lemma contDiffOn_nativeMixedKernelGluedFiveHalfDensityProfile
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling) :
    ContDiffOn ℝ ∞
      (nativeMixedKernelGluedFiveHalfDensityProfile hcalc hF hO hD τ0 S L lam delta Rstar p cover Gext hG)
      (nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover) := by
  intro y hy
  obtain ⟨i,hi⟩ := mem_iUnion.mp hy.1
  have hU := isOpen_nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover hdelta hRstar
  have hEq : nativeMixedKernelGluedFiveHalfDensityProfile hcalc hF hO hD τ0 S L lam delta Rstar p cover Gext hG =ᶠ[𝓝 y]
      (fun y' => nativeMixedKernelHighDensityFiveHalf hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
        (lam,(y',referenceRadius delta Rstar p L y'))) := by
    filter_upwards [hU.mem_nhds hy,(cover.packet i).centers_open.mem_nhds hi] with y' hy' hi'
    exact nativeMixedKernelGluedFiveHalfDensityProfile_eq_packet hcalc hreg hF hO hD τ0 S L lam delta Rstar p
      cover Gext hG hdelta hRstar hLam i y' hi' hy'.2
  exact ((contDiff_nativeMixedKernelHighDensityFiveHalf_profile hcalc hreg hF hO hD τ0 S L
    lam delta Rstar p (cover.packet i) Gext hG hdelta hRstar).contDiffAt.congr_of_eventuallyEq hEq).contDiffWithinAt

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
