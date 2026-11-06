import Calderon.ActualMixedKernelDensityPacketCoherence
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

def nativeMixedKernelHighDensityProfileDomain
    (S : KnownSideSourceData) (L delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L) : Set R3 :=
  (⋃ i : Fin cover.count, (cover.packet i).centers) ∩
    {y | referenceRadius delta Rstar p L y < cover.radiusCeiling}

/-- Choose a packet on the union of centers; the overlap theorem removes this
choice on the original radius-room domain. Outside the union the value is zero. -/
def nativeMixedKernelGluedHighDensityProfile
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext) (y : R3) : SphereSobolev (3/2 : ℝ) := by
  classical
  exact if h : ∃ i : Fin cover.count, y ∈ (cover.packet i).centers then
    nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet (Classical.choose h)) Gext hG
      (lam,(y,referenceRadius delta Rstar p L y)) else 0

lemma nativeMixedKernelGluedHighDensityProfile_eq_packet
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (i : Fin cover.count) (y : R3) (hy : y ∈ (cover.packet i).centers)
    (hRadius : referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    nativeMixedKernelGluedHighDensityProfile hcalc hF hO hD τ0 S L lam delta Rstar p cover Gext hG y =
      nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
        (lam,(y,referenceRadius delta Rstar p L y)) := by
  classical
  unfold nativeMixedKernelGluedHighDensityProfile
  split_ifs with h
  · exact nativeMixedKernelHighDensity_eq_on_overlap hcalc hF hO hD τ0 S L cover
      (Classical.choose h) i Gext hG lam hLam y ⟨Classical.choose_spec h,hy⟩
      (referenceRadius delta Rstar p L y)
      (referenceRadius_pos delta Rstar p L y hdelta hRstar) hRadius
  · exact False.elim (h ⟨i,hy⟩)

lemma isOpen_nativeMixedKernelHighDensityProfileDomain
    (S : KnownSideSourceData) (L delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar) :
    IsOpen (nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover) := by
  exact (isOpen_iUnion (fun i => (cover.packet i).centers_open)).inter
    (isOpen_lt (contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar).continuous
      continuous_const)

lemma cylinder_subset_nativeMixedKernelHighDensityProfileDomain
    (S : KnownSideSourceData) (L delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    cylinder ⊆ nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover := by
  intro y hy
  obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
  exact ⟨mem_iUnion.mpr ⟨i,hi⟩,hRadius y hy⟩

lemma contDiffOn_nativeMixedKernelGluedHighDensityProfile
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling) :
    ContDiffOn ℝ ∞
      (nativeMixedKernelGluedHighDensityProfile hcalc hF hO hD τ0 S L lam delta Rstar p cover Gext hG)
      (nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover) := by
  intro y hy
  obtain ⟨i,hi⟩ := mem_iUnion.mp hy.1
  have hU := isOpen_nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover hdelta hRstar
  have hEq : nativeMixedKernelGluedHighDensityProfile hcalc hF hO hD τ0 S L lam delta Rstar p cover Gext hG =ᶠ[𝓝 y]
      (fun y' => nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
        (lam,(y',referenceRadius delta Rstar p L y'))) := by
    filter_upwards [hU.mem_nhds hy,(cover.packet i).centers_open.mem_nhds hi] with y' hy' hi'
    exact nativeMixedKernelGluedHighDensityProfile_eq_packet hcalc hF hO hD τ0 S L lam delta Rstar p
      cover Gext hG hdelta hRstar hLam i y' hi' hy'.2
  exact ((contDiff_nativeMixedKernelHighDensity_profile hcalc hreg hF hO hD τ0 S L lam delta Rstar p
    (cover.packet i) Gext hG hdelta hRstar).contDiffAt.congr_of_eventuallyEq hEq).contDiffWithinAt

/-- ONE native high density, smooth on an open neighborhood of the entire
original cylinder and agreeing with every original packet wherever it applies. -/
theorem exists_smooth_nativeMixedKernelHighDensity_profile_on_neighborhood
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ (psi : R3 → SphereSobolev (3/2 : ℝ)) (U : Set R3), IsOpen U ∧ cylinder ⊆ U ∧
      ContDiffOn ℝ ∞ psi U ∧ ∀ i : Fin cover.count, ∀ y ∈ U ∩ (cover.packet i).centers,
        psi y = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
          (lam,(y,referenceRadius delta Rstar p L y)) := by
  refine ⟨nativeMixedKernelGluedHighDensityProfile hcalc hF hO hD τ0 S L lam delta Rstar p cover Gext hG,
    nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover,
    isOpen_nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover hdelta hRstar,
    cylinder_subset_nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover hRadius,
    contDiffOn_nativeMixedKernelGluedHighDensityProfile hcalc hreg hF hO hD τ0 S L lam delta Rstar p
      cover Gext hG hdelta hRstar hLam,?_⟩
  intro i y hy
  exact nativeMixedKernelGluedHighDensityProfile_eq_packet hcalc hF hO hD τ0 S L lam delta Rstar p
    cover Gext hG hdelta hRstar hLam i y hy.2 hy.1.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
