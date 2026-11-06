import Calderon.ActualKnownSidePoissonDensity
import Calderon.ActualNativeHarmonicTestDensityUniqueness

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError ConformalDepth ActualNormalizedSecondMetricDrift
attribute [local irreducible] referencePhysicalPoissonDensity

theorem any_eligible_native_density_eq_knownSidePoisson
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsiSmooth : ContDiff ℝ ∞ Psi) (hPsiCompact : HasCompactSupport Psi)
    (hFlux : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y) :
    ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      lam • y ∈ S.W → Psi y = referencePhysicalPoissonDensity S.g1 S.g1_admissible L
        (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
        (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        hcalc hF hO hD τ0 (lam,(y,referenceRadius delta Rstar p L y)) := by
  obtain ⟨PsiNorm,hPsiNormSmooth,hPsiNormCompact,hFluxNorm,hKnown,hPoisson,hPDE⟩ :=
    exists_original_global_native_density_knownSide_eq_fixedPoissonDensity
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  have hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  have hSame : ∀ y ∈ cylinder, PsiNorm y = Psi y := by
    intro y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
    have hrPos : 0 < referenceRadius delta Rstar p L y :=
      referenceRadius_pos delta Rstar p L y hdelta hRstar
    have hrCeil : referenceRadius delta Rstar p L y < cover.radiusCeiling :=
      hRadius y hy
    apply eq_of_nativeMixedKernelDensityFunctional_eq_on_actual_physical_harmonic_tests
      hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i hLam y hi
      hrPos hrCeil PsiNorm Psi
    intro V hV u hCover hPhysical
    have hBall : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y
            (referenceRadius delta Rstar p L y) z) = 0 := by
      intro z hz
      exact hPhysical _ (hCover ⟨z,ball_subset_closedBall hz,rfl⟩)
    exact (hFluxNorm i y ⟨hy,hi⟩ u hBall).trans
      (hFlux i y ⟨hy,hi⟩ u hBall).symm
  intro i y hy hKnownSide
  exact (hSame y hy.1).symm.trans (hPoisson i y hy hKnownSide)

theorem any_eligible_native_density_eventuallyEq_knownSidePoisson
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsiSmooth : ContDiff ℝ ∞ Psi) (hPsiCompact : HasCompactSupport Psi)
    (hFlux : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y)
    (i : Fin cover.count) (U : Set R3) (hU : IsOpen U)
    (hRoom : U ⊆ interior cylinder ∩ (cover.packet i).centers)
    (hKnown : ∀ z ∈ U, lam • z ∈ S.W) (y : R3) (hy : y ∈ U) :
    Psi =ᶠ[𝓝 y] (fun z => referencePhysicalPoissonDensity S.g1 S.g1_admissible L
        (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
        (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        hcalc hF hO hD τ0 (lam,(z,referenceRadius delta Rstar p L z))) := by
  have hEq := any_eligible_native_density_eq_knownSidePoisson
    hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius Psi hPsiSmooth hPsiCompact hFlux
  filter_upwards [hU.mem_nhds hy] with z hz
  exact hEq i z ⟨interior_subset (hRoom hz).1,(hRoom hz).2⟩ (hKnown z hz)

theorem fderiv_any_eligible_native_density_eq_knownSidePoisson
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsiSmooth : ContDiff ℝ ∞ Psi) (hPsiCompact : HasCompactSupport Psi)
    (hFlux : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y)
    (i : Fin cover.count) (U : Set R3) (hU : IsOpen U)
    (hRoom : U ⊆ interior cylinder ∩ (cover.packet i).centers)
    (hKnown : ∀ z ∈ U, lam • z ∈ S.W) (y : R3) (hy : y ∈ U) :
    fderiv ℝ Psi y = fderiv ℝ (fun z => referencePhysicalPoissonDensity S.g1 S.g1_admissible L
        (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
        (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        hcalc hF hO hD τ0 (lam,(z,referenceRadius delta Rstar p L z))) y := by
  exact ((any_eligible_native_density_eventuallyEq_knownSidePoisson
    hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius Psi hPsiSmooth hPsiCompact hFlux i U hU hRoom hKnown y hy).fderiv (𝕜 := ℝ)).self_of_nhds

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
