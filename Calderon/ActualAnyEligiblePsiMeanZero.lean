import Calderon.ActualNativeDensityFiberMean
import Calderon.ActualNativeHarmonicTestDensityUniqueness

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError ConformalDepth ActualNormalizedSecondMetricDrift

/-- Every eligible density representing the same constructed kernel inherits
the already proved constant normalization, for the original selected cutoff. -/
theorem sphereMean_any_eligible_native_density_and_cutoff_sub_one
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
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
    (chi : R3 → ℝ) (hchiSupp : tsupport chi ⊆ interior cylinder) :
    (∀ y ∈ cylinder, sphereMean ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))) = 1) ∧
    (∀ y : R3, sphereMean (chi y •
      ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)) -
          polynomialSphereL2 (C 1))) = 0) := by
  obtain ⟨PsiNorm,hPsiNormSmooth,hPsiNormCompact,hFluxNorm,hKnown,hPDE,hOperator,
      hNorm,hMeanNorm⟩ :=
    exists_global_native_density_operator_and_fiber_mean_one
      hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
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
  have hMean : ∀ y ∈ cylinder, sphereMean ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))) = 1 := by
    intro y hy
    rw [← hSame y hy]
    exact hMeanNorm y hy
  have hSupport : Function.support chi ⊆ cylinder := by
    intro y hy
    have ht : y ∈ tsupport chi := subset_tsupport chi hy
    exact interior_subset (hchiSupp ht)
  exact ⟨hMean,
    sphereMean_cutoff_native_density_sub_one_eq_zero hO hD Psi chi hSupport hMean⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
