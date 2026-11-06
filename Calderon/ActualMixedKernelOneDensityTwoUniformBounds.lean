import Calderon.ActualMixedKernelConstructionWithUniformUpperDensity
import Calderon.ActualKnownSidePoissonDensity
import Calderon.ActualNativeHarmonicTestDensityUniqueness
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift NativePolynomialBulkMoments

/-- One SAME original constructed kernel and ONE global actual density carrying
both the known-side Poisson bound and the upper-coordinate annular bound. -/
def ActualMixedKernelOneDensityTwoUniformBoundsGoal
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) : Prop :=
  ∀ (S : KnownSideSourceData) (bound separation : ℝ), 0 < bound → 0 < separation →
  ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
  ∃ cover : NativeNormalCover S L,
  ∃ Clow : ℝ, 1 ≤ Clow ∧
  ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
  ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧
  ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
  ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
  ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ cover.dilationCeiling ∧
  ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
  ∃ B : ℝ, 0 ≤ B ∧
  ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
    CurrentRadiusBootstrap S L lam delta Rstar eps p →
    (∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
      referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
    ∃ K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover,
    ∃ Psi : R3 → SphereSobolev (3/2 : ℝ),
      (ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u y =
          nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
            y (referenceRadius delta Rstar p L y) y) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        lam • y ∈ S.W → ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi u y = u.1 y) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        lam • y ∈ S.W → Psi y = referencePhysicalPoissonDensity S.g1 S.g1_admissible L
          (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
          (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          hcalc hF hO hD τ0
          (lam,(y,referenceRadius delta Rstar p L y))) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        lam • y ∈ S.W → ‖Psi y‖ ≤ Clow ∧
          ‖Psi y - (sphereSobolevSingleL (3/2 : ℝ) 0 ⟨polynomialSphereL2 (MvPolynomial.C 1),polynomialSphereL2_mem 0 _ (C_harmonicHomogeneous 1)⟩)‖ ≤ Clow * referenceRadius delta Rstar p L y) ∧
      ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
          closedBall (0 : R3) 1 ⊆ V →
        (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
          ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u) Y ∧
          ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
            (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u) z = 0) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        (1/4 : ℝ) ≤ referenceCoordinateDepth y → ‖Psi y‖ ≤ B)

/-- The harmonic-test uniqueness theorem identifies the two profiles for the
same original K; the final witness is the known-side Poisson profile. -/
theorem actualMixedKernelOneDensityTwoUniformBoundsGoal_of_upper
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hUpper : ActualMixedKernelConstructionWithUniformUpperDensityGoal
      hcalc hreg hF hO hD τ0) :
    ActualMixedKernelOneDensityTwoUniformBoundsGoal hcalc hreg hF hO hD τ0 := by
  intro S bound separation hBound hSep
  obtain ⟨L0,hL0,hL⟩ := hUpper S bound separation hBound hSep
  refine ⟨L0,hL0,?_⟩
  intro L hLL0
  obtain ⟨cover,p0,hp0,hp⟩ := hL L hLL0
  obtain ⟨Clow,hClow,Hlow⟩ :=
    exists_original_global_native_density_knownSide_uniform_bound
      hcalc hreg hF hO hD τ0 S L cover
  refine ⟨cover,Clow,hClow,p0,hp0,?_⟩
  intro p hpp0
  obtain ⟨eps0,heps0,heps01,heps⟩ := hp p hpp0
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps hepsPos hepsSmall
  obtain ⟨R0,hR0,hRstar⟩ := heps eps hepsPos hepsSmall
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRs0
  obtain ⟨lam0,hlam0,hlamC,hlam⟩ := hRstar Rstar hRs hRs0
  refine ⟨lam0,hlam0,hlamC,?_⟩
  intro lam hlamPos hlamSmall
  obtain ⟨R,tail,a,b,Hseed,Hext,hHext,B,hR,hRoom,hTailA,ha,hb,hCompact,
      hGerm,hBnonneg,hSeedSol,hDelta⟩ := hlam lam hlamPos hlamSmall
  refine ⟨B,hBnonneg,?_⟩
  intro delta hdPos hdOne hBoot
  obtain ⟨hRadius,K,hKRoom,hKEq,PsiUpper,hPsiUpperSmooth,hPsiUpperCompact,
      hFluxUpper,hUpperBound⟩ := hDelta delta hdPos hdOne hBoot
  have hRadiusAt : ∀ y ∈ cylinder,
      referenceRadius delta Rstar p L y < cover.radiusCeiling :=
    hRadius delta ⟨le_rfl,hdOne⟩
  obtain ⟨PsiLow,hPsiLowSmooth,hPsiLowCompact,hFluxLow,hKnown,hPiEq,hLower,hPDE⟩ :=
    Hlow lam delta Rstar bound separation p K hdPos hRs hlamPos
      (hlamSmall.trans hlamC) hRadiusAt
  refine ⟨hRadius,K,PsiLow,⟨hPsiLowSmooth,hPsiLowCompact,hFluxLow,
    hKnown,hPiEq,hLower,hPDE⟩,?_⟩
  intro i y hy hCoord
  have hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling :=
    ⟨hlamPos.le,hlamSmall.trans hlamC⟩
  have hrPos : 0 < referenceRadius delta Rstar p L y :=
    referenceRadius_pos delta Rstar p L y hdPos hRs
  have hrCeil : referenceRadius delta Rstar p L y < cover.radiusCeiling :=
    hRadiusAt y hy.1
  have hSame : PsiLow y = PsiUpper y := by
    apply eq_of_nativeMixedKernelDensityFunctional_eq_on_actual_physical_harmonic_tests
      hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i hLam y hy.2
      hrPos hrCeil PsiLow PsiUpper
    intro V hV u hCover hPhysical
    have hBall : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y
            (referenceRadius delta Rstar p L y) z) = 0 := by
      intro z hz
      exact hPhysical _ (hCover ⟨z,ball_subset_closedBall hz,rfl⟩)
    exact (hFluxLow i y hy u hBall).trans (hFluxUpper i y hy u hBall).symm
  rw [hSame]
  exact hUpperBound i y hy hCoord

/-- Concrete joined density from both checked factories. -/
theorem actual_mixed_kernel_one_density_two_uniform_bounds
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ActualMixedKernelOneDensityTwoUniformBoundsGoal hcalc hreg hF hO hD τ0 :=
  actualMixedKernelOneDensityTwoUniformBoundsGoal_of_upper
    hcalc hreg hF hO hD τ0
    (actual_mixed_kernel_exists_with_uniform_upper_density hcalc hreg hF hO hD τ0)

/-- Erasing the additional density witnesses yields the exact original goal. -/
theorem actualMixedKernelConstructionGoal_of_one_density_two_uniform_bounds
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (h : ActualMixedKernelOneDensityTwoUniformBoundsGoal
      hcalc hreg hF hO hD τ0) : ActualMixedKernelConstructionGoal := by
  intro S bound separation hBound hSep
  obtain ⟨L0,hL0,hL⟩ := h S bound separation hBound hSep
  refine ⟨L0,hL0,?_⟩
  intro L hLL0
  obtain ⟨cover,Clow,hClow,p0,hp0,hp⟩ := hL L hLL0
  refine ⟨cover,p0,hp0,?_⟩
  intro p hpp0
  obtain ⟨eps0,heps0,heps01,heps⟩ := hp p hpp0
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps hepsPos hepsSmall
  obtain ⟨R0,hR0,hRstar⟩ := heps eps hepsPos hepsSmall
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRs0
  obtain ⟨lam0,hlam0,hlamC,hlam⟩ := hRstar Rstar hRs hRs0
  refine ⟨lam0,hlam0,hlamC,?_⟩
  intro lam hlamPos hlamSmall delta hdPos hdOne hBoot
  obtain ⟨B,hBnonneg,hDelta⟩ := hlam lam hlamPos hlamSmall
  obtain ⟨hRadius,K,Psi,hPsiContract,hUpper⟩ := hDelta delta hdPos hdOne hBoot
  exact ⟨hRadius,⟨K⟩⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
