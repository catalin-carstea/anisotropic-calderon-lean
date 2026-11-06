import Calderon.ActualFactoryMiddleSourceMatchedH8LateDensity
import Calderon.ActualOneDilationMiddleGeometry

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ENNReal ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceWeightedApproximation SphereHarmonic DirichletFamily.DriftBootstrap
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift CoordinateBootstrapJets
  ExteriorSource.MetricCompatibleSourceJetAlgebra RadiusProfile

/-- The actual source-matched five-source factory and one-dilation continuation
reduce the Section 06 bootstrap to the same-cutoff Euclidean angular density
bound for its exact mixed-kernel density-functional source. -/
theorem exists_actual_factory_one_dilation_bootstrap_for_late_same_cutoff_density_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData)
    (hFirst : ‖S.Xi1 0‖ ≤ 1) (hSecond : ‖S.Xi2 0‖ ≤ 1)
    (hFree : ∀ x ∈ S.coordinateRoom,
      S.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
      S.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3))
    (hMatch : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x))
    (L Rstar eps : ℝ) (cover : NativeNormalCover S L) (p : ℕ)
    (bound separation etaKernel : ℝ)
    (hL : 0 < L) (hRstar : 0 < Rstar) (heps : 0 < eps) (hp : 24 ≤ p)
    (hEtaKernel : 0 < etaKernel)
    (hBeta : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ y ∈ cylinder,
        referenceRadius delta Rstar p L y *
          (actualReferenceBeta S.g1 L lam delta Rstar p y)^2 ≤ eps)
    (hRadius : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (hKK : ∀ lam : ℝ, 0 < lam → lam ≤ etaKernel →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        CurrentRadiusBootstrap S L lam delta Rstar eps p →
        Nonempty (ConstructedMixedKernel S L lam delta Rstar bound separation p cover)) :
    ∃ eta tb : ℝ, 0 < eta ∧ eta ≤ cover.dilationCeiling ∧
      0 < tb ∧ 3 * tb < depthPrimitive L (1/8) (1/4) ∧
      let K : Set R3 := {y | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
        referenceDepth L y ≤ 2 * tb}
      IsCompact K ∧ K ⊆ interior cylinder ∧
      ∃ chi : R3 → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
        range chi ⊆ Icc 0 1 ∧ tsupport chi ⊆ interior cylinder ∧
        ∃ W : Set R3, IsOpen W ∧ K ⊆ W ∧
          (∀ z ∈ W, chi z = 1) ∧
          tsupport (fderiv ℝ chi) ⊆
            {z : R3 | z 2 < -(1/4 : ℝ)} ∪
              {z : R3 | tb < referenceDepth L z} ∧
          (∀ B : ℝ, 0 ≤ B → ∃ rho0 Cstar : ℝ, 0 < rho0 ∧ 0 < Cstar ∧
          ((∀ lam delta : ℝ,
            ∀ KK : ConstructedMixedKernel S L lam delta Rstar bound separation p cover,
            ∀ Psi : R3 → SphereSobolev (3/2 : ℝ),
              0 < lam → lam ≤ eta → 0 < delta → delta ≤ 1 →
              CurrentRadiusBootstrap S L lam delta Rstar eps p →
              ContDiff ℝ ∞ Psi → HasCompactSupport Psi →
              (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                ∀ u : SmoothData,
                (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
                  (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
                  (packetEndpoint S L (cover.packet i) lam y
                    (referenceRadius delta Rstar p L y) z) = 0) →
                nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
                  lam delta Rstar p Psi u y =
                  nativeMixedKernelWronskianFlux S L (cover.packet i) lam KK.kernel u.1
                    y (referenceRadius delta Rstar p L y) y) →
              eLpNorm (fun z : R3 => chi z •
                (sphereSobolevZeroEquiv hO hD).symm
                  (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi z)))
                2 (volume.restrict cylinder) ≤ ENNReal.ofReal B) →
          ∃ rho lam : ℝ, 0 < rho ∧ rho < rho0 ∧ 0 < lam ∧ lam ≤ eta ∧
            (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
              CurrentRadiusBootstrap S L lam delta Rstar eps p))) := by
  obtain ⟨s,etaF,C,tb,hEtaF,hEtaFCover,hC,htb,hthree,
    hKcompact,hKinside,chi,hChi,hChiCompact,hRange,hSupport,
    W,hWopen,hKW,hWOne,hDerivSupport,hFactoryLate⟩ :=
    exists_actual_factory_middle_source_matched_coordinateH8_le_three_halves_for_late_density_bound
      hcalc hreg hF hO hD τ0 hKernel S hFirst hSecond hFree hMatch
      L Rstar cover p hL hRstar hp
  let eta : ℝ := min etaF etaKernel
  have hEta : 0 < eta := lt_min hEtaF hEtaKernel
  have hEtaCover : eta ≤ cover.dilationCeiling :=
    (min_le_left _ _).trans hEtaFCover
  refine ⟨eta,tb,hEta,hEtaCover,htb,hthree,
    hKcompact,hKinside,chi,hChi,hChiCompact,hRange,hSupport,
    W,hWopen,hKW,hWOne,hDerivSupport,?_⟩
  intro B hB
  obtain ⟨rho0,Cstar,hrho0,hCstar,hGeometry,hFactory⟩ := hFactoryLate B hB
  refine ⟨rho0,Cstar,hrho0,hCstar,?_⟩
  intro hDensity
  have hGain : ∀ lam : ℝ, 0 < lam → lam ≤ eta →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        CurrentRadiusBootstrap S L lam delta Rstar eps p →
        ∀ y ∈ {y : R3 | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
          referenceDepth L y ≤ 2 * tb},
          referenceRadius delta Rstar p L y < rho0 →
          coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
            Cstar * (referenceRadius delta Rstar p L y)^(3/2 : ℝ) := by
    intro lam hlam hlamEta delta hdelta hdeltaOne hBoot y hy hr
    have hlamKernel : lam ≤ etaKernel := hlamEta.trans (min_le_right _ _)
    have hlamFactory : lam ≤ etaF := hlamEta.trans (min_le_left _ _)
    obtain ⟨KK⟩ := hKK lam hlam hlamKernel delta hdelta hdeltaOne hBoot
    obtain ⟨Psi,hPsiSmooth,hPsiCompact,hPsiIdentity,hPsiMoment,hPsiGain⟩ :=
      hFactory lam delta bound separation KK hlam hlamFactory hdelta
        (hRadius delta hdelta hdeltaOne)
    exact hPsiGain
      (hDensity lam delta KK Psi hlam hlamEta hdelta hdeltaOne hBoot
        hPsiSmooth hPsiCompact hPsiIdentity) y hy hr
  obtain ⟨rho,lam,hrho,hrho0',hChoice,hlam,hlamEta,
    hInitial,hOff,hImprove,hAll⟩ :=
    exists_one_dilation_current_radius_bootstrap_of_middle_three_halves
      S L Rstar eps Cstar rho0 tb eta p hL hRstar heps hCstar.le hrho0 htb
      hEta (hEtaCover.trans cover.dilation_le_one) hKcompact hBeta hGain
  exact ⟨rho,lam,hrho,hrho0',hlam,hlamEta,hAll⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
