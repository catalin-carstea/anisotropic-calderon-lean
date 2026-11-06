import Calderon.ActualFactoryOneDilationReferenceBaseLift
import Calderon.ActualKernelBetaRadiusProfile

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ENNReal ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceWeightedApproximation SphereHarmonic DirichletFamily.DriftBootstrap
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift CoordinateBootstrapJets
  ExteriorSource.MetricCompatibleSourceJetAlgebra RadiusProfile WeightedBaseSpectral

/-- The native mixed-kernel provider and actual q=2 beta profile supply the
complete source parameter order for the source-matched one-dilation bootstrap.
The fixed-frame reference-base lift norm bound is a hypothesis, with D chosen after chi; no moving-fiber identity is used. -/
theorem exists_actual_factory_one_dilation_bootstrap_with_native_referenceBaseLift_profile
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
    (bound separation : ℝ) (hBound : 0 < bound) (hSeparation : 0 < separation) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∃ cover : NativeNormalCover S L,
    ∃ p0 : ℕ, 24 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧
    ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
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
          (∀ D : ℝ, 0 ≤ D → ∃ rho0 Cstar : ℝ, 0 < rho0 ∧ 0 < Cstar ∧
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
              let V : R3 → SphereL2 := fun z => chi z •
                (sphereSobolevZeroEquiv hO hD).symm
                  (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi z))
              ∀ hV : Continuous V, ∀ hVc : HasCompactSupport V,
                ‖referenceBaseLift S.g1 S.g1_admissible L lam V hV hVc‖ₑ ≤
                  ENNReal.ofReal D) →
          ∃ rho lam : ℝ, 0 < rho ∧ rho < rho0 ∧ 0 < lam ∧ lam ≤ eta ∧
            (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
              CurrentRadiusBootstrap S L lam delta Rstar eps p))) := by
  obtain ⟨L0,hL0,hLs⟩ :=
    exists_actual_kernel_beta_radius_profile_with_order
      S bound separation hBound hSeparation
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos : 0 < L := hL0.trans_le hL
  obtain ⟨cover,p0,hp0,hPs⟩ := hLs L hL
  refine ⟨cover,p0,hp0,?_⟩
  intro p hp
  have hp24 : 24 ≤ p := hp0.trans hp
  obtain ⟨eps0,heps0,heps01,hEps⟩ := hPs p hp
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps heps hepsCap
  obtain ⟨R0,hR0,hRs⟩ := hEps eps heps hepsCap
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRstar hRstarCap
  obtain ⟨etaKernel,hEtaKernel,hEtaKernelCover,hBeta,hRadius,hSeed⟩ :=
    hRs Rstar hRstar hRstarCap
  have hKK : ∀ lam : ℝ, 0 < lam → lam ≤ etaKernel →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        CurrentRadiusBootstrap S L lam delta Rstar eps p →
        Nonempty (ConstructedMixedKernel S L lam delta Rstar bound separation p cover) := by
    intro lam hlam hLamCap delta hdelta hdeltaOne hBoot
    obtain ⟨R,tail,Hseed,hR,hRRoom,hTail,hTailRoom,hSeedSolution,hDeltas⟩ :=
      hSeed lam hlam hLamCap
    obtain ⟨hRadiusRoom,KK,hKKRoom,hKKEq⟩ :=
      hDeltas delta hdelta hdeltaOne hBoot
    exact ⟨KK⟩
  exact exists_actual_factory_one_dilation_bootstrap_of_referenceBaseLift_bound
    hcalc hreg hF hO hD τ0 hKernel S hFirst hSecond hFree hMatch
    L Rstar eps cover p bound separation etaKernel
    hLpos hRstar heps hp24 hEtaKernel hBeta hRadius hKK

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
