import Calderon.ActualSourceFreeCurrentRadiusBootstrap
import Calderon.ActualLocalFrontierOfCurrentBootstrap
import Calderon.ActualCutoffDensityRealBaseTransport

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

/-- The exact same cutoff and density field may be bounded in the fixed-frame
reference-base lift for sufficiently small dilations, with that positive
threshold chosen after the cutoff; the local frontier follows from all radii.
The lift bound is a hypothesis of this theorem. -/
theorem exists_actual_factory_one_dilation_local_frontier_of_referenceBaseLift_bound_with_small_dilation_cap_of_source_free_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData)
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
          (∀ etaDensity : ℝ, 0 < etaDensity → ∀ D : ℝ, 0 ≤ D → ∃ rho0 Cstar : ℝ, 0 < rho0 ∧ 0 < Cstar ∧
          ((∀ lam delta : ℝ,
            ∀ KK : ConstructedMixedKernel S L lam delta Rstar bound separation p cover,
            ∀ Psi : R3 → SphereSobolev (3/2 : ℝ),
              0 < lam → lam ≤ min eta etaDensity → 0 < delta → delta ≤ 1 →
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
          ∃ rho lam : ℝ, 0 < rho ∧ rho < rho0 ∧ 0 < lam ∧
            lam ≤ min eta etaDensity ∧
            ActualLocalFrontierOutcome S L lam Rstar eps p)) := by
  obtain ⟨A,hA,hTransport⟩ :=
    exists_uniform_cutoff_density_Euclidean_le_real_referenceBaseLift
      S.g1 S.g1_admissible L hO hD
  obtain ⟨eta,tb,hEta,hEtaCover,htb,hthree,hKcompact,hKinside,
    chi,hChi,hChiCompact,hRange,hSupport,W,hWopen,hKW,hWOne,hDerivSupport,
    hDensityResult⟩ :=
    exists_actual_factory_one_dilation_bootstrap_for_late_same_cutoff_density_bound_with_small_dilation_cap_of_source_free_room
      hcalc hreg hF hO hD τ0 hKernel S hFree hMatch
      L Rstar eps cover p bound separation etaKernel hL hRstar heps hp
      hEtaKernel hBeta hRadius hKK
  refine ⟨eta,tb,hEta,hEtaCover,htb,hthree,hKcompact,hKinside,
    chi,hChi,hChiCompact,hRange,hSupport,W,hWopen,hKW,hWOne,hDerivSupport,?_⟩
  intro etaDensity hEtaDensity D hD
  let B : ℝ := A*D
  have hB : 0 ≤ B := mul_nonneg hA hD
  obtain ⟨rho0,Cstar,hrho0,hCstar,hEuclidResult⟩ :=
    hDensityResult etaDensity hEtaDensity B hB
  refine ⟨rho0,Cstar,hrho0,hCstar,?_⟩
  intro hLift
  obtain ⟨rho,lam,hrho,hrho0,hlam,hlamEta,hAllBoot⟩ :=
    hEuclidResult (by
      intro lam delta KK Psi hlam hlamEta hdelta hdeltaOne hBoot hPsi hPsiCompact hIdentity
      have hLamIcc : lam ∈ Icc (0 : ℝ) 1 :=
        ⟨hlam.le, (hlamEta.trans (min_le_left _ _)).trans
          (hEtaCover.trans cover.dilation_le_one)⟩
      obtain ⟨hV,hVc,hFromLift⟩ :=
        hTransport lam hLamIcc chi hChi.continuous hChiCompact Psi hPsi
      exact hFromLift D hD
        (hLift lam delta KK Psi hlam hlamEta hdelta hdeltaOne hBoot
          hPsi hPsiCompact hIdentity hV hVc))
  exact ⟨rho,lam,hrho,hrho0,hlam,hlamEta,
    actual_local_frontier_of_all_current_radius_bootstrap
      S hFree hMatch L lam Rstar eps p hL hlam hRstar heps (by omega) hAllBoot⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
