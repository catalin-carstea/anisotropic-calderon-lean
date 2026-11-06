import Calderon.ActualFiveSourceRecoveryMomentPackage
import Calderon.ActualMiddleSourceMatchedH8MetricRecoveryLateDensity

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

/-- One actual five-test factory supplies the same renormalized sources to the
native moment, spatial smoothness, metric recovery, and Section 06 gain. The
angular density bound for its actual Psi stays explicit. -/
theorem exists_actual_factory_middle_source_matched_coordinateH8_le_three_halves_for_late_density_bound
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
    (L Rstar : ℝ) (cover : NativeNormalCover S L) (p : ℕ)
    (hL : 0 < L) (hRstar : 0 < Rstar) (hp : 24 ≤ p) :
    ∃ s : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ),
      let v1 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
      let v2 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
      let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
        secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
      let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
        secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
      ∃ eta C tb : ℝ, 0 < eta ∧ eta ≤ cover.dilationCeiling ∧
        1 ≤ C ∧ 0 < tb ∧ 3 * tb < depthPrimitive L (1/8) (1/4) ∧
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
          (∀ B : ℝ, 0 ≤ B → ∃ rho Cstar : ℝ, 0 < rho ∧ 0 < Cstar ∧
          (∀ delta : ℝ, 0 < delta → ∀ y ∈ K,
            referenceRadius delta Rstar p L y < rho →
              let radius := (referenceRadius delta Rstar p L y) ^ ((1 : ℝ) / 23)
              closedBall y radius ⊆ W ∧
              closedBall y radius ⊆ interior cylinder ∧
              closedBall y radius ⊆ closedBall (0 : R3) 3 ∧
              ∀ z ∈ closedBall y radius, chi z = 1) ∧
          ∀ (lam delta bound separation : ℝ)
            (KK : ConstructedMixedKernel S L lam delta Rstar bound separation p cover),
            0 < lam → lam ≤ eta → 0 < delta →
            (∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) →
            ∃ Psi : R3 → SphereSobolev (3/2 : ℝ),
              ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
              (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                ∀ u : SmoothData,
                (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
                  (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
                  (packetEndpoint S L (cover.packet i) lam y
                    (referenceRadius delta Rstar p L y) z) = 0) →
                nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
                  lam delta Rstar p Psi u y =
                  nativeMixedKernelWronskianFlux S L (cover.packet i) lam KK.kernel u.1
                    y (referenceRadius delta Rstar p L y) y) ∧
              (∀ k : Fin 5, ∀ i : Fin cover.count,
                ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                  |R2 k (y,lam)-R1 k (y,lam)| ≤
                    C * (referenceRadius delta Rstar p L y)^2 *
                      ‖(sphereSobolevZeroEquiv hO hD).symm
                        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖) ∧
              (eLpNorm (fun z : R3 => chi z •
                (sphereSobolevZeroEquiv hO hD).symm
                  (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi z)))
                2 (volume.restrict cylinder) ≤ ENNReal.ofReal B →
                ∀ y ∈ K, referenceRadius delta Rstar p L y < rho →
                  coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
                    Cstar * (referenceRadius delta Rstar p L y)^(3/2 : ℝ))) := by
  obtain ⟨s,etaM,C,etaA,CA,U,hEtaM,hEtaMCover,hC,hEtaA,hCA,hU,hStrip,
      hR1,hR2,hRecovery,hMomentFactory⟩ :=
    exists_actual_five_source_recovery_moment_package
      hcalc hreg hF hO hD τ0 hKernel S hFirst hSecond hFree hMatch
      L Rstar cover p hRstar
  let v1 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
  let v2 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
  let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
  let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
  change (∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U)) at hR1
  change (∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U)) at hR2
  have hCoreResult :=
    exists_actual_middle_source_matched_five_source_coordinateH8_le_three_halves_of_metric_recovery_for_late_density_bound
      S L Rstar cover hO hD p hL hRstar hp R1 R2 etaA hEtaA U hU hStrip hR1 hR2
      CA C hCA (by linarith) hRecovery
  obtain ⟨tb,htb,hthree,hKcompact,hKinside,chi,hChi,hChiCompact,hRange,
    hChiSupport,W,hWopen,hKW,hWOne,hDerivRegion,hCoreLate⟩ := hCoreResult
  let eta : ℝ := min etaM etaA
  have hEta : 0 < eta := lt_min hEtaM hEtaA
  have hEtaCover : eta ≤ cover.dilationCeiling :=
    (min_le_left etaM etaA).trans hEtaMCover
  refine ⟨s,eta,C,tb,hEta,hEtaCover,hC,htb,hthree,
    hKcompact,hKinside,chi,hChi,hChiCompact,hRange,hChiSupport,
    W,hWopen,hKW,hWOne,hDerivRegion,?_⟩
  intro B hB
  obtain ⟨rho,Cstar,hrho,hCstar,hGeometry,hCore⟩ := hCoreLate B hB
  refine ⟨rho,Cstar,hrho,hCstar,hGeometry,?_⟩
  intro lam delta bound separation KK hLamPos hLamLe hDelta hRadius
  have hLamM : lam ≤ etaM := hLamLe.trans (min_le_left _ _)
  have hLamA : lam ∈ Icc (-etaA) etaA := by
    constructor
    · linarith
    · exact hLamLe.trans (min_le_right _ _)
  obtain ⟨Psi,hPsiSmooth,hPsiCompact,hPsiIdentity,hPsiMoment⟩ :=
    hMomentFactory lam delta bound separation KK
      hDelta hLamPos hLamM hRadius
  refine ⟨Psi,hPsiSmooth,hPsiCompact,hPsiIdentity,hPsiMoment,?_⟩
  intro hDensity y hy hrsmall
  exact hCore lam hLamA delta hDelta Psi hPsiSmooth hPsiCompact
    hPsiMoment hDensity y hy hrsmall

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
