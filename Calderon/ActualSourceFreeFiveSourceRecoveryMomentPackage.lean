import Calderon.ActualSourceFreeUniformFiveSourceMoments

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

/-- The checked five-test factory is exposed in a narrow interface retaining
its SAME source families in metric recovery, source moment, and the original
kernel density-functional identity. -/
theorem exists_actual_five_source_recovery_moment_package_of_source_free_room
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
    (L Rstar : ℝ) (cover : NativeNormalCover S L) (p : ℕ)
    (hRstar : 0 < Rstar) :
    ∃ s : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ),
      let v1 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
      let v2 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
      let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
        secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
      let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
        secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
      ∃ etaM C etaA CA : ℝ, ∃ U : Set (ℝ × R3),
        0 < etaM ∧ etaM ≤ cover.dilationCeiling ∧ 1 ≤ C ∧
        0 < etaA ∧ 1 ≤ CA ∧ IsOpen U ∧
        Icc (-etaA) etaA ×ˢ cylinder ⊆ U ∧
        (∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U)) ∧
        (∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U)) ∧
        (∀ lam ∈ Icc (-etaA) etaA, ∀ n : ℕ, n ≤ 8 → ∀ y ∈ cylinder,
          ‖iteratedFDeriv ℝ n
            (fun x => referenceNormalizedPrincipalDifference S.g1 S.g2 L lam x) y‖ ≤
            CA * ∑ i ∈ Finset.range (n+1), (Nat.choose n i : ℝ) *
              ∑ k : Fin 5, ‖iteratedFDeriv ℝ (n-i+2)
                (fun x => R1 k (x,lam)-R2 k (x,lam)) y‖) ∧
        ∀ (lam delta bound separation : ℝ)
          (KK : ConstructedMixedKernel S L lam delta Rstar bound separation p cover),
          0 < delta → 0 < lam → lam ≤ etaM →
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
                      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖) := by
  obtain ⟨s,hs⟩ := exists_uniform_native_five_source_moments_of_source_free_room
    hcalc hreg hF hO hD τ0 hKernel S hFree hMatch
  let v1 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
  let v2 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
  let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
  let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
  obtain ⟨etaM,C,hEtaM,hEtaMCover,hC,hMomentFactory⟩ := hs.2 L cover
  obtain ⟨etaA,CA,U,hEtaA,_hEtaA1,hCA,hU,hStrip,_hRoom,_hAvoid,hR1,hR2,hRecovery⟩ :=
    hs.1.1.2.2 L cylinder isCompact_native_center_cylinder 8
  change (∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U)) at hR1
  change (∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U)) at hR2
  refine ⟨s,etaM,C,etaA,CA,U,hEtaM,hEtaMCover,hC,hEtaA,hCA,hU,hStrip,
    hR1,hR2,hRecovery,?_⟩
  intro lam delta bound separation KK hDelta hLamPos hLamM hRadius
  obtain ⟨Psi,hPsi⟩ := hMomentFactory lam delta Rstar bound separation p KK
    hDelta hRstar hLamPos hLamM hRadius
  exact ⟨Psi,hPsi.1.1,hPsi.1.2.1,hPsi.1.2.2.1,hPsi.2⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
