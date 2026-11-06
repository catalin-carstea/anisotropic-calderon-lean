import Calderon.ActualOriginalSourceTransferReproduction
import Calderon.CollaboratorFixedDirichletRegularityOct17
import Calderon.CollaboratorFixedSobolevCalculusOct17
import Calderon.ActualOriginalSourceResponseCoordinatePDE
import Calderon.LocalSmoothAmbientExtension
import Calderon.PhysicalHarmonicDilation
import Calderon.ActualCoveredScalarTransfer
import Calderon.ActualNormalizedSecondUCPDictionary
import Calderon.ActualKnownSideInteriorSeed
import Calderon.CollaboratorUniqueContinuationProofOct17
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ExteriorSource
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift

theorem exists_actual_main_original_source_transfer_density
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData) (hOriginal1 : S.original1 = g1) (hOriginal2 : S.original2 = g2)
    (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ Psi : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
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
        ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
          closedBall (0 : R3) 1 ⊆ V →
        (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
          ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u) Y ∧
          ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
            (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u) z = 0 ) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
          (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          S.g1_admissible fixedSobolevCalculus hF hO hD τ0 S.g2 lam
          (referenceRadius delta Rstar p L) Psi y = 0 ) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData) y = 1 ) ∧
      (∀ V : Set R3, IsOpen V → ∀ u : SmoothData,
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
            closedBall (0 : R3) 1 ⊆ V) →
        (∀ x ∈ V, coordinateFluxDivergence
          (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∀ v : SmoothData,
        (∀ y ∈ interior cylinder, coordinateFluxDivergence
          (metricDivergenceFlux (fun z => S.g2 (lam • z)) v.1) y = 0) →
        (∀ y ∈ cylinder, lam • y ∈ S.W → u.1 y = v.1 y) →
        ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u y = v.1 y) ∧
      (∀ k : Fin 3, ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi
          (⟨fun z : R3 => z k, (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff⟩ : SmoothData) y = y k) ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        (∀ y ∈ cylinder, S.Xi1 (lam • y) ∉ tsupport s) →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z ∈ closedBall (0 : R3) 1, S.Xi1 (lam • packetEndpoint S L (cover.packet i)
            lam y (referenceRadius delta Rstar p L y) z) ∉ tsupport s) →
        (∀ y ∈ cylinder, S.Xi2 (lam • y) ∉ tsupport s) →
        (∀ y ∈ cylinder, lam • y ∈ S.W →
          radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s
            (S.Xi1 (lam • y)) =
          radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s
            (S.Xi2 (lam • y))) →
        ∃ u v : SmoothData, HasCompactSupport u.1 ∧ HasCompactSupport v.1 ∧
          (∀ y ∈ cylinder, u.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (S.Xi1 (lam • x)))) ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            ∀ z ∈ closedBall (0 : R3) 1,
            u.1 =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam y
              (referenceRadius delta Rstar p L y) z)] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (S.Xi1 (lam • x)))) ∧
          (∀ y ∈ cylinder, v.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s (S.Xi2 (lam • x)))) ∧
          ∃ V : Set R3, IsOpen V ∧
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
                closedBall (0 : R3) 1 ⊆ V) ∧
            (∀ x ∈ V, coordinateFluxDivergence
              (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) ∧
            ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
                lam delta Rstar p Psi u y =
              radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s
                (S.Xi2 (lam • y)) := by
  have hOne : radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 := by
    cases hOriginal1
    rfl
  have hTwo : radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 := by
    cases hOriginal2
    rfl
  obtain ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass,hPair,hCoordinates,hSource⟩ :=
    exists_global_native_density_original_source_reproduction
      fixedSobolevCalculus fixedDirichletRegularity hF hO hD τ0 hKernel S L lam delta Rstar
      bound separation p cover K hdelta hRstar hlam hlamRoom hRadius
  rw [hOne,hTwo] at hSource
  exact ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass,hPair,hCoordinates,hSource⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
