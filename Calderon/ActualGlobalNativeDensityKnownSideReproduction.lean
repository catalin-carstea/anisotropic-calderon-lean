import Calderon.ActualOriginalSourcePhysicalFluxReproduction
import Calderon.ActualMixedKernelScalarTransfer

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift

theorem exists_global_native_density_scalarPDE_and_original_known_side_reproduction
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
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
      ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
          closedBall (0 : R3) 1 ⊆ V →
        (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
          ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u) Y ∧
          ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
            (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u) z = 0 := by
  have hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  obtain ⟨Gext,hG,hGCompact,hGerm⟩ := exists_smooth_mixed_kernel_eq_near_all_native_surfaces
    S L lam delta Rstar bound separation p cover K hdelta hRstar hLam hRadius
  obtain ⟨Psi,hPsi,hCompact,hRep,hPDE⟩ :=
    exists_global_nativeMixedKernelDensityFunctional_secondPDE
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hLam hRadius
  refine ⟨Psi,hPsi,hCompact,hRep,?_,hPDE⟩
  intro i y hy hKnown u hphysical
  have hPhysicalBall : ∀ z ∈ ball (0 : R3) 1, coordinateFluxDivergence
      (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
      (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0 := by
    intro z hz
    exact hphysical z (by simpa only [coe_ballOpens,B] using hz)
  have hValue := nativeMixedKernelWronskianFlux_eq_value_on_original_known_side
    S L lam delta Rstar bound separation p cover K hlam hlamRoom hdelta hRstar i y hy
    (hRadius y hy.1) hKnown Gext hG (hGerm i y hy) u hPhysicalBall
  have hFlux := nativeMixedKernelWronskianFlux_eq_of_product_germs
    S L (cover.packet i) lam Gext K.kernel u.1 y (referenceRadius delta Rstar p L y) y
    (hGerm i y hy)
  exact (hRep i y hy u hphysical).trans (hFlux.symm.trans hValue)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
