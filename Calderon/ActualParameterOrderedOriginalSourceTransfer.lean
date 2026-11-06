import Calderon.ActualSourceFreeKnownSideRestriction
import Calderon.ActualMixedKernelConstruction

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ExteriorSource
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift

theorem exists_parameter_ordered_actual_original_source_transfer
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData) (hOriginal1 : S.original1 = g1) (hOriginal2 : S.original2 = g2)
    (hFirst : ‖S.Xi1 0‖ ≤ 1) (hSecond : ‖S.Xi2 0‖ ≤ 1)
    (hKnown : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x))
    (bound separation : ℝ) (hbound : 0 < bound) (hseparation : 0 < separation) :
    ∃ T : KnownSideSourceData,
      T.hreg = S.hreg ∧ T.hcalc = S.hcalc ∧
      T.original1 = S.original1 ∧ T.original2 = S.original2 ∧
      T.K1 = S.K1 ∧ T.K2 = S.K2 ∧ T.G1 = S.G1 ∧ T.G2 = S.G2 ∧
      T.Xi1 = S.Xi1 ∧ T.Xi2 = S.Xi2 ∧ T.g1 = S.g1 ∧ T.g2 = S.g2 ∧
      T.separating_function = S.separating_function ∧
      T.coordinateRoom ⊆ S.coordinateRoom ∧ T.W = S.W ∩ T.coordinateRoom ∧
      (∀ x ∈ T.coordinateRoom,
        T.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
        T.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3)) ∧
      ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∃ cover : NativeNormalCover T L,
      ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
      ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
      ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
      ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ cover.dilationCeiling ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      CurrentRadiusBootstrap S L lam delta Rstar eps p →
      ∃ K : ConstructedMixedKernel T L lam delta Rstar bound separation p cover,
        (∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
          referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
        ∃ Psi : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
            (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
              (metricDivergenceFlux (fun x => T.g1 (lam • x)) u.1)
              (packetEndpoint T L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
            nativeMixedKernelDensityFunctional hO hD τ0 T L (cover.packet i) lam delta Rstar p Psi u y =
              nativeMixedKernelWronskianFlux T L (cover.packet i) lam K.kernel u.1
                y (referenceRadius delta Rstar p L y) y) ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            lam • y ∈ T.W → ∀ u : SmoothData,
            (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
              (metricDivergenceFlux (fun x => T.g1 (lam • x)) u.1)
              (packetEndpoint T L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
            nativeMixedKernelDensityFunctional hO hD τ0 T L (cover.packet i)
              lam delta Rstar p Psi u y = u.1 y) ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
            packetEndpoint T L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
              closedBall (0 : R3) 1 ⊆ V →
            (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => T.g1 (lam • z)) u.1) x = 0) →
            ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
              ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 T L (cover.packet i)
                lam delta Rstar p Psi u) Y ∧
              ∀ z ∈ Y, normalizedSecondLaplacian T.g1 T.g2 L lam
                (nativeMixedKernelDensityFunctional hO hD τ0 T L (cover.packet i) lam delta Rstar p Psi u) z = 0 ) ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            referencePhysicalDensityOperator T.g1 L (cover.packet i).y0 (cover.packet i).Phi
              (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
              (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
              T.g1_admissible fixedSobolevCalculus hF hO hD τ0 T.g2 lam
              (referenceRadius delta Rstar p L) Psi y = 0 ) ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            nativeMixedKernelDensityFunctional hO hD τ0 T L (cover.packet i)
              lam delta Rstar p Psi (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData) y = 1 ) ∧
          (∀ V : Set R3, IsOpen V → ∀ u : SmoothData,
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              packetEndpoint T L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
                closedBall (0 : R3) 1 ⊆ V) →
            (∀ x ∈ V, coordinateFluxDivergence
              (metricDivergenceFlux (fun z => T.g1 (lam • z)) u.1) x = 0) →
            ∀ v : SmoothData,
            (∀ y ∈ interior cylinder, coordinateFluxDivergence
              (metricDivergenceFlux (fun z => T.g2 (lam • z)) v.1) y = 0) →
            (∀ y ∈ cylinder, lam • y ∈ T.W → u.1 y = v.1 y) →
            ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              nativeMixedKernelDensityFunctional hO hD τ0 T L (cover.packet i)
                lam delta Rstar p Psi u y = v.1 y) ∧
          (∀ k : Fin 3, ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            nativeMixedKernelDensityFunctional hO hD τ0 T L (cover.packet i)
              lam delta Rstar p Psi
              (⟨fun z : R3 => z k, (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff⟩ : SmoothData) y = y k) ∧
          ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
            ∃ u v : SmoothData, HasCompactSupport u.1 ∧ HasCompactSupport v.1 ∧
              (∀ y ∈ cylinder, u.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (T.Xi1 (lam • x)))) ∧
              (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                ∀ z ∈ closedBall (0 : R3) 1,
                u.1 =ᶠ[𝓝 (packetEndpoint T L (cover.packet i) lam y
                  (referenceRadius delta Rstar p L y) z)] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (T.Xi1 (lam • x)))) ∧
              (∀ y ∈ cylinder, v.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s (T.Xi2 (lam • x)))) ∧
              ∃ V : Set R3, IsOpen V ∧
                (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                  packetEndpoint T L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
                    closedBall (0 : R3) 1 ⊆ V) ∧
                (∀ x ∈ V, coordinateFluxDivergence
                  (metricDivergenceFlux (fun z => T.g1 (lam • z)) u.1) x = 0) ∧
                ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                  nativeMixedKernelDensityFunctional hO hD τ0 T L (cover.packet i)
                    lam delta Rstar p Psi u y =
                  radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s
                    (T.Xi2 (lam • y)) := by
  obtain ⟨T,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hGOrig1,hGOrig2,hXi1,hXi2,hgT1,hgT2,
    hSep,hRoom,hW,hFree,hPreserve⟩ :=
    exists_known_side_source_data_with_source_free_room S hFirst hSecond
  have hGT1 : T.original1 = g1 := hOrig1.trans hOriginal1
  have hGT2 : T.original2 = g2 := hOrig2.trans hOriginal2
  have hOne : radiusTwoSmoothSourceResponse T.hreg T.hcalc T.original1 T.original1_admissible =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 := by
    cases hGT1
    rfl
  have hTwo : radiusTwoSmoothSourceResponse T.hreg T.hcalc T.original2 T.original2_admissible =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 := by
    cases hGT2
    rfl
  refine ⟨T,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hGOrig1,hGOrig2,hXi1,hXi2,hgT1,hgT2,
    hSep,hRoom,hW,hFree,?_⟩
  obtain ⟨L0,hL0,hL⟩ := actual_mixed_kernel_exists T bound separation hbound hseparation
  refine ⟨L0,hL0,?_⟩
  intro L hLge
  obtain ⟨cover,p0,hp0,hp⟩ := hL L hLge
  refine ⟨cover,p0,hp0,?_⟩
  intro p hpge
  obtain ⟨eps0,heps0,heps01,heps⟩ := hp p hpge
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps hepspos hepsle
  obtain ⟨R0,hR0,hR⟩ := heps eps hepspos hepsle
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRstar hRle
  obtain ⟨lam0,hlam0,hlam0Room,hLam⟩ := hR Rstar hRstar hRle
  refine ⟨lam0,hlam0,hlam0Room,?_⟩
  intro lam hlam hlamle delta hdelta hdelta1 hBootstrap
  have hBootstrapT : CurrentRadiusBootstrap T L lam delta Rstar eps p := by
    simpa only [CurrentRadiusBootstrap,hgT1,hgT2] using hBootstrap
  obtain ⟨hAllRadius,⟨K⟩⟩ := hLam lam hlam hlamle delta hdelta hdelta1 hBootstrapT
  have hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling :=
    hAllRadius delta ⟨le_rfl,hdelta1⟩
  have hlamRoom : lam ≤ cover.dilationCeiling := hlamle.trans hlam0Room
  refine ⟨K,hAllRadius,?_⟩
  obtain ⟨Psi,hPsi,hCompact,hRep,hKnownPsi,hPDE,hOperator,hMass,hPair,hCoordinates,hSource⟩ :=
    exists_actual_main_original_source_transfer_density g1 g2 hg1 hg2 hF hO hD τ0 hKernel
      T hGT1 hGT2 L lam delta Rstar bound separation p cover K hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompact,hRep,hKnownPsi,hPDE,hOperator,hMass,hPair,hCoordinates,?_⟩
  intro s
  obtain ⟨hAvoidCenter,hAvoidBall,hAvoidSecond⟩ :=
    source_support_avoidance_on_actual_transfer_family T hFree L lam delta Rstar bound
      separation p cover K hdelta hRstar ⟨le_of_lt hlam,hlamRoom⟩ hRadius s
  have hKnownT : ∀ y ∈ cylinder, lam • y ∈ T.W →
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s
        (T.Xi1 (lam • y)) =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s
        (T.Xi2 (lam • y)) := by
    intro y _ hyW
    have hm := hPreserve s (hKnown s) (lam • y) hyW
    rwa [hOne,hTwo] at hm
  exact hSource s hAvoidCenter hAvoidBall hAvoidSecond hKnownT

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
