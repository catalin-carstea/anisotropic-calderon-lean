import Calderon.ActualPhysicalKnownBallOriginalSourceData

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ExteriorSource
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift

theorem exists_parameter_ordered_transfer_of_physical_known_ball
    (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (original1 original2 : MatrixField)
    (hOriginal1 : IsAdmissibleMetric original1) (hOriginal2 : IsAdmissibleMetric original2)
    (K1 K2 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G1 G2 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hKernel1 : IsRadiusTwoSeparatelySmoothInverseSourceKernel original1 hOriginal1 K1 G1)
    (hKernel2 : IsRadiusTwoSeparatelySmoothInverseSourceKernel original2 hOriginal2 K2 G2)
    (U : Set R3) (hU : IsOpen U) (h0 : (0 : R3) ∈ U)
    (Xi1 Xi2 : R3 → R3)
    (hSmooth1 : ContDiffOn ℝ ∞ Xi1 U) (hSmooth2 : ContDiffOn ℝ ∞ Xi2 U)
    (hInjective1 : Set.InjOn Xi1 U) (hInjective2 : Set.InjOn Xi2 U)
    (hJac1 : ∀ x ∈ U, IsUnit (coordinateJacobianMatrix Xi1 x).det)
    (hJac2 : ∀ x ∈ U, IsUnit (coordinateJacobianMatrix Xi2 x).det)
    (hRange1 : ∀ x ∈ U, Xi1 x ∈ (radiusTwoOpens : Set R3))
    (hRange2 : ∀ x ∈ U, Xi2 x ∈ (radiusTwoOpens : Set R3))
    (hHarmonic1 : ∀ i : Fin 3, ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric original1 Xi1) (fun z => z i)) x = 0)
    (hHarmonic2 : ∀ i : Fin 3, ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric original2 Xi2) (fun z => z i)) x = 0)
    (physicalW : Set R3) (hPhysicalW : IsOpen physicalW) (hConnected : IsConnected physicalW)
    (hPhysicalRoom : physicalW ⊆ (radiusTwoOpens : Set R3))
    (hSource : (fixedExteriorSourceOpens : Set R3) ⊆ physicalW)
    (Phi : R3 → R3) (hPhiRoom : ∀ x ∈ physicalW, Phi x ∈ (radiusTwoOpens : Set R3))
    (hPhiSmooth : ContDiffOn ℝ ∞ Phi physicalW) (hPhiInj : Set.InjOn Phi physicalW)
    (hPhiJac : ∀ x ∈ physicalW, IsUnit (coordinateJacobianMatrix Phi x).det)
    (hIso : EqOn (pullbackMetric original1 Phi) original2 physicalW)
    (hFix : ∀ x ∈ (fixedExteriorSourceOpens : Set R3), Phi x = x)
    (hMatch : ∀ x ∈ physicalW,
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus original2 hOriginal2 x =
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus original1 hOriginal1 (Phi x))
    (hBranch : ∀ z ∈ U, Xi2 z ∈ physicalW → Xi1 z = Phi (Xi2 z))
    (center : R3) (r : ℝ) (hr : 0 < r)
    (hTouch : Xi2 0 ∈ sphere center r) (hBall : ball center r ⊆ physicalW)
    (hFirstPoint : ‖Xi1 0‖ ≤ 1) (hSecondPoint : ‖Xi2 0‖ ≤ 1)
    (bound separation : ℝ) (hbound : 0 < bound) (hseparation : 0 < separation) :
    ∃ (A : R3 ≃L[ℝ] R3) (c : ℝ), 0 < c ∧ (∀ v : R3, fderiv ℝ (fun z => ‖Xi2 z - center‖ ^ 2 - r ^ 2) 0 (A v) = c * v 2) ∧
    ∃ S : KnownSideSourceData,
      S.hreg = fixedDirichletRegularity ∧ S.hcalc = fixedSobolevCalculus ∧
      S.original1 = original1 ∧ S.original2 = original2 ∧
      S.K1 = K1 ∧ S.K2 = K2 ∧ S.G1 = G1 ∧ S.G2 = G2 ∧
      S.Xi1 = Xi1 ∘ A ∧ S.Xi2 = Xi2 ∘ A ∧
      S.separating_function = (fun x => c⁻¹ * (‖Xi2 (A x) - center‖ ^ 2 - r ^ 2)) ∧
      S.coordinateRoom ⊆ A ⁻¹' U ∧ S.W = (A ⁻¹' (U ∩ Xi2 ⁻¹' physicalW)) ∩ S.coordinateRoom ∧
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
                (∀ y ∈ cylinder, u.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original1 hOriginal1 s (T.Xi1 (lam • x)))) ∧
                (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                  ∀ z ∈ closedBall (0 : R3) 1,
                  u.1 =ᶠ[𝓝 (packetEndpoint T L (cover.packet i) lam y
                    (referenceRadius delta Rstar p L y) z)] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original1 hOriginal1 s (T.Xi1 (lam • x)))) ∧
                (∀ y ∈ cylinder, v.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original2 hOriginal2 s (T.Xi2 (lam • x)))) ∧
                ∃ V : Set R3, IsOpen V ∧
                  (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                    packetEndpoint T L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
                      closedBall (0 : R3) 1 ⊆ V) ∧
                  (∀ x ∈ V, coordinateFluxDivergence
                    (metricDivergenceFlux (fun z => T.g1 (lam • z)) u.1) x = 0) ∧
                  ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                    nativeMixedKernelDensityFunctional hO hD τ0 T L (cover.packet i)
                      lam delta Rstar p Psi u y =
                    radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original2 hOriginal2 s
                      (T.Xi2 (lam • y)) := by
  obtain ⟨A,c,hc,hDirection,S,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hG1,hG2,hXiS1,hXiS2,hSepS,hRoom,hSW,hKnownS⟩ :=
    exists_original_source_data_of_physical_known_ball original1 original2 hOriginal1 hOriginal2
      K1 K2 G1 G2 hKernel1 hKernel2 U hU h0 Xi1 Xi2 hSmooth1 hSmooth2 hInjective1 hInjective2
      hJac1 hJac2 hRange1 hRange2 hHarmonic1 hHarmonic2 physicalW hPhysicalW hConnected hPhysicalRoom
      hSource Phi hPhiRoom hPhiSmooth hPhiInj hPhiJac hIso hFix hMatch hBranch center r hr hTouch hBall
  refine ⟨A,c,hc,hDirection,S,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hG1,hG2,hXiS1,hXiS2,hSepS,hRoom,hSW,?_⟩
  have hFirstS : ‖S.Xi1 0‖ ≤ 1 := by
    simpa only [hXiS1,Function.comp_apply,map_zero] using hFirstPoint
  have hSecondS : ‖S.Xi2 0‖ ≤ 1 := by
    simpa only [hXiS2,Function.comp_apply,map_zero] using hSecondPoint
  exact exists_parameter_ordered_actual_original_source_transfer original1 original2 hOriginal1 hOriginal2
    hF hO hD τ0 hKernel S hOrig1 hOrig2 hFirstS hSecondS hKnownS bound separation hbound hseparation

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
