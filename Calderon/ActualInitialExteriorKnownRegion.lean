import Calderon.ActualInitialPhysicalFrontierTransferWithSourceTests
import Calderon.RadiusTwoSmoothSourceCommonExterior
import Mathlib.Analysis.Normed.Module.Connected
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix BigOperators
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift
  ReferenceWeightedApproximation SphereHarmonic DirichletFamily.DriftBootstrap
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem isConnected_exteriorAnnulusOpens : IsConnected (exteriorAnnulusOpens : Set R3) := by
  have hRank : 1 < Module.rank ℝ R3 := by
    exact Module.one_lt_rank_of_one_lt_finrank (by norm_num [R3])
  have hSphere : IsConnected (sphere (0 : R3) 1) :=
    isConnected_sphere hRank (0 : R3) (by norm_num)
  have hInterval : IsConnected (Ioo (1 : ℝ) 2) := isConnected_Ioo (by norm_num)
  let F : R3 × ℝ → R3 := fun z => z.2 • z.1
  have hF : Continuous F := continuous_snd.smul continuous_fst
  have hImage : F '' (sphere (0 : R3) 1 ×ˢ Ioo (1 : ℝ) 2) = (exteriorAnnulusOpens : Set R3) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨w,r⟩,⟨hw,hr⟩,rfl⟩
      have hw1 : ‖w‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hw
      have hr0 : 0 < r := lt_trans zero_lt_one hr.1
      change 1 < ‖r • w‖ ∧ ‖r • w‖ < 2
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr0,hw1,mul_one]
      exact ⟨hr.1,hr.2⟩
    · intro x hx
      have hx0 : 0 < ‖x‖ := lt_trans zero_lt_one hx.1
      refine ⟨(‖x‖⁻¹ • x,‖x‖),⟨?_,hx⟩,?_⟩
      · change ‖‖x‖⁻¹ • x - (0 : R3)‖ = 1
        rw [sub_zero,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hx0,
          inv_mul_cancel₀ hx0.ne']
      · change ‖x‖ • (‖x‖⁻¹ • x) = x
        rw [smul_smul,mul_inv_cancel₀ hx0.ne',one_smul]
  rw [← hImage]
  exact (hSphere.prod hInterval).image F hF.continuousOn

theorem exists_actual_initial_exterior_transfer_with_source_tests
    (original1 original2 : MatrixField)
    (hOriginal1 : IsAdmissibleMetric original1) (hOriginal2 : IsAdmissibleMetric original2)
    (hEnergy : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy original1 f = minimalEnergy original2 f)
    (bound separation : ℝ) (hbound : 0 < bound) (hseparation : 0 < separation) :
    ∃ τ0 : UnitBallValueTrace,
    ∃ (K1 K2 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
      (G1 G2 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ),
      UnitBallValueTraceKernel τ0 ∧
      IsRadiusTwoSeparatelySmoothInverseSourceKernel original1 hOriginal1 K1 G1 ∧
      IsRadiusTwoSeparatelySmoothInverseSourceKernel original2 hOriginal2 K2 G2 ∧
      (∀ pole : (radiusTwoOpens : Set R3), (pole : R3) ∈ (exteriorAnnulusOpens : Set R3) →
        EqOn (G1 pole) (G2 pole) ((exteriorAnnulusOpens : Set R3) \ {(pole : R3)})) ∧
    ∃ (center p q : R3) (S : KnownSideSourceData),
      closedBall center (1/4 : ℝ) ⊆ (radiusTwoOpens : Set R3) ∧
      ball center (1/4 : ℝ) ⊆ (exteriorAnnulusOpens : Set R3) ∧
      p ∈ sphere center (1/4 : ℝ) ∧ p ∈ (radiusTwoOpens : Set R3) ∧
      ‖p‖ ≤ 1 ∧ p ∉ (exteriorAnnulusOpens : Set R3) ∧ p ∈ closure (exteriorAnnulusOpens : Set R3) ∧
      q ∈ (radiusTwoOpens : Set R3) ∧ ‖q‖ ≤ 1 ∧
      S.hreg = fixedDirichletRegularity ∧ S.hcalc = fixedSobolevCalculus ∧
      S.original1 = original1 ∧ S.original2 = original2 ∧
      S.K1 = K1 ∧ S.K2 = K2 ∧ S.G1 = G1 ∧ S.G2 = G2 ∧
      S.Xi1 0 = q ∧ S.Xi2 0 = p ∧
      ‖S.Xi1 0‖ ≤ 1 ∧ ‖S.Xi2 0‖ ≤ 1 ∧
      (∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
        radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
        radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x)) ∧
      (
    ∃ s : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ),
      let v1 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
      let v2 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
      (∀ k : Fin 5,
        v1 k 0 = 0 ∧ fderiv ℝ (v1 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v1 k)) 0 =
          matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k) ∧
        v2 k 0 = 0 ∧ fderiv ℝ (v2 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v2 k)) 0 =
          matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)) ∧
      ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ S.coordinateRoom ∧
      (∀ (K : Set R3), IsCompact K → ∀ N : ℕ,
    let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
      secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
    let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
      secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
    ∃ (lam0 C : ℝ) (U : Set (R3 × ℝ)),
      0 < lam0 ∧ lam0 ≤ 1 ∧ 0 ≤ C ∧ IsOpen U ∧
      (K ×ˢ Icc (-lam0) lam0 ⊆ U) ∧
      (∀ z ∈ U, z.2 • z.1 ∈ ball (0 : R3) (r / 2)) ∧
      (∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) U) ∧
      (∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) U) ∧
      (∀ k : Fin 5, ∀ z ∈ U, z.2 ≠ 0 →
        R1 k z = (z.2 ^ 2)⁻¹ * v1 k (z.2 • z.1)) ∧
      (∀ k : Fin 5, ∀ z ∈ U, z.2 ≠ 0 →
        R2 k z = (z.2 ^ 2)⁻¹ * v2 k (z.2 • z.1)) ∧
      (∀ k : Fin 5, ∀ y : R3,
        R1 k (y, 0) = (1 / 2 : ℝ) *
          matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k) y y ∧
        R2 k (y, 0) = (1 / 2 : ℝ) *
          matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k) y y) ∧
      (∀ k : Fin 5, ∀ n : ℕ, n ≤ N → ∀ z ∈ K ×ˢ Icc (-lam0) lam0,
        ‖iteratedFDeriv ℝ n (R1 k) z‖ ≤ C) ∧
      (∀ k : Fin 5, ∀ n : ℕ, n ≤ N → ∀ z ∈ K ×ˢ Icc (-lam0) lam0,
        ‖iteratedFDeriv ℝ n (R2 k) z‖ ≤ C) ∧
      (∀ k : Fin 5, ∀ lam ∈ Icc (-lam0) lam0, ∀ n : ℕ, n ≤ N →
        ∀ y ∈ K, ‖iteratedFDeriv ℝ n (fun x => R1 k (x, lam)) y‖ ≤ C) ∧
      (∀ k : Fin 5, ∀ lam ∈ Icc (-lam0) lam0, ∀ n : ℕ, n ≤ N →
        ∀ y ∈ K, ‖iteratedFDeriv ℝ n (fun x => R2 k (x, lam)) y‖ ≤ C) ∧
      (∀ k : Fin 5, ∀ z ∈ U,
        fderiv ℝ (fderiv ℝ (fun x : R3 => R1 k (x, z.2))) z.1 =
          fderiv ℝ (fderiv ℝ (v1 k)) (z.2 • z.1)) ∧
      (∀ k : Fin 5, ∀ z ∈ U,
        fderiv ℝ (fderiv ℝ (fun x : R3 => R2 k (x, z.2))) z.1 =
          fderiv ℝ (fderiv ℝ (v2 k)) (z.2 • z.1)) ∧
      (∀ k : Fin 5, ∀ y : R3,
        fderiv ℝ (fderiv ℝ (fun x : R3 => R1 k (x, 0))) y =
          matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k) ∧
        fderiv ℝ (fderiv ℝ (fun x : R3 => R2 k (x, 0))) y =
          matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)) ) ∧
      (∀ (L : ℝ) (K : Set R3), IsCompact K → ∀ N : ℕ,
    letI : NormedAddCommGroup Mat := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ Mat := Matrix.normedSpace
    letI : NormedAddCommGroup (Mat →L[ℝ] Mat) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (Mat →L[ℝ] Mat) :=
      ContinuousLinearMap.toNormedSpace
    let H : (ℝ × R3) → Fin 5 → Mat := fun t k i j =>
      fderiv ℝ (fderiv ℝ (v1 k)) (t.1 • t.2)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    let gamma : (ℝ × R3) → Mat := fun t =>
      Real.exp (-2 * L * referenceCoordinateDepth t.2) •
        S.g1 (t.1 • t.2)
    ∃ A : (ℝ × R3) → (Mat →L[ℝ] Mat),
      (∀ t : ℝ × R3, ∀ Z : Mat,
        A t Z =
          ![![matrixContractionL (H t 0) Z,
              matrixContractionL (H t 1) Z,
              matrixContractionL (H t 2) Z],
            ![matrixContractionL (H t 3) Z,
              matrixContractionL (H t 4) Z,
              matrixContractionL (gamma t) Z],
            ![Z 0 1 - Z 1 0, Z 0 2 - Z 2 0, Z 1 2 - Z 2 1]]) ∧
      ∃ (eta C : ℝ) (U : Set (ℝ × R3)),
        0 < eta ∧ eta ≤ 1 ∧ 0 ≤ C ∧ IsOpen U ∧
        (Icc (-eta) eta ×ˢ K ⊆ U) ∧
        (∀ t ∈ U, t.1 • t.2 ∈ ball (0 : R3) (r / 2)) ∧
        ContDiffOn ℝ ∞ A U ∧
        (∀ t ∈ U, (A t).IsInvertible) ∧
        ContDiffOn ℝ ∞ (fun t => (A t).inverse) U ∧
        (∀ n : ℕ, n ≤ N → ∀ t ∈ Icc (-eta) eta ×ˢ K,
          ‖iteratedFDeriv ℝ n A t‖ ≤ C) ∧
        (∀ n : ℕ, n ≤ N → ∀ t ∈ Icc (-eta) eta ×ˢ K,
          ‖iteratedFDeriv ℝ n (fun t => (A t).inverse) t‖ ≤ C) ) ) ∧
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
        ∃ K : ConstructedMixedKernel T L lam (1 : ℝ) Rstar bound separation p cover,
          (∀ delta' ∈ Icc (1 : ℝ) (1 : ℝ), ∀ y ∈ cylinder,
            referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
          ∃ Psi : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
              (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
                (metricDivergenceFlux (fun x => T.g1 (lam • x)) u.1)
                (packetEndpoint T L (cover.packet i) lam y (referenceRadius (1 : ℝ) Rstar p L y) z) = 0) →
              nativeMixedKernelDensityFunctional orthogonalSphereHarmonics denseSphereHarmonics τ0 T L (cover.packet i) lam (1 : ℝ) Rstar p Psi u y =
                nativeMixedKernelWronskianFlux T L (cover.packet i) lam K.kernel u.1
                  y (referenceRadius (1 : ℝ) Rstar p L y) y) ∧
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              lam • y ∈ T.W → ∀ u : SmoothData,
              (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
                (metricDivergenceFlux (fun x => T.g1 (lam • x)) u.1)
                (packetEndpoint T L (cover.packet i) lam y (referenceRadius (1 : ℝ) Rstar p L y) z) = 0) →
              nativeMixedKernelDensityFunctional orthogonalSphereHarmonics denseSphereHarmonics τ0 T L (cover.packet i)
                lam (1 : ℝ) Rstar p Psi u y = u.1 y) ∧
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
              packetEndpoint T L (cover.packet i) lam y (referenceRadius (1 : ℝ) Rstar p L y) ''
                closedBall (0 : R3) 1 ⊆ V →
              (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => T.g1 (lam • z)) u.1) x = 0) →
              ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
                ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional orthogonalSphereHarmonics denseSphereHarmonics τ0 T L (cover.packet i)
                  lam (1 : ℝ) Rstar p Psi u) Y ∧
                ∀ z ∈ Y, normalizedSecondLaplacian T.g1 T.g2 L lam
                  (nativeMixedKernelDensityFunctional orthogonalSphereHarmonics denseSphereHarmonics τ0 T L (cover.packet i) lam (1 : ℝ) Rstar p Psi u) z = 0 ) ∧
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              referencePhysicalDensityOperator T.g1 L (cover.packet i).y0 (cover.packet i).Phi
                (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
                (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
                T.g1_admissible fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics τ0 T.g2 lam
                (referenceRadius (1 : ℝ) Rstar p L) Psi y = 0 ) ∧
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              nativeMixedKernelDensityFunctional orthogonalSphereHarmonics denseSphereHarmonics τ0 T L (cover.packet i)
                lam (1 : ℝ) Rstar p Psi (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData) y = 1 ) ∧
            (∀ V : Set R3, IsOpen V → ∀ u : SmoothData,
              (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                packetEndpoint T L (cover.packet i) lam y (referenceRadius (1 : ℝ) Rstar p L y) ''
                  closedBall (0 : R3) 1 ⊆ V) →
              (∀ x ∈ V, coordinateFluxDivergence
                (metricDivergenceFlux (fun z => T.g1 (lam • z)) u.1) x = 0) →
              ∀ v : SmoothData,
              (∀ y ∈ interior cylinder, coordinateFluxDivergence
                (metricDivergenceFlux (fun z => T.g2 (lam • z)) v.1) y = 0) →
              (∀ y ∈ cylinder, lam • y ∈ T.W → u.1 y = v.1 y) →
              ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                nativeMixedKernelDensityFunctional orthogonalSphereHarmonics denseSphereHarmonics τ0 T L (cover.packet i)
                  lam (1 : ℝ) Rstar p Psi u y = v.1 y) ∧
            (∀ k : Fin 3, ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              nativeMixedKernelDensityFunctional orthogonalSphereHarmonics denseSphereHarmonics τ0 T L (cover.packet i)
                lam (1 : ℝ) Rstar p Psi
                (⟨fun z : R3 => z k, (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff⟩ : SmoothData) y = y k) ∧
            ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
              ∃ u v : SmoothData, HasCompactSupport u.1 ∧ HasCompactSupport v.1 ∧
                (∀ y ∈ cylinder, u.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original1 hOriginal1 s (T.Xi1 (lam • x)))) ∧
                (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                  ∀ z ∈ closedBall (0 : R3) 1,
                  u.1 =ᶠ[𝓝 (packetEndpoint T L (cover.packet i) lam y
                    (referenceRadius (1 : ℝ) Rstar p L y) z)] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original1 hOriginal1 s (T.Xi1 (lam • x)))) ∧
                (∀ y ∈ cylinder, v.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original2 hOriginal2 s (T.Xi2 (lam • x)))) ∧
                ∃ V : Set R3, IsOpen V ∧
                  (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                    packetEndpoint T L (cover.packet i) lam y (referenceRadius (1 : ℝ) Rstar p L y) ''
                      closedBall (0 : R3) 1 ⊆ V) ∧
                  (∀ x ∈ V, coordinateFluxDivergence
                    (metricDivergenceFlux (fun z => T.g1 (lam • z)) u.1) x = 0) ∧
                  ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
                    nativeMixedKernelDensityFunctional orthogonalSphereHarmonics denseSphereHarmonics τ0 T L (cover.packet i)
                      lam (1 : ℝ) Rstar p Psi u y =
                    radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus original2 hOriginal2 s
                      (T.Xi2 (lam • y)) := by
  have hIdMap : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) = (1 : Mat) :=
    matrixOperatorAlgEquiv.symm.map_one
  have hDId (x : R3) : fderiv ℝ (fun z : R3 => z) x = ContinuousLinearMap.id ℝ R3 :=
    (hasFDerivAt_id x).fderiv
  have hJac (x : R3) : coordinateJacobianMatrix (fun z : R3 => z) x = (1 : Mat) := by
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap]
    simpa only [hDId] using hIdMap
  have hPull (x : R3) : pullbackMetric original1 (fun z : R3 => z) x = original1 x := by
    simp only [pullbackMetric,hDId,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,hIdMap,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]
  have hIso : EqOn (pullbackMetric original1 (fun z : R3 => z)) original2
      (exteriorAnnulusOpens : Set R3) := by
    intro x hx
    rw [hPull,hOriginal1.euclidean_exterior x hx.1.le,hOriginal2.euclidean_exterior x hx.1.le]
  have hSources (x : R3) (hx : x ∈ (exteriorAnnulusOpens : Set R3)) :
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus original2 hOriginal2 x =
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus original1 hOriginal1 x := by
    funext s
    exact (radiusTwoSmoothSourceResponse_eqOn_exterior fixedDirichletRegularity fixedSobolevCalculus
      original1 original2 hOriginal1 hOriginal2 hEnergy s hx).symm
  have hMissing : ∃ x ∈ (radiusTwoOpens : Set R3), x ∉ (exteriorAnnulusOpens : Set R3) := by
    refine ⟨0,?_,?_⟩
    · change (0 : R3) ∈ ball (0 : R3) 2
      simp
    · change ¬ ((1 : ℝ) < ‖(0 : R3)‖ ∧ ‖(0 : R3)‖ < 2)
      norm_num
  exact exists_actual_initial_physical_frontier_transfer_with_source_tests original1 original2
    hOriginal1 hOriginal2 hEnergy (exteriorAnnulusOpens : Set R3) exteriorAnnulusOpens.isOpen
    isConnected_exteriorAnnulusOpens exteriorAnnulusOpens_le_radiusTwoOpens (fun _ hx => hx)
    (fun z : R3 => z) (fun _ hx => exteriorAnnulusOpens_le_radiusTwoOpens hx)
    contDiff_id.contDiffOn (fun _ _ _ _ h => h)
    (fun x _ => by rw [hJac,Matrix.det_one];exact isUnit_one)
    hIso (fun _ _ => rfl) hSources hMissing bound separation hbound hseparation

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
