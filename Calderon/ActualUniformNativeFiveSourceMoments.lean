import Calderon.ActualSourceFiniteCoverTaylorFamily
import Calderon.ActualGlobalNativeDensityNormalizedSourceMoment
import Calderon.ActualSourceFreeKnownSideRestriction

noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceWeightedApproximation SphereHarmonic DirichletFamily.DriftBootstrap
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_native_five_source_moments_of_cover_taylor
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
    (s : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (R1 R2 : Fin 5 → (R3 × ℝ) → ℝ)
    (L : ℝ) (cover : NativeNormalCover S L)
    (hCover :
        ∃ (eta C : ℝ) (U : Set (ℝ × R3)),
          0 < eta ∧ eta ≤ cover.dilationCeiling ∧ 1 ≤ C ∧ IsOpen U ∧
          Icc (-eta) eta ×ˢ cylinder ⊆ U ∧
          (∀ k : Fin 5, ∀ t ∈ U, t.1 ≠ 0 →
            R1 k (t.2,t.1) = (t.1^2)⁻¹ * radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k) (S.Xi1 (t.1 • t.2))) ∧
          (∀ k : Fin 5, ∀ t ∈ U, t.1 ≠ 0 →
            R2 k (t.2,t.1) = (t.1^2)⁻¹ * radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k) (S.Xi2 (t.1 • t.2))) ∧
          (∀ k : Fin 5, ∀ i : Fin cover.count, ∀ lam ∈ Icc (0 : ℝ) eta,
            ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            ∀ r ∈ Icc (0 : ℝ) cover.radiusCeiling, ∀ z ∈ closedBall (0 : R3) 1,
              (∀ a ∈ Icc (0 : ℝ) 1,
                (lam, y+a • (packetEndpoint S L (cover.packet i) lam y r z-y)) ∈ U) ∧
              (lam,packetEndpoint S L (cover.packet i) lam y r z) ∈ U ∧
              |R1 k (packetEndpoint S L (cover.packet i) lam y r z,lam) - R1 k (y,lam) -
                fderiv ℝ (fun x : R3 => R1 k (x,lam)) y
                  (packetEndpoint S L (cover.packet i) lam y r z-y)| ≤ C*r^2)) :
        ∃ eta C : ℝ, 0 < eta ∧ eta ≤ cover.dilationCeiling ∧ 1 ≤ C ∧
        ∀ (lam delta Rstar bound separation : ℝ) (p : ℕ)
          (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover),
          0 < delta → 0 < Rstar → 0 < lam → lam ≤ eta →
          (∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) →
    ∃ Psi : R3 → SphereSobolev (3/2 : ℝ),
      (
        ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
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
          S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
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
      (∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        (∀ y ∈ cylinder, S.Xi1 (lam • y) ∉ tsupport s) →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z ∈ closedBall (0 : R3) 1, S.Xi1 (lam • packetEndpoint S L (cover.packet i)
            lam y (referenceRadius delta Rstar p L y) z) ∉ tsupport s) →
        (∀ y ∈ cylinder, S.Xi2 (lam • y) ∉ tsupport s) →
        (∀ y ∈ cylinder, lam • y ∈ S.W →
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
            (S.Xi1 (lam • y)) =
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
            (S.Xi2 (lam • y))) →
        ∃ u v : SmoothData, HasCompactSupport u.1 ∧ HasCompactSupport v.1 ∧
          (∀ y ∈ cylinder, u.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 (lam • x)))) ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            ∀ z ∈ closedBall (0 : R3) 1,
            u.1 =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam y
              (referenceRadius delta Rstar p L y) z)] (fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 (lam • x)))) ∧
          (∀ y ∈ cylinder, v.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 (lam • x)))) ∧
          ∃ V : Set R3, IsOpen V ∧
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
                closedBall (0 : R3) 1 ⊆ V) ∧
            (∀ x ∈ V, coordinateFluxDivergence
              (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) ∧
            ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
                lam delta Rstar p Psi u y =
              radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
                (S.Xi2 (lam • y))) ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        (∀ y ∈ cylinder, S.Xi1 (lam • y) ∉ tsupport s) →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z ∈ closedBall (0 : R3) 1, S.Xi1 (lam • packetEndpoint S L (cover.packet i)
            lam y (referenceRadius delta Rstar p L y) z) ∉ tsupport s) →
        (∀ y ∈ cylinder, S.Xi2 (lam • y) ∉ tsupport s) →
        (∀ y ∈ cylinder, lam • y ∈ S.W →
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
            (S.Xi1 (lam • y)) =
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
            (S.Xi2 (lam • y))) →
        ∀ (R1 R2 : R3 → ℝ) (O : Set R3), IsOpen O → cylinder ⊆ O →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z ∈ closedBall (0 : R3) 1,
            packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z ∈ O) →
        (∀ x ∈ O, R1 x = (lam^2)⁻¹ * radiusTwoSmoothSourceResponse S.hreg S.hcalc
          S.original1 S.original1_admissible s (S.Xi1 (lam • x))) →
        (∀ y ∈ cylinder, R2 y = (lam^2)⁻¹ * radiusTwoSmoothSourceResponse S.hreg S.hcalc
          S.original2 S.original2_admissible s (S.Xi2 (lam • y))) →
        ∀ C : ℝ, 0 ≤ C →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z : UnitSphere,
            |R1 (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z.val) -
              R1 y - fderiv ℝ R1 y
                (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z.val-y)| ≤
              C * (referenceRadius delta Rstar p L y)^2) →
        ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          |R2 y-R1 y| ≤ C * (referenceRadius delta Rstar p L y)^2 *
            ‖(sphereSobolevZeroEquiv hO hD).symm
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖
      ) ∧
      ∀ k : Fin 5, ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        |R2 k (y,lam) - R1 k (y,lam)| ≤
          C * (referenceRadius delta Rstar p L y)^2 *
            ‖(sphereSobolevZeroEquiv hO hD).symm
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖ := by
  obtain ⟨eta, C, U, hEta, hEtaCover, hC1, hU, hStrip, hNorm1, hNorm2, hTaylor⟩ :=
    hCover
  refine ⟨eta, C, hEta, hEtaCover, hC1, ?_⟩
  intro lam delta Rstar bound separation p K hdelta hRstar hlam hlamEta hRadius
  have hlamRoom : lam ≤ cover.dilationCeiling := hlamEta.trans hEtaCover
  have hLamCover : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le, hlamRoom⟩
  have hLamPositive : lam ∈ Icc (0 : ℝ) eta := ⟨hlam.le, hlamEta⟩
  have hLamSigned : lam ∈ Icc (-eta) eta :=
    ⟨(neg_nonpos.mpr hEta.le).trans hlam.le, hlamEta⟩
  have hC : 0 ≤ C := zero_le_one.trans hC1
  have hRadiusClosed (y : R3) (hy : y ∈ cylinder) :
      referenceRadius delta Rstar p L y ∈ Icc (0 : ℝ) cover.radiusCeiling :=
    ⟨(referenceRadius_pos delta Rstar p L y hdelta hRstar).le, (hRadius y hy).le⟩
  let O : Set R3 := (fun x : R3 => (lam, x)) ⁻¹' U
  have hOpenO : IsOpen O := hU.preimage (continuous_const.prodMk continuous_id)
  have hCylinderO : cylinder ⊆ O := fun y hy => hStrip ⟨hLamSigned, hy⟩
  have hEndpointsO : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ z ∈ closedBall (0 : R3) 1,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z ∈ O := by
    intro i y hy z hz
    exact (hTaylor (0 : Fin 5) i lam hLamPositive y hy
      (referenceRadius delta Rstar p L y) (hRadiusClosed y hy.1) z hz).2.1
  obtain ⟨Psi, hGlobal⟩ := exists_global_native_density_normalized_original_source_moments
    hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
    hdelta hRstar hlam hlamRoom hRadius
  have hGlobalCopy := hGlobal
  rcases hGlobalCopy with ⟨_, _, _, _, _, _, _, _, _, _, hMoment⟩
  refine ⟨Psi, hGlobal, ?_⟩
  intro k
  obtain ⟨hCyl1, hBall1, hCyl2⟩ := source_support_avoidance_on_actual_transfer_family
    S hFree L lam delta Rstar bound separation p cover K hdelta hRstar hLamCover hRadius (s k)
  have hMatchK : ∀ y ∈ cylinder, lam • y ∈ S.W →
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)
        (S.Xi1 (lam • y)) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)
        (S.Xi2 (lam • y)) :=
    fun y _ hyW => hMatch (s k) (lam • y) hyW
  have hNormalize1 : ∀ x ∈ O, R1 k (x, lam) = (lam^2)⁻¹ *
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)
        (S.Xi1 (lam • x)) :=
    fun x hx => hNorm1 k (lam, x) hx hlam.ne'
  have hNormalize2 : ∀ y ∈ cylinder, R2 k (y, lam) = (lam^2)⁻¹ *
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)
        (S.Xi2 (lam • y)) :=
    fun y hy => hNorm2 k (lam, y) (hCylinderO hy) hlam.ne'
  have hResidual : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ z : UnitSphere,
        |R1 k (packetEndpoint S L (cover.packet i) lam y
            (referenceRadius delta Rstar p L y) z.val, lam) - R1 k (y, lam) -
          fderiv ℝ (fun x : R3 => R1 k (x, lam)) y
            (packetEndpoint S L (cover.packet i) lam y
              (referenceRadius delta Rstar p L y) z.val - y)| ≤
          C * (referenceRadius delta Rstar p L y)^2 := by
    intro i y hy z
    exact (hTaylor k i lam hLamPositive y hy (referenceRadius delta Rstar p L y)
      (hRadiusClosed y hy.1) z.val (sphere_subset_closedBall z.property)).2.2
  exact hMoment (s k) hCyl1 hBall1 hCyl2 hMatchK
    (fun x : R3 => R1 k (x, lam)) (fun x : R3 => R2 k (x, lam)) O hOpenO hCylinderO
    hEndpointsO hNormalize1 hNormalize2 C hC hResidual


theorem exists_uniform_native_five_source_moments
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
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x)) :
    ∃ s : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ),
      let v1 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
      let v2 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
      let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
        secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
      let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
        secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
      (
      ((∀ k : Fin 5,
        v1 k 0 = 0 ∧ fderiv ℝ (v1 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v1 k)) 0 = matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k) ∧
        v2 k 0 = 0 ∧ fderiv ℝ (v2 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v2 k)) 0 = matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)) ∧
      (∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ S.coordinateRoom ∧
        ∀ (K : Set R3), IsCompact K → ∀ N : ℕ,
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
                matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k))) ∧
      ∀ (L : ℝ) (K : Set R3), IsCompact K → ∀ N : ℕ,
        ∃ (eta C : ℝ) (U : Set (ℝ × R3)),
          0 < eta ∧ eta ≤ 1 ∧ 1 ≤ C ∧ IsOpen U ∧
          Icc (-eta) eta ×ˢ K ⊆ U ∧
          (∀ t ∈ U, t.1 • t.2 ∈ S.coordinateRoom) ∧
          (∀ t ∈ U, ∀ k : Fin 5,
            S.Xi1 (t.1 • t.2) ∉ tsupport (s k) ∧ S.Xi2 (t.1 • t.2) ∉ tsupport (s k)) ∧
          (∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U)) ∧
          (∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U)) ∧
          (∀ lam ∈ Icc (-eta) eta, ∀ n : ℕ, n ≤ N → ∀ y ∈ K,
            ‖iteratedFDeriv ℝ n
              (fun x => referenceNormalizedPrincipalDifference S.g1 S.g2 L lam x) y‖ ≤
              C * ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) *
                ∑ k : Fin 5, ‖iteratedFDeriv ℝ (n - i + 2)
                  (fun x => R1 k (x, lam) - R2 k (x, lam)) y‖)) ∧
      ∀ (L : ℝ) (cover : NativeNormalCover S L),
        ∃ (eta C : ℝ) (U : Set (ℝ × R3)),
          0 < eta ∧ eta ≤ cover.dilationCeiling ∧ 1 ≤ C ∧ IsOpen U ∧
          Icc (-eta) eta ×ˢ cylinder ⊆ U ∧
          (∀ k : Fin 5, ∀ t ∈ U, t.1 ≠ 0 →
            R1 k (t.2,t.1) = (t.1^2)⁻¹ * v1 k (t.1 • t.2)) ∧
          (∀ k : Fin 5, ∀ t ∈ U, t.1 ≠ 0 →
            R2 k (t.2,t.1) = (t.1^2)⁻¹ * v2 k (t.1 • t.2)) ∧
          (∀ k : Fin 5, ∀ i : Fin cover.count, ∀ lam ∈ Icc (0 : ℝ) eta,
            ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            ∀ r ∈ Icc (0 : ℝ) cover.radiusCeiling, ∀ z ∈ closedBall (0 : R3) 1,
              (∀ a ∈ Icc (0 : ℝ) 1,
                (lam, y+a • (packetEndpoint S L (cover.packet i) lam y r z-y)) ∈ U) ∧
              (lam,packetEndpoint S L (cover.packet i) lam y r z) ∈ U ∧
              |R1 k (packetEndpoint S L (cover.packet i) lam y r z,lam) - R1 k (y,lam) -
                fderiv ℝ (fun x : R3 => R1 k (x,lam)) y
                  (packetEndpoint S L (cover.packet i) lam y r z-y)| ≤ C*r^2)
      ) ∧
      ∀ (L : ℝ) (cover : NativeNormalCover S L),
        ∃ eta C : ℝ, 0 < eta ∧ eta ≤ cover.dilationCeiling ∧ 1 ≤ C ∧
        ∀ (lam delta Rstar bound separation : ℝ) (p : ℕ)
          (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover),
          0 < delta → 0 < Rstar → 0 < lam → lam ≤ eta →
          (∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) →
    ∃ Psi : R3 → SphereSobolev (3/2 : ℝ),
      (
        ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
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
          S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
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
      (∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        (∀ y ∈ cylinder, S.Xi1 (lam • y) ∉ tsupport s) →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z ∈ closedBall (0 : R3) 1, S.Xi1 (lam • packetEndpoint S L (cover.packet i)
            lam y (referenceRadius delta Rstar p L y) z) ∉ tsupport s) →
        (∀ y ∈ cylinder, S.Xi2 (lam • y) ∉ tsupport s) →
        (∀ y ∈ cylinder, lam • y ∈ S.W →
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
            (S.Xi1 (lam • y)) =
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
            (S.Xi2 (lam • y))) →
        ∃ u v : SmoothData, HasCompactSupport u.1 ∧ HasCompactSupport v.1 ∧
          (∀ y ∈ cylinder, u.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 (lam • x)))) ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            ∀ z ∈ closedBall (0 : R3) 1,
            u.1 =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam y
              (referenceRadius delta Rstar p L y) z)] (fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 (lam • x)))) ∧
          (∀ y ∈ cylinder, v.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 (lam • x)))) ∧
          ∃ V : Set R3, IsOpen V ∧
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
                closedBall (0 : R3) 1 ⊆ V) ∧
            (∀ x ∈ V, coordinateFluxDivergence
              (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) ∧
            ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
                lam delta Rstar p Psi u y =
              radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
                (S.Xi2 (lam • y))) ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        (∀ y ∈ cylinder, S.Xi1 (lam • y) ∉ tsupport s) →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z ∈ closedBall (0 : R3) 1, S.Xi1 (lam • packetEndpoint S L (cover.packet i)
            lam y (referenceRadius delta Rstar p L y) z) ∉ tsupport s) →
        (∀ y ∈ cylinder, S.Xi2 (lam • y) ∉ tsupport s) →
        (∀ y ∈ cylinder, lam • y ∈ S.W →
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
            (S.Xi1 (lam • y)) =
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
            (S.Xi2 (lam • y))) →
        ∀ (R1 R2 : R3 → ℝ) (O : Set R3), IsOpen O → cylinder ⊆ O →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z ∈ closedBall (0 : R3) 1,
            packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z ∈ O) →
        (∀ x ∈ O, R1 x = (lam^2)⁻¹ * radiusTwoSmoothSourceResponse S.hreg S.hcalc
          S.original1 S.original1_admissible s (S.Xi1 (lam • x))) →
        (∀ y ∈ cylinder, R2 y = (lam^2)⁻¹ * radiusTwoSmoothSourceResponse S.hreg S.hcalc
          S.original2 S.original2_admissible s (S.Xi2 (lam • y))) →
        ∀ C : ℝ, 0 ≤ C →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z : UnitSphere,
            |R1 (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z.val) -
              R1 y - fderiv ℝ R1 y
                (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z.val-y)| ≤
              C * (referenceRadius delta Rstar p L y)^2) →
        ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          |R2 y-R1 y| ≤ C * (referenceRadius delta Rstar p L y)^2 *
            ‖(sphereSobolevZeroEquiv hO hD).symm
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖
      ) ∧
      ∀ k : Fin 5, ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        |R2 k (y,lam) - R1 k (y,lam)| ≤
          C * (referenceRadius delta Rstar p L y)^2 *
            ‖(sphereSobolevZeroEquiv hO hD).symm
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖ := by
  obtain ⟨s, hs⟩ := exists_original_source_spatial_metric_jets_with_finite_cover_taylor
    S hFirst hSecond hMatch
  let v1 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
  let v2 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
  let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
  let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
  refine ⟨s, hs, ?_⟩
  intro L cover
  exact exists_native_five_source_moments_of_cover_taylor
    hcalc hreg hF hO hD τ0 hKernel S hFree hMatch s R1 R2 L cover (hs.2 L cover)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
