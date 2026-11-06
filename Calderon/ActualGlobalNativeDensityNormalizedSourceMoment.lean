import Calderon.ActualOriginalSourceTransferReproduction
import Calderon.ActualNormalizedSourceMoment
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ExteriorSource
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift

theorem exists_global_native_density_normalized_original_source_moments
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
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
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖ := by
  classical
  obtain ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass,hPair,hCoord,hSource⟩ :=
    exists_global_native_density_original_source_reproduction
      hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass,hPair,hCoord,hSource,?_⟩
  intro s hCyl1 hBall1 hCyl2 hMatch R1 R2 O hOpen hCylinderO hEndpointsO hNorm1 hNorm2 C hC hTaylor
  let c : ℝ := (lam^2)⁻¹
  have hSupport : tsupport (c • s : 𝓓(fixedExteriorSourceOpens, ℝ)) ⊆ tsupport s := by
    change tsupport (fun x => c • s x) ⊆ tsupport s
    exact tsupport_smul_subset_right (fun _ : R3 => c) s
  have hMatchScaled : ∀ y ∈ cylinder, lam • y ∈ S.W →
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible
        (c • s) (S.Xi1 (lam • y)) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible
        (c • s) (S.Xi2 (lam • y)) := by
    intro y hy hW
    rw [radiusTwoSmoothSourceResponse_smul, radiusTwoSmoothSourceResponse_smul]
    exact congrArg (fun v : ℝ => c • v) (hMatch y hy hW)
  obtain ⟨u,v,hCu,hCv,hGerm,hEndpointGerm,hSecondGerm,V,hV,hBallV,hPDEu,hReproduce⟩ :=
    hSource (c • s)
      (fun y hy hx => hCyl1 y hy (hSupport hx))
      (fun i y hy z hz hx => hBall1 i y hy z hz (hSupport hx))
      (fun y hy hx => hCyl2 y hy (hSupport hx)) hMatchScaled
  intro i y hy
  have hSphere (z : UnitSphere) : z.val ∈ closedBall (0 : R3) 1 :=
    sphere_subset_closedBall z.property
  exact nativeMixedKernelDensityFunctional_normalized_original_source_moment_le
    hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi s u R1 R2 y O hOpen
    (hCylinderO hy.1) C hC (fun z => hEndpointsO i y hy z.val (hSphere z))
    hNorm1 (hNorm2 y hy.1) (hGerm y hy.1)
    (fun z => hEndpointGerm i y hy z.val (hSphere z)) (hReproduce i y hy)
    (hMass i y hy) (fun k => hCoord k i y hy) (hTaylor i y hy)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
