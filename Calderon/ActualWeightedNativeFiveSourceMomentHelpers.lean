import Calderon.ActualUniformNativeFiveSourceMoments
import Calderon.ActualCoveredNativeSourceMomentL2
import Calderon.ReverseSourceCoordinateJetComparison
import Calderon.CoordinateH8FrechetRecovery

noncomputable section
open Set Metric Filter MeasureTheory
open scoped ENNReal ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceWeightedApproximation SphereHarmonic DirichletFamily.DriftBootstrap
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift CoordinateBootstrapJets
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_common_scale_coordinateH8_and_source_profile_smoothness
    (S : KnownSideSourceData) (L : ℝ)
    (R1 R2 : Fin 5 → (R3 × ℝ) → ℝ)
    (etaM : ℝ) (hEtaM : 0 < etaM)
    (etaA CA : ℝ) (U : Set (ℝ × R3))
    (hEtaA : 0 < etaA) (hCA : 1 ≤ CA) (hU : IsOpen U)
    (hStrip : Icc (-etaA) etaA ×ˢ cylinder ⊆ U)
    (hR1 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U))
    (hR2 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U))
    (hRecovery : ∀ lam ∈ Icc (-etaA) etaA, ∀ n : ℕ, n ≤ 8 → ∀ y ∈ cylinder,
      ‖iteratedFDeriv ℝ n (fun x => referenceNormalizedPrincipalDifference S.g1 S.g2 L lam x) y‖ ≤
        CA * ∑ i ∈ Finset.range (n+1), (Nat.choose n i : ℝ) *
          ∑ k : Fin 5, ‖iteratedFDeriv ℝ (n-i+2) (fun x => R1 k (x,lam)-R2 k (x,lam)) y‖) :
    ∃ eta C_H : ℝ, 0 < eta ∧ eta ≤ etaM ∧ 1 ≤ C_H ∧
          (∀ lam ∈ Icc (-eta) eta, ∀ y ∈ cylinder,
            coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
              C_H * ∑ k : Fin 5, ∑ alpha : Fin 3 → Fin 11,
                if (∑ j : Fin 3, (alpha j).val) ≤ 10 then
                  |(((coordinateDerivative 0)^[(alpha 0).val])
                    (((coordinateDerivative 1)^[(alpha 1).val])
                      (((coordinateDerivative 2)^[(alpha 2).val])
                        (fun x => R1 k (x,lam)-R2 k (x,lam))))) y| else 0) ∧
      ∀ lam ∈ Icc (-eta) eta,
        ∃ V : Set R3, IsOpen V ∧ cylinder ⊆ V ∧
          ∀ k : Fin 5, ContDiffOn ℝ ∞ (fun x : R3 => R1 k (x,lam)-R2 k (x,lam)) V := by
  obtain ⟨B,hB1,hB⟩ := exists_coordinateH8_le_source_jet_sum_of_binomial_recovery
  let eta : ℝ := min etaM etaA
  have hEta : 0 < eta := lt_min hEtaM hEtaA
  have hComparisonConstant : (1 : ℝ) ≤ 11 * (3 : ℝ)^10 := by norm_num
  have hLamA (lam : ℝ) (hLam : lam ∈ Icc (-eta) eta) :
      lam ∈ Icc (-etaA) etaA :=
    ⟨(neg_le_neg (min_le_right etaM etaA)).trans hLam.1,
      hLam.2.trans (min_le_right etaM etaA)⟩
  have hSliceData (lam : ℝ) (hLam : lam ∈ Icc (-eta) eta) :
      ∃ V : Set R3, IsOpen V ∧ cylinder ⊆ V ∧
        ∀ k : Fin 5, ContDiffOn ℝ ∞ (fun x : R3 => R1 k (x,lam)-R2 k (x,lam)) V := by
    let V : Set R3 := (fun x : R3 => (lam,x)) ⁻¹' U
    have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
    have hCylinderV : cylinder ⊆ V := fun y hy => hStrip ⟨hLamA lam hLam,hy⟩
    have hSlice : ContDiff ℝ ∞ (fun x : R3 => (x,lam)) :=
      contDiff_id.prodMk contDiff_const
    have hRange : MapsTo (fun x : R3 => (x,lam)) V (Prod.swap ⁻¹' U) :=
      fun _ hx => hx
    refine ⟨V,hV,hCylinderV,?_⟩
    intro k
    exact ((hR1 k).comp hSlice.contDiffOn hRange).sub
      ((hR2 k).comp hSlice.contDiffOn hRange)
  have hMetricSmooth (lam : ℝ) : @ContDiff ℝ _ R3 _ _
      (Matrix (Fin 3) (Fin 3) ℝ) Matrix.normedAddCommGroup Matrix.normedSpace ∞
      (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_referenceNormalizedPrincipalDifference_entry
      S.g1 S.g2 S.g1_admissible S.g2_admissible L lam i j
  refine ⟨eta,(B*CA)*(11*(3:ℝ)^10),hEta,min_le_left etaM etaA,
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB1 hCA)
      hComparisonConstant,?_,hSliceData⟩
  intro lam hLam y hy
  obtain ⟨V,hV,hCylinderV,hProfiles⟩ := hSliceData lam hLam
  let F : Fin 5 → R3 → ℝ := fun k x => R1 k (x,lam)-R2 k (x,lam)
  have hRecover := hB (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam)
    (hMetricSmooth lam) F CA (zero_le_one.trans hCA) y
    (fun n hn => hRecovery lam (hLamA lam hLam) n hn y hy)
  have hCompare :=
    ReverseSourceCoordinateJetComparison.five_source_sum_norm_iteratedFDeriv_le_sourceCoordinateJetSum_on
      V hV F hProfiles y (hCylinderV hy)
  have hLiteral : coordinateH8
      (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
      (B*CA)*(11*(3:ℝ)^10) * ∑ k : Fin 5,
        ReverseSourceCoordinateJetComparison.sourceCoordinateJetSum (F k) y := by
    exact hRecover.trans (by
      calc B*CA * (∑ k : Fin 5, ∑ n ∈ Finset.range 11,
              ‖iteratedFDeriv ℝ n (F k) y‖)
          ≤ B*CA * ((11*(3:ℝ)^10) * ∑ k : Fin 5,
              ReverseSourceCoordinateJetComparison.sourceCoordinateJetSum (F k) y) :=
            mul_le_mul_of_nonneg_left hCompare
              (mul_nonneg (zero_le_one.trans hB1) (zero_le_one.trans hCA))
        _ = _ := by ring)
  simpa only [ReverseSourceCoordinateJetComparison.sourceCoordinateJetSum_eq_literal]
    using hLiteral

theorem exists_weighted_native_five_source_moments_of_profile_recovery
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (R1 R2 : Fin 5 → (R3 × ℝ) → ℝ)
    (etaM C : ℝ) (hEtaM : 0 < etaM)
    (hEtaMCover : etaM ≤ cover.dilationCeiling) (hC : 1 ≤ C)
    (hMomentFactory :
        ∀ (lam delta Rstar bound separation : ℝ) (p : ℕ)
          (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover),
          0 < delta → 0 < Rstar → 0 < lam → lam ≤ etaM →
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
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖)
    (etaA CA : ℝ) (U : Set (ℝ × R3))
    (hEtaA : 0 < etaA) (hCA : 1 ≤ CA) (hU : IsOpen U)
    (hStrip : Icc (-etaA) etaA ×ˢ cylinder ⊆ U)
    (hR1 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U))
    (hR2 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U))
    (hRecovery : ∀ lam ∈ Icc (-etaA) etaA, ∀ n : ℕ, n ≤ 8 → ∀ y ∈ cylinder,
      ‖iteratedFDeriv ℝ n (fun x => referenceNormalizedPrincipalDifference S.g1 S.g2 L lam x) y‖ ≤
        CA * ∑ i ∈ Finset.range (n+1), (Nat.choose n i : ℝ) *
          ∑ k : Fin 5, ‖iteratedFDeriv ℝ (n-i+2) (fun x => R1 k (x,lam)-R2 k (x,lam)) y‖) :
        ∃ eta C_H : ℝ,
          0 < eta ∧ eta ≤ cover.dilationCeiling ∧ 1 ≤ C ∧ 1 ≤ C_H ∧
          (∀ lam ∈ Icc (-eta) eta, ∀ y ∈ cylinder,
            coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
              C_H * ∑ k : Fin 5, ∑ alpha : Fin 3 → Fin 11,
                if (∑ j : Fin 3, (alpha j).val) ≤ 10 then
                  |(((coordinateDerivative 0)^[(alpha 0).val])
                    (((coordinateDerivative 1)^[(alpha 1).val])
                      (((coordinateDerivative 2)^[(alpha 2).val])
                        (fun x => R1 k (x,lam)-R2 k (x,lam))))) y| else 0) ∧
        ∀ (lam delta Rstar bound separation : ℝ) (p : ℕ)
          (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover),
          0 < delta → 0 < Rstar → 0 < lam → lam ≤ eta →
          (∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) →
    ∃ Psi : R3 → SphereSobolev (3/2 : ℝ),
      (
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
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖
      ) ∧
      ∀ (μ : Measure R3) [IsFiniteMeasureOnCompacts μ],
        ∀ (chi : R3 → ℝ), Continuous chi → ∀ k : Fin 5,
          MemLp (fun y => chi y * (R1 k (y,lam)-R2 k (y,lam)) /
            (referenceRadius delta Rstar p L y)^2) 2 (μ.restrict cylinder) ∧
          eLpNorm (fun y => chi y * (R1 k (y,lam)-R2 k (y,lam)) /
            (referenceRadius delta Rstar p L y)^2) 2 (μ.restrict cylinder) ≤
            ENNReal.ofReal C * eLpNorm (fun y => chi y •
              (sphereSobolevZeroEquiv hO hD).symm
                (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)))
              2 (μ.restrict cylinder) := by
  obtain ⟨eta,C_H,hEta,hEtaMle,hCH,hH8,hSliceData⟩ :=
    exists_common_scale_coordinateH8_and_source_profile_smoothness
      S L R1 R2 etaM hEtaM etaA CA U hEtaA hCA hU hStrip hR1 hR2 hRecovery
  refine ⟨eta,C_H,hEta,hEtaMle.trans hEtaMCover,hC,hCH,hH8,?_⟩
  intro lam delta Rstar bound separation p K hDelta hRstar hLam hLamEta hRadius
  have hLamM : lam ≤ etaM := hLamEta.trans hEtaMle
  have hLamSigned : lam ∈ Icc (-eta) eta :=
    ⟨(neg_nonpos.mpr hEta.le).trans hLam.le,hLamEta⟩
  have hNative :
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
    exact hMomentFactory lam delta Rstar bound separation p K hDelta hRstar hLam hLamM hRadius
  rcases hNative with ⟨Psi,hPsi⟩
  refine ⟨Psi,hPsi,?_⟩
  intro μ hMu chi hChi k
  obtain ⟨V,hV,hCylinderV,hProfiles⟩ := hSliceData lam hLamSigned
  have hContinuous : ContinuousOn
      (fun x : R3 => R1 k (x,lam)-R2 k (x,lam)) cylinder :=
    (hProfiles k).continuousOn.mono hCylinderV
  have hMoment : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      |R1 k (y,lam)-R2 k (y,lam)| ≤ C * (referenceRadius delta Rstar p L y)^2 *
        ‖(sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))‖ := by
    intro i y hy
    rw [abs_sub_comm]
    exact hPsi.2 k i y hy
  exact memLp_covered_native_source_moment_and_eLpNorm_le
    S L cover hO hD Psi hPsi.1.1 hPsi.1.2.1 μ chi
    (fun x : R3 => R1 k (x,lam)-R2 k (x,lam)) hChi hContinuous
    delta Rstar p hDelta hRstar C (zero_le_one.trans hC) hMoment

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
