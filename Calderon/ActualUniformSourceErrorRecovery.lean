import Calderon.ActualOriginalSourceHessianErrorRecovery
import Calderon.OperatorApplicationFiniteJets
import Calderon.ActualSameSourceNormalizedAnalyticFamily
import Calderon.ActualSameSourceNormalizedCoefficientRecovery
import Calderon.ActualSourceFreeKnownSideRestriction
import Calderon.CompactInverseDerivativeBounds
import Calderon.NormalizedPrincipalMetricSmooth
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_uniform_original_source_hessian_error_recovery
    (S : KnownSideSourceData)
    (hFirst : ‖S.Xi1 0‖ ≤ 1) (hSecond : ‖S.Xi2 0‖ ≤ 1)
    (hMatch : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x)) :
    ∃ s : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ),
      let v1 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
      let v2 : Fin 5 → R3 → ℝ := fun k =>
        (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
      (∀ k : Fin 5,
        v1 k 0 = 0 ∧ fderiv ℝ (v1 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v1 k)) 0 = matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k) ∧
        v2 k 0 = 0 ∧ fderiv ℝ (v2 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v2 k)) 0 = matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)) ∧
      ∀ (L : ℝ) (K : Set R3), IsCompact K → ∀ N : ℕ,
        let E : (ℝ × R3) → Mat := fun t => referenceNormalizedPrincipalDifference S.g1 S.g2 L t.1 t.2
        let errors : (ℝ × R3) → (Fin 5 → Mat) := fun t k i j =>
          fderiv ℝ (fderiv ℝ (v1 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
          fderiv ℝ (fderiv ℝ (v2 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        ∃ (eta C : ℝ) (U : Set (ℝ × R3))
          (M : (ℝ × R3) → ((Fin 5 → Mat) →L[ℝ] Mat)),
          0 < eta ∧ eta ≤ 1 ∧ 1 ≤ C ∧ IsOpen U ∧
          Icc (-eta) eta ×ˢ K ⊆ U ∧
          (∀ t ∈ U, t.1 • t.2 ∈ S.coordinateRoom) ∧
          (∀ t ∈ U, ∀ k : Fin 5,
            S.Xi1 (t.1 • t.2) ∉ tsupport (s k) ∧ S.Xi2 (t.1 • t.2) ∉ tsupport (s k)) ∧
          @ContDiffOn ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
            (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
            (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞ M U ∧ ContDiffOn ℝ ∞ errors U ∧
          (∀ t ∈ U, E t = M t (errors t)) ∧
          (∀ n : ℕ, n ≤ N → ∀ t ∈ Icc (-eta) eta ×ˢ K, @norm _
              (@ContinuousMultilinearMap.hasOpNorm ℝ (Fin n) (fun _ => ℝ × R3)
                ((Fin 5 → Mat) →L[ℝ] Mat) _ _ _
                (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)).toSeminormedAddCommGroup
                (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) _)
              (@iteratedFDeriv ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
                  (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
                  (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) n M t) ≤ C) ∧
          (∀ n : ℕ, n ≤ N → ∀ t ∈ Icc (-eta) eta ×ˢ K,
            ‖iteratedFDeriv ℝ n E t‖ ≤
              C * ∑ i ∈ Finset.range (n + 1),
                (Nat.choose n i : ℝ) * ‖iteratedFDeriv ℝ (n-i) errors t‖) := by
  classical
  obtain ⟨s, hs⟩ := exists_original_source_hessian_error_recovery S hFirst hSecond hMatch
  let v1 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
  let v2 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
  refine ⟨s, hs.1, ?_⟩
  intro L K hK N
  let E : (ℝ × R3) → Mat := fun t =>
    referenceNormalizedPrincipalDifference S.g1 S.g2 L t.1 t.2
  let errors : (ℝ × R3) → (Fin 5 → Mat) := fun t k i j =>
    fderiv ℝ (fderiv ℝ (v1 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
    fderiv ℝ (fderiv ℝ (v2 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  obtain ⟨eta, U, M, hEta, hEta1, hU, hStrip, hRoom, hAvoid, hM, hErrors, hEq⟩ := hs.2 L K hK
  have hCompact : IsCompact (Icc (-eta) eta ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C0, hC0, hBound⟩ := @exists_compact_iteratedFDeriv_bound
    (ℝ × R3) ((Fin 5 → Mat) →L[ℝ] Mat) _ _
    (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ))
    M (Icc (-eta) eta ×ˢ K) hCompact
    (fun t ht => @ContDiffOn.contDiffAt ℝ _ (ℝ × R3) _ _
      ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ))
      U M t ∞ hM (hU.mem_nhds (hStrip ht))) N
  let C : ℝ := max C0 1
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC : 0 ≤ C := zero_le_one.trans hC1
  have hBoundC : ∀ n : ℕ, n ≤ N → ∀ t ∈ Icc (-eta) eta ×ˢ K,
      @norm _
        (@ContinuousMultilinearMap.hasOpNorm ℝ (Fin n) (fun _ => ℝ × R3)
          ((Fin 5 → Mat) →L[ℝ] Mat) _ _ _
          (ContinuousLinearMap.toNormedAddCommGroup
            (σ₁₂ := RingHom.id ℝ)).toSeminormedAddCommGroup
          (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) _)
        (@iteratedFDeriv ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
          (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
          (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) n M t) ≤ C := by
    intro n hn t ht
    exact (hBound n hn t ht).trans (le_max_left _ _)
  refine ⟨eta, C, U, M, hEta, hEta1, hC1, hU, hStrip, hRoom, hAvoid,
    hM, hErrors, hEq, hBoundC, ?_⟩
  exact @norm_iteratedFDeriv_clm_apply_le_uniform
    (ℝ × R3) _ _ (Fin 5 → Mat) _ _ Mat _ _
    M errors E U (Icc (-eta) eta ×ˢ K) N C
    hU hStrip hM hErrors hEq hC hBoundC

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
