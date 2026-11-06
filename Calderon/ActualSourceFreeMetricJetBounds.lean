import Calderon.ActualSourceFreeHessianErrorRecovery
import Calderon.ActualSourceSpatialMetricJetRecovery
import Calderon.ActualOriginalSourceHessianErrorRecovery
import Calderon.OperatorApplicationFiniteJets
import Calderon.ActualSameSourceNormalizedAnalyticFamily
import Calderon.ActualSameSourceNormalizedCoefficientRecovery
import Calderon.ActualSourceFreeKnownSideRestriction
import Calderon.CompactInverseDerivativeBounds
import Calderon.NormalizedPrincipalMetricSmooth
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Calderon.ActualUniformSourceErrorRecovery
import Calderon.ActualNormalizedPairHessianFiniteJets
import Calderon.SpatialSourceJetRecoveryBounds
import Calderon.HessianDifferenceGerm
import Mathlib.Tactic.Linarith
import Calderon.ActualSourceSpatialMetricJetRecoveryWithFiniteJets
import Calderon.FiniteCoverSourceTaylorBounds
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_uniform_original_source_hessian_error_recovery_of_source_free_room
    (S : KnownSideSourceData)
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
  obtain ⟨s, hs⟩ := exists_original_source_hessian_error_recovery_of_source_free_room S hFree hMatch
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

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

/-- Smooth joint functions restrict to smooth spatial slices with the supplied norm. -/
theorem exists_original_source_spatial_metric_jet_recovery_of_source_free_room
    (S : KnownSideSourceData)
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
      (∀ k : Fin 5,
        v1 k 0 = 0 ∧ fderiv ℝ (v1 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v1 k)) 0 = matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k) ∧
        v2 k 0 = 0 ∧ fderiv ℝ (v2 k) 0 = 0 ∧
        fderiv ℝ (fderiv ℝ (v2 k)) 0 = matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)) ∧
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
                  (fun x => R1 k (x, lam) - R2 k (x, lam)) y‖) := by
  classical
  obtain ⟨s, hs⟩ := exists_uniform_original_source_hessian_error_recovery_of_source_free_room S hFree hMatch
  let v1 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
  let v2 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
  let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
  let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
  let B : Fin 5 → R3 →L[ℝ] R3 →L[ℝ] ℝ := fun k =>
    matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)
  have hJets1 (k : Fin 5) : v1 k 0 = 0 ∧ fderiv ℝ (v1 k) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (v1 k)) 0 = B k :=
    ⟨(hs.1 k).1, (hs.1 k).2.1, (hs.1 k).2.2.1⟩
  have hJets2 (k : Fin 5) : v2 k 0 = 0 ∧ fderiv ℝ (v2 k) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (v2 k)) 0 = B k :=
    ⟨(hs.1 k).2.2.2.1, (hs.1 k).2.2.2.2.1, (hs.1 k).2.2.2.2.2⟩
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp
    (S.coordinateRoom_open.mem_nhds S.origin_mem)
  have hv1 (k : Fin 5) : ContDiffOn ℝ ∞ (v1 k) (ball (0 : R3) r) :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original1
      S.original1_admissible (s k)).2.1.comp S.Xi1_smooth S.Xi1_room).mono hBall
  have hv2 (k : Fin 5) : ContDiffOn ℝ ∞ (v2 k) (ball (0 : R3) r) :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original2
      S.original2_admissible (s k)).2.1.comp S.Xi2_smooth S.Xi2_room).mono hBall
  refine ⟨s, hs.1, ?_⟩
  intro L K hK N
  let E : (ℝ × R3) → Mat := fun t =>
    referenceNormalizedPrincipalDifference S.g1 S.g2 L t.1 t.2
  let errors : (ℝ × R3) → (Fin 5 → Mat) := fun t k i j =>
    fderiv ℝ (fderiv ℝ (v1 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
    fderiv ℝ (fderiv ℝ (v2 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  obtain ⟨etaM, C, UM, M, hEtaM, hEtaM1, hC1, hUM, hStripM, hRoom, hAvoid,
    hM, hErrors, hEq, hBoundM, hJointRecovery⟩ := hs.2 L K hK N
  obtain ⟨etaT, CT, UT, hEtaT, hEtaT1, hCT, hUT, hStripT, hTaylorRoom,
    hR1, hR2, hNorm1, hNorm2, hZero, hJoint1, hJoint2, hSpatial1, hSpatial2,
    hH1, hH2, hZeroH⟩ :=
    exists_normalized_pair_hessian_compact_finite_jet_bound
      v1 v2 B r hr hv1 hv2 hJets1 hJets2 K hK 0
  let eta : ℝ := min etaM etaT
  let U : Set (ℝ × R3) := UM ∩ Prod.swap ⁻¹' UT
  have hEta : 0 < eta := lt_min hEtaM hEtaT
  have hEta_le_M : eta ≤ etaM := min_le_left _ _
  have hEta_le_T : eta ≤ etaT := min_le_right _ _
  have hEta1 : eta ≤ 1 := hEta_le_M.trans hEtaM1
  have hC : 0 ≤ C := zero_le_one.trans hC1
  have hU : IsOpen U := hUM.inter (hUT.preimage continuous_swap)
  have hLamM (lam : ℝ) (hlam : lam ∈ Icc (-eta) eta) : lam ∈ Icc (-etaM) etaM := by
    constructor <;> linarith [hlam.1, hlam.2]
  have hLamT (lam : ℝ) (hlam : lam ∈ Icc (-eta) eta) : lam ∈ Icc (-etaT) etaT := by
    constructor <;> linarith [hlam.1, hlam.2]
  have hStrip : Icc (-eta) eta ×ˢ K ⊆ U := by
    intro t ht
    exact ⟨hStripM ⟨hLamM t.1 ht.1, ht.2⟩, hStripT ⟨ht.2, hLamT t.1 ht.1⟩⟩
  have hSwapSub : Prod.swap ⁻¹' U ⊆ UT := by
    intro z hz
    exact hz.2
  have hMU : @ContDiffOn ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞ M U :=
    @ContDiffOn.mono ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) UM M ∞ hM U inter_subset_left
  have hErrorsU : ContDiffOn ℝ ∞ errors U := hErrors.mono inter_subset_left
  refine ⟨eta, C, U, hEta, hEta1, hC1, hU, hStrip,
    (fun t ht => hRoom t ht.1), (fun t ht k => hAvoid t ht.1 k),
    (fun k => (hR1 k).mono hSwapSub), (fun k => (hR2 k).mono hSwapSub), ?_⟩
  intro lam hlam
  let Ulam : Set R3 := (fun x : R3 => (lam, x)) ⁻¹' U
  have hUlam : IsOpen Ulam := hU.preimage (continuous_const.prodMk continuous_id)
  have hKUlam : K ⊆ Ulam := fun y hy => hStrip ⟨hlam, hy⟩
  have hMSlice : @ContDiffOn ℝ _ R3 _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞
      (fun x : R3 => M (lam, x)) Ulam :=
    @contDiffOn_real_prod_slice_snd ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) M U hMU lam
  have hErrorsSlice : ContDiffOn ℝ ∞ (fun x : R3 => errors (lam, x)) Ulam :=
    contDiffOn_real_prod_slice_snd errors U hErrorsU lam
  have hEqSlice (x : R3) (hx : x ∈ Ulam) :
      E (lam, x) = M (lam, x) (errors (lam, x)) := hEq (lam, x) hx.1
  have hSliceBound : ∀ i : ℕ, i ≤ N → ∀ y ∈ K,
      @norm _
        (@ContinuousMultilinearMap.hasOpNorm ℝ (Fin i) (fun _ => R3)
          ((Fin 5 → Mat) →L[ℝ] Mat) _ _ _
          (ContinuousLinearMap.toNormedAddCommGroup
            (σ₁₂ := RingHom.id ℝ)).toSeminormedAddCommGroup
          (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) _)
        (@iteratedFDeriv ℝ _ R3 _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
          (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
          (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) i
          (fun x : R3 => M (lam, x)) y) ≤ C := by
    intro i hi y hy
    have hMAt : @ContDiffAt ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
        (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
        (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞ M (lam, y) :=
      @ContDiffOn.contDiffAt ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
        (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
        (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) UM M (lam, y) ∞ hM
        (hUM.mem_nhds (hStripM ⟨hLamM lam hlam, hy⟩))
    exact (@norm_iteratedFDeriv_prod_slice_snd_le ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) M lam y hMAt i).trans
      (hBoundM i hi (lam, y) ⟨hLamM lam hlam, hy⟩)
  have hLeibniz := @norm_iteratedFDeriv_clm_apply_le_uniform
    R3 _ _ (Fin 5 → Mat) _ _ Mat _ _
    (fun x : R3 => M (lam, x)) (fun x : R3 => errors (lam, x))
    (fun x : R3 => E (lam, x)) Ulam K N C hUlam hKUlam
    hMSlice hErrorsSlice hEqSlice hC hSliceBound
  have hR1Slice (k : Fin 5) : ContDiffOn ℝ ∞ (fun x : R3 => R1 k (x, lam)) Ulam :=
    (hR1 k).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun x hx => hx.2)
  have hR2Slice (k : Fin 5) : ContDiffOn ℝ ∞ (fun x : R3 => R2 k (x, lam)) Ulam :=
    (hR2 k).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun x hx => hx.2)
  let F : Fin 5 → R3 → ℝ := fun k x => R1 k (x, lam) - R2 k (x, lam)
  have hF (k : Fin 5) : ContDiffOn ℝ ∞ (F k) Ulam := (hR1Slice k).sub (hR2Slice k)
  let Herrors : R3 → (Fin 5 → Mat) := fun x k i j =>
    fderiv ℝ (fderiv ℝ (F k)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hErrorEqOn : EqOn (fun x : R3 => errors (lam, x)) Herrors Ulam := by
    intro x hx
    have hxT : (x, lam) ∈ UT := hx.2
    ext k i j
    have hHess : fderiv ℝ (fderiv ℝ (F k)) x =
        fderiv ℝ (fderiv ℝ (v1 k)) (lam • x) -
        fderiv ℝ (fderiv ℝ (v2 k)) (lam • x) := by
      rw [fderiv_fderiv_fun_sub_of_contDiffAt
        (fun z : R3 => R1 k (z, lam)) (fun z : R3 => R2 k (z, lam)) x
        ((hR1Slice k).contDiffAt (hUlam.mem_nhds hx))
        ((hR2Slice k).contDiffAt (hUlam.mem_nhds hx)), hH1 k (x, lam) hxT,
        hH2 k (x, lam) hxT]
    change fderiv ℝ (fderiv ℝ (v1 k)) (lam • x)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      fderiv ℝ (fderiv ℝ (v2 k)) (lam • x)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      fderiv ℝ (fderiv ℝ (F k)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    rw [hHess]
    rfl
  have hErrorJet (m : ℕ) (y : R3) (hy : y ∈ K) :
      ‖iteratedFDeriv ℝ m (fun x : R3 => errors (lam, x)) y‖ ≤
        ∑ k : Fin 5, ‖iteratedFDeriv ℝ (m + 2) (F k) y‖ := by
    have hGerm : (fun x : R3 => errors (lam, x)) =ᶠ[𝓝 y] Herrors := by
      filter_upwards [hUlam.mem_nhds (hKUlam hy)] with x hx
      exact hErrorEqOn hx
    have hD := (hGerm.iteratedFDeriv ℝ m).eq_of_nhds
    rw [hD]
    exact norm_iteratedFDeriv_coordinateHessian_family_le_sum F y
      (fun k => (hF k).contDiffAt (hUlam.mem_nhds (hKUlam hy))) m
  intro n hn y hy
  apply (hLeibniz n hn y hy).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hErrorJet (n - i) y hy) (Nat.cast_nonneg _)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_original_source_spatial_metric_jet_recovery_with_finite_jets_of_source_free_room
    (S : KnownSideSourceData)
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
      (∀ k : Fin 5,
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
                  (fun x => R1 k (x, lam) - R2 k (x, lam)) y‖) := by
  classical
  obtain ⟨s, hs⟩ := exists_original_source_spatial_metric_jet_recovery_of_source_free_room S hFree hMatch
  let v1 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
  let v2 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
  let B : Fin 5 → R3 →L[ℝ] R3 →L[ℝ] ℝ := fun k =>
    matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)
  have hJets1 (k : Fin 5) : v1 k 0 = 0 ∧ fderiv ℝ (v1 k) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (v1 k)) 0 = B k :=
    ⟨(hs.1 k).1, (hs.1 k).2.1, (hs.1 k).2.2.1⟩
  have hJets2 (k : Fin 5) : v2 k 0 = 0 ∧ fderiv ℝ (v2 k) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (v2 k)) 0 = B k :=
    ⟨(hs.1 k).2.2.2.1, (hs.1 k).2.2.2.2.1, (hs.1 k).2.2.2.2.2⟩
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp
    (S.coordinateRoom_open.mem_nhds S.origin_mem)
  have hv1 (k : Fin 5) : ContDiffOn ℝ ∞ (v1 k) (ball (0 : R3) r) :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original1
      S.original1_admissible (s k)).2.1.comp S.Xi1_smooth S.Xi1_room).mono hBall
  have hv2 (k : Fin 5) : ContDiffOn ℝ ∞ (v2 k) (ball (0 : R3) r) :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original2
      S.original2_admissible (s k)).2.1.comp S.Xi2_smooth S.Xi2_room).mono hBall
  refine ⟨s, hs.1, ?_, hs.2⟩
  refine ⟨r, hr, hBall, ?_⟩
  intro K hK N
  exact exists_normalized_pair_hessian_compact_finite_jet_bound
    v1 v2 B r hr hv1 hv2 hJets1 hJets2 K hK N

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_original_source_spatial_metric_jets_with_finite_cover_taylor_of_source_free_room
    (S : KnownSideSourceData)
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
                  (packetEndpoint S L (cover.packet i) lam y r z-y)| ≤ C*r^2) := by
  classical
  obtain ⟨s,hs⟩ := exists_original_source_spatial_metric_jet_recovery_with_finite_jets_of_source_free_room
    S hFree hMatch
  refine ⟨s,hs,?_⟩
  intro L cover
  obtain ⟨B,hB,hCylB,hBig⟩ := exists_uniform_finite_cover_source_taylor_bound S L cover
  obtain ⟨r,hr,hRoom,hAnalytic⟩ := hs.2.1
  obtain ⟨etaT,A,UT,hEtaT,hEtaT1,hA,hUT,hStripT,hTaylorRoom,hR1,hR2,
    hNorm1,hNorm2,hZero,hJoint1,hJoint2,hSpatial1,hSpatial2,hH1,hH2,hZeroH⟩ :=
    hAnalytic (closedBall (0 : R3) B) (isCompact_closedBall _ _) 2
  let U : Set (ℝ × R3) := Prod.swap ⁻¹' UT
  have hU : IsOpen U := hUT.preimage continuous_swap
  have hStrip : Icc (-etaT) etaT ×ˢ closedBall (0 : R3) B ⊆ U := by
    intro t ht
    exact hStripT ⟨ht.2,ht.1⟩
  let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ =>
      ((radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1)
        (t • z.1)) z.2
  change (∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) UT) at hR1
  have hProfile (k : Fin 5) :
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ i : Fin cover.count, ∀ lam ∈ Icc (0 : ℝ) (min etaT cover.dilationCeiling),
        ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ r ∈ Icc (0 : ℝ) cover.radiusCeiling, ∀ z ∈ closedBall (0 : R3) 1,
          (∀ a ∈ Icc (0 : ℝ) 1,
            (lam,y+a • (packetEndpoint S L (cover.packet i) lam y r z-y)) ∈ U) ∧
          (lam,packetEndpoint S L (cover.packet i) lam y r z) ∈ U ∧
          |R1 k (packetEndpoint S L (cover.packet i) lam y r z,lam) - R1 k (y,lam) -
            fderiv ℝ (fun x : R3 => R1 k (x,lam)) y
                (packetEndpoint S L (cover.packet i) lam y r z-y)| ≤ C*r^2 := by
    have hSwap : ContDiff ℝ ∞ (Prod.swap : (ℝ × R3) → (R3 × ℝ)) :=
      contDiff_snd.prodMk contDiff_fst
    have hSmooth : ContDiffOn ℝ ∞ (fun z : ℝ × R3 => R1 k (z.2,z.1)) U :=
      (hR1 k).comp hSwap.contDiffOn (fun x hx => hx)
    have hBound : ∀ lam ∈ Icc (-etaT) etaT, ∀ x ∈ closedBall (0 : R3) B,
        ‖iteratedFDeriv ℝ 2 (fun y : R3 => R1 k (y,lam)) x‖ ≤ A := by
      intro lam hLam x hx
      exact hSpatial1 k lam hLam 2 le_rfl x hx
    exact hBig (fun z : ℝ × R3 => R1 k (z.2,z.1)) etaT A U
      hEtaT hA hU hSmooth hStrip hBound
  choose Ck hCk hBounds using hProfile
  let eta : ℝ := min etaT cover.dilationCeiling
  let C : ℝ := max 1 (∑ k : Fin 5, Ck k)
  have hCk0 (k : Fin 5) : 0 ≤ Ck k := zero_le_one.trans (hCk k)
  have hCkC (k : Fin 5) : Ck k ≤ C :=
    (Finset.single_le_sum (fun j _ => hCk0 j) (Finset.mem_univ k)).trans (le_max_right _ _)
  have hEta : 0 < eta := lt_min hEtaT cover.dilation_positive
  refine ⟨eta,C,U,hEta,min_le_right _ _,le_max_left _ _,hU,?_,?_,?_,?_⟩
  · intro t ht
    apply hStrip
    refine ⟨?_,ball_subset_closedBall (hCylB ht.2)⟩
    constructor <;> linarith [ht.1.1,ht.1.2,min_le_left etaT cover.dilationCeiling]
  · intro k t ht hNe
    exact hNorm1 k (t.2,t.1) ht hNe
  · intro k t ht hNe
    exact hNorm2 k (t.2,t.1) ht hNe
  · intro k i lam hLam y hy r hr z hz
    obtain ⟨hSegment,hEndpoint,hBound⟩ := hBounds k i lam hLam y hy r hr z hz
    exact ⟨hSegment,hEndpoint,hBound.trans (mul_le_mul_of_nonneg_right (hCkC k) (sq_nonneg r))⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
