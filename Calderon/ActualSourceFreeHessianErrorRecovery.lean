import Calderon.ActualSourceFreeNormalizedAnalyticFamily
import Calderon.ActualSameSourceNormalizedCoefficientRecovery
import Calderon.ActualSourceFreeKnownSideRestriction
import Calderon.ActualHessianErrorRows
import Calderon.NormalizedPrincipalMetricSmooth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_original_source_hessian_error_recovery_of_source_free_room
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
      ∀ (L : ℝ) (K : Set R3), IsCompact K →
        let E : (ℝ × R3) → Mat := fun t => referenceNormalizedPrincipalDifference S.g1 S.g2 L t.1 t.2
        let errors : (ℝ × R3) → (Fin 5 → Mat) := fun t k i j =>
          fderiv ℝ (fderiv ℝ (v1 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
          fderiv ℝ (fderiv ℝ (v2 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
        ∃ (eta : ℝ) (U : Set (ℝ × R3))
          (M : (ℝ × R3) → ((Fin 5 → Mat) →L[ℝ] Mat)),
          0 < eta ∧ eta ≤ 1 ∧ IsOpen U ∧
          Icc (-eta) eta ×ˢ K ⊆ U ∧
          (∀ t ∈ U, t.1 • t.2 ∈ S.coordinateRoom) ∧
          (∀ t ∈ U, ∀ k : Fin 5,
            S.Xi1 (t.1 • t.2) ∉ tsupport (s k) ∧ S.Xi2 (t.1 • t.2) ∉ tsupport (s k)) ∧
          @ContDiffOn ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
            (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
            (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞ M U ∧
          ContDiffOn ℝ ∞ errors U ∧
          (∀ t ∈ U, E t = M t (errors t)) := by
  classical
  obtain ⟨s, hs⟩ := exists_same_source_normalized_analytic_family_of_source_free_room S hFree hMatch
  let v1 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
  let v2 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
  rcases hs with ⟨hJets, r, hr, hBall, hTaylor, hInverse⟩
  refine ⟨s, hJets, ?_⟩
  intro L K hK
  let E : (ℝ × R3) → Mat := fun t =>
    referenceNormalizedPrincipalDifference S.g1 S.g2 L t.1 t.2
  let errors : (ℝ × R3) → (Fin 5 → Mat) := fun t k i j =>
    fderiv ℝ (fderiv ℝ (v1 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
    fderiv ℝ (fderiv ℝ (v2 k)) (t.1 • t.2) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  let H : (ℝ × R3) → Fin 5 → Mat := fun t k i j =>
    fderiv ℝ (fderiv ℝ (v1 k)) (t.1 • t.2)
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  let gamma : (ℝ × R3) → Mat := fun t =>
    Real.exp (-2 * L * referenceCoordinateDepth t.2) • S.g1 (t.1 • t.2)
  obtain ⟨A, hARows, eta0, C0, U0, hEta0, hEta01, hC0, hU0,
    hStrip0, hAroom, hASmooth, hInvert, hInvSmooth, hABound, hInvBound⟩ :=
    hInverse L K hK 0
  have hARow (t : ℝ × R3) (Z : Mat) :
      A t Z =
        ![![matrixContractionL (H t 0) Z,
            matrixContractionL (H t 1) Z,
            matrixContractionL (H t 2) Z],
          ![matrixContractionL (H t 3) Z,
            matrixContractionL (H t 4) Z,
            matrixContractionL (gamma t) Z],
          ![Z 0 1 - Z 1 0, Z 0 2 - Z 2 0, Z 1 2 - Z 2 1]] :=
    hARows t Z
  let scale : (ℝ × R3) → R3 := fun t => t.1 • t.2
  have hScale : ContDiff ℝ ∞ scale := contDiff_fst.smul contDiff_snd
  let U : Set (ℝ × R3) := U0 ∩ scale ⁻¹' S.coordinateRoom
  have hU : IsOpen U := hU0.inter (S.coordinateRoom_open.preimage hScale.continuous)
  have hZero : ({(0 : ℝ)} : Set ℝ) ×ˢ K ⊆ U := by
    rintro ⟨lam, y⟩ ⟨hlam, hy⟩
    have hlam0 : lam = 0 := Set.mem_singleton_iff.mp hlam
    subst lam
    refine ⟨hStrip0 ⟨?_, hy⟩, ?_⟩
    · constructor <;> linarith
    · change (0 : ℝ) • y ∈ S.coordinateRoom
      simpa only [zero_smul] using S.origin_mem
  obtain ⟨u, w, hu, hw, h0u, hKw, hProduct⟩ :=
    generalized_tube_lemma isCompact_singleton hK hU hZero
  have h0uPoint : (0 : ℝ) ∈ u := h0u (by simp)
  obtain ⟨d, hd, hdu⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds h0uPoint)
  let eta : ℝ := min 1 (d / 2)
  have hEta : 0 < eta := lt_min zero_lt_one (half_pos hd)
  have hEta1 : eta ≤ 1 := min_le_left _ _
  have hEtad : eta ≤ d / 2 := min_le_right _ _
  have hStrip : Icc (-eta) eta ×ˢ K ⊆ U := by
    intro t ht
    apply hProduct
    refine ⟨hdu ?_, hKw ht.2⟩
    have hAbs : |t.1| ≤ eta := abs_le.mpr ht.1
    have hLt : |t.1| < d := lt_of_le_of_lt hAbs (by linarith)
    simpa only [mem_ball_zero_iff, Real.norm_eq_abs] using hLt
  have hScaledRoom (t : ℝ × R3) (ht : t ∈ U) : t.1 • t.2 ∈ S.coordinateRoom :=
    ht.2
  have hAvoid (t : ℝ × R3) (ht : t ∈ U) (k : Fin 5) :
      S.Xi1 (t.1 • t.2) ∉ tsupport (s k) ∧
      S.Xi2 (t.1 • t.2) ∉ tsupport (s k) := by
    have hOutside := hFree (scale t) ht.2
    constructor
    · intro hIn
      exact hOutside.1 (subset_closure ((s k).tsupport_subset hIn))
    · intro hIn
      exact hOutside.2 (subset_closure ((s k).tsupport_subset hIn))
  let b : (ℝ × R3) → Mat := fun t =>
    referenceNormalizedPrincipalMatrix S.g1 S.g2 L t.1 t.2
  obtain ⟨B, hB, hBRows⟩ := exists_smooth_hessian_error_rows b
    (fun a c => contDiff_referenceNormalizedPrincipalMatrix_entry_joint
      S.g1 S.g2 S.g1_admissible S.g2_admissible L a c)
  let M : (ℝ × R3) → ((Fin 5 → Mat) →L[ℝ] Mat) := fun t =>
    (A t).inverse.comp (B t)
  have hM : @ContDiffOn ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
      (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞ M U := by
    have hInvU : @ContDiffOn ℝ _ (ℝ × R3) _ _ (Mat →L[ℝ] Mat)
        (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
        (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞
        (fun t => (A t).inverse) U :=
      @ContDiffOn.mono ℝ _ (ℝ × R3) _ _ (Mat →L[ℝ] Mat)
        (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
        (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) U0
        (fun t => (A t).inverse) ∞ hInvSmooth U inter_subset_left
    have hBU : @ContDiffOn ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
        (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
        (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) ∞ B U :=
      @ContDiff.contDiffOn ℝ _ (ℝ × R3) _ _ ((Fin 5 → Mat) →L[ℝ] Mat)
        (ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ))
        (ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)) U B ∞ hB
    exact ContDiffOn.clm_comp (E := Fin 5 → Mat) (F := Mat) (G := Mat) hInvU hBU
  have hv1 (k : Fin 5) : ContDiffOn ℝ ∞ (v1 k) S.coordinateRoom :=
    (radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original1
      S.original1_admissible (s k)).2.1.comp S.Xi1_smooth S.Xi1_room
  have hv2 (k : Fin 5) : ContDiffOn ℝ ∞ (v2 k) S.coordinateRoom :=
    (radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original2
      S.original2_admissible (s k)).2.1.comp S.Xi2_smooth S.Xi2_room
  have hMaps : MapsTo scale U S.coordinateRoom := hScaledRoom
  have hHH1 (k : Fin 5) : ContDiffOn ℝ ∞
      (fun t : ℝ × R3 => fderiv ℝ (fderiv ℝ (v1 k)) (scale t)) U :=
    (((hv1 k).fderiv_of_isOpen (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)).fderiv_of_isOpen
      (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)).comp hScale.contDiffOn hMaps
  have hHH2 (k : Fin 5) : ContDiffOn ℝ ∞
      (fun t : ℝ × R3 => fderiv ℝ (fderiv ℝ (v2 k)) (scale t)) U :=
    (((hv2 k).fderiv_of_isOpen (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)).fderiv_of_isOpen
      (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)).comp hScale.contDiffOn hMaps
  have hErrors : ContDiffOn ℝ ∞ errors U := by
    apply contDiffOn_pi.2
    intro k
    apply contDiffOn_pi.2
    intro i
    apply contDiffOn_pi.2
    intro j
    exact (((hHH1 k).clm_apply contDiffOn_const).clm_apply contDiffOn_const).sub
      (((hHH2 k).clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  have hGamma (t : ℝ × R3) :
      gamma t = referenceMetric (dilatedMetric S.g1 t.1) L t.2 := by
    have hExp : -2 * L * referenceCoordinateDepth t.2 =
        2 * (-L * referenceCoordinateDepth t.2) := by ring
    change Real.exp (-2 * L * referenceCoordinateDepth t.2) • S.g1 (t.1 • t.2) =
      Real.exp (2 * (-L * referenceCoordinateDepth t.2)) • S.g1 (t.1 • t.2)
    rw [hExp]
  have hContractionComm (X Y : Mat) : matrixContractionL X Y = matrixContractionL Y X := by
    change (∑ i : Fin 3, ∑ j : Fin 3, X i j * Y i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, Y i j * X i j
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hContract (t : ℝ × R3) (ht : t ∈ U) (k : Fin 5) :
      matrixContractionL (H t k) (E t) = matrixContractionL (b t) (errors t k) := by
    rw [hContractionComm]
    exact (actual_normalized_principal_original_source_hessian_recovery_rows S (s k)
      L t.1 t.2 (hScaledRoom t ht) (hAvoid t ht k).1 (hAvoid t ht k).2).1
  have hTrace (t : ℝ × R3) (ht : t ∈ U) : matrixContractionL (gamma t) (E t) = 0 := by
    rw [hGamma]
    exact (actual_normalized_principal_original_source_hessian_recovery_rows S (s 0)
      L t.1 t.2 (hScaledRoom t ht) (hAvoid t ht 0).1 (hAvoid t ht 0).2).2.1
  have hSym (t : ℝ × R3) (ht : t ∈ U) (i j : Fin 3) : E t i j = E t j i :=
    (actual_normalized_principal_original_source_hessian_recovery_rows S (s 0)
      L t.1 t.2 (hScaledRoom t ht) (hAvoid t ht 0).1 (hAvoid t ht 0).2).2.2 i j
  have hRows (t : ℝ × R3) (ht : t ∈ U) : A t (E t) = B t (errors t) := by
    rw [hARow, hBRows]
    ext i j
    fin_cases i <;> fin_cases j
    · exact hContract t ht 0
    · exact hContract t ht 1
    · exact hContract t ht 2
    · exact hContract t ht 3
    · exact hContract t ht 4
    · exact hTrace t ht
    · exact sub_eq_zero.mpr (hSym t ht 0 1)
    · exact sub_eq_zero.mpr (hSym t ht 0 2)
    · exact sub_eq_zero.mpr (hSym t ht 1 2)
  have hRecovery (t : ℝ × R3) (ht : t ∈ U) : E t = M t (errors t) := by
    change E t = (A t).inverse (B t (errors t))
    rw [← hRows t ht, (hInvert t ht.1).inverse_apply_self]
  exact ⟨eta, U, M, hEta, hEta1, hU, hStrip, hScaledRoom, hAvoid, hM, hErrors, hRecovery⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
