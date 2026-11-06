import Calderon.ActualSourceSpatialMetricJetRecovery
import Calderon.ActualNormalizedPairHessianFiniteJets

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_original_source_spatial_metric_jet_recovery_with_finite_jets
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
  obtain ⟨s, hs⟩ := exists_original_source_spatial_metric_jet_recovery S hFirst hSecond hMatch
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
