import Calderon.ActualSourceFreeKnownSideHessians
import Calderon.ActualNormalizedPairHessianFiniteJets
import Calderon.ActualNormalizedHessianCoefficientInverse
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Distributions Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature MetricVolume ConnectionError ConformalDepth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_same_source_normalized_analytic_family_of_source_free_room
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
          ‖iteratedFDeriv ℝ n (fun t => (A t).inverse) t‖ ≤ C) ) := by
  obtain ⟨s,hs⟩ := exists_same_source_normalized_known_side_five_hessians_of_source_free_room S hFree hMatch
  let v1 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible (s k)) ∘ S.Xi1
  let v2 : Fin 5 → R3 → ℝ := fun k =>
    (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible (s k)) ∘ S.Xi2
  let B : Fin 5 → R3 →L[ℝ] R3 →L[ℝ] ℝ := fun k =>
    matrixJetBilinear (traceFreeHessianMatrix (1 : Mat) k)
  have hJets1 (k : Fin 5) : v1 k 0 = 0 ∧ fderiv ℝ (v1 k) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (v1 k)) 0 = B k :=
    ⟨(hs k).1,(hs k).2.1,(hs k).2.2.1⟩
  have hJets2 (k : Fin 5) : v2 k 0 = 0 ∧ fderiv ℝ (v2 k) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (v2 k)) 0 = B k :=
    ⟨(hs k).2.2.2.1,(hs k).2.2.2.2.1,(hs k).2.2.2.2.2⟩
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp
    (S.coordinateRoom_open.mem_nhds S.origin_mem)
  have hv1 (k : Fin 5) : ContDiffOn ℝ ∞ (v1 k) (ball (0 : R3) r) :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original1
      S.original1_admissible (s k)).2.1.comp S.Xi1_smooth S.Xi1_room).mono hBall
  have hv2 (k : Fin 5) : ContDiffOn ℝ ∞ (v2 k) (ball (0 : R3) r) :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original2
      S.original2_admissible (s k)).2.1.comp S.Xi2_smooth S.Xi2_room).mono hBall
  refine ⟨s,hs,r,hr,hBall,?_,?_⟩
  · intro K hK N
    exact exists_normalized_pair_hessian_compact_finite_jet_bound v1 v2 B r hr
      hv1 hv2 hJets1 hJets2 K hK N
  · intro L K hK N
    have hCanonical (k : Fin 5) : fderiv ℝ (fderiv ℝ (v1 k)) 0 =
        matrixJetBilinear (traceFreeHessianMatrix ((S.g1 0)⁻¹) k) := by
      rw [S.g1_origin,inv_one]
      exact (hJets1 k).2.2
    exact exists_normalized_hessianCoefficient_uniform_inverse S.g1 S.g1_admissible
      v1 r hr hv1 hCanonical L K hK N

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
