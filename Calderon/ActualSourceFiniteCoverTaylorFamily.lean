import Calderon.ActualSourceSpatialMetricJetRecoveryWithFiniteJets
import Calderon.FiniteCoverSourceTaylorBounds
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_original_source_spatial_metric_jets_with_finite_cover_taylor
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
  obtain ⟨s,hs⟩ := exists_original_source_spatial_metric_jet_recovery_with_finite_jets
    S hFirst hSecond hMatch
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
