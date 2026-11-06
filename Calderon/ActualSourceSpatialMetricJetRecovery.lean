import Calderon.ActualUniformSourceErrorRecovery
import Calderon.ActualNormalizedPairHessianFiniteJets
import Calderon.OperatorApplicationFiniteJets
import Calderon.SpatialSourceJetRecoveryBounds
import Calderon.HessianDifferenceGerm
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ExteriorSource.MetricCompatibleSourceJetAlgebra

/-- Smooth joint functions restrict to smooth spatial slices with the supplied norm. -/
theorem contDiffOn_real_prod_slice_snd
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (ℝ × R3) → V) (U : Set (ℝ × R3))
    (hf : ContDiffOn ℝ ∞ f U) (lam : ℝ) :
    ContDiffOn ℝ ∞ (fun x : R3 => f (lam, x))
      ((fun x : R3 => (lam, x)) ⁻¹' U) := by
  exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => hx)

theorem exists_original_source_spatial_metric_jet_recovery
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
  obtain ⟨s, hs⟩ := exists_uniform_original_source_hessian_error_recovery S hFirst hSecond hMatch
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
