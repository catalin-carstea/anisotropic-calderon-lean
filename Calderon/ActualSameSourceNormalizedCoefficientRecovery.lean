import Calderon.ActualOriginalSourceResponseCoordinatePDE
import Calderon.ActualSourceChartNondivergenceEquation
import Calderon.ActualNormalizedSecondMetricDrift
import Calderon.NormalizedPrincipalMetricSmooth
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix BigOperators
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ActualNormalizedSecondMetricDrift

/-- Consumed helper: a zero flux divergence in an admissible carrier whose coordinate
functions are harmonic at `x` gives the raw nondivergence Hessian equation at `x`. -/
theorem hessian_trace_eq_zero_of_harmonic_coordinates
    (g : MatrixField) (hg : IsAdmissibleMetric g) (v : R3 → ℝ) (x : R3)
    (hD2 : DifferentiableAt ℝ (fderiv ℝ v) x)
    (hColumns : ∀ j : Fin 3,
      coordinateFluxDivergence (metricDivergenceFlux g (fun z => z j)) x = 0)
    (hDiv : coordinateFluxDivergence (metricDivergenceFlux g v) x = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3, ((g x)⁻¹) i j *
      fderiv ℝ (fderiv ℝ v) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 := by
  have hbD (i j : Fin 3) : DifferentiableAt ℝ (fun y => g y i j) x :=
    (hg.smooth i j).differentiable (by simp) x
  have hbPos : (g x).PosDef := hg.posDef x
  have hFlux (i : Fin 3) :
      (fun y => metricDivergenceFlux g v y i) =
      (fun y => vol g y * (matrixOperatorMap ((g y)⁻¹) (gradient v y)) i) := by
    funext y
    simp only [metricDivergenceFlux,principalCoefficient,map_smul,
      ContinuousLinearMap.smul_apply,PiLp.smul_apply,smul_eq_mul]
  have hExpand : coordinateFluxDivergence (metricDivergenceFlux g v) x =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y => principalCoefficient g y i j) x (EuclideanSpace.single i 1) *
          fderiv ℝ v x (EuclideanSpace.single j 1) +
        principalCoefficient g x i j *
          fderiv ℝ (fderiv ℝ v) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
    unfold coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i _
    rw [hFlux i]
    exact derivative_density_gradient_entry g v x hbD hbPos hD2 i
  have hFirst : (∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun y => principalCoefficient g y i j) x (EuclideanSpace.single i 1) *
        fderiv ℝ v x (EuclideanSpace.single j 1)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.sum_mul]
    have hC : (∑ i : Fin 3, fderiv ℝ (fun y => principalCoefficient g y i j) x
        (EuclideanSpace.single i 1)) = 0 :=
      (coordinateFluxDivergence_metricDivergenceFlux_coordinate g j x).symm.trans (hColumns j)
    rw [hC,zero_mul]
  have hSecond : (∑ i : Fin 3, ∑ j : Fin 3, principalCoefficient g x i j *
      fderiv ℝ (fderiv ℝ v) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 := by
    simp only [Finset.sum_add_distrib] at hExpand
    rw [hDiv,hFirst,zero_add] at hExpand
    exact hExpand.symm
  have hProduct : vol g x * (∑ i : Fin 3, ∑ j : Fin 3, ((g x)⁻¹) i j *
      fderiv ℝ (fderiv ℝ v) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 := by
    simpa only [principalCoefficient,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
      using hSecond
  have hVol : 0 < vol g x := Real.sqrt_pos.mpr hbPos.det_pos
  exact (mul_eq_zero.mp hProduct).resolve_left hVol.ne'

/-- Consumed helper: for a symmetric `A`, the entrywise pairing with `N` is `trace (N * A)`. -/
theorem matrix_entry_contraction_eq_trace_mul_of_symm
    (A N : Matrix (Fin 3) (Fin 3) ℝ) (hA : ∀ i j : Fin 3, A i j = A j i) :
    (∑ i : Fin 3, ∑ j : Fin 3, A i j * N i j) = Matrix.trace (N * A) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA i j]
  ring

theorem original_first_source_coordinate_nondivergence_eq_zero
    (S : KnownSideSourceData) (s : 𝓓(fixedExteriorSourceOpens, ℝ))
    (x : R3) (hx : x ∈ S.coordinateRoom) (hSource : S.Xi1 x ∉ tsupport s) :
    (∑ i : Fin 3, ∑ j : Fin 3, ((S.g1 x)⁻¹) i j *
      fderiv ℝ (fderiv ℝ
        ((radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s) ∘ S.Xi1)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 := by
  let u : R3 → ℝ :=
    radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
  have hv : ContDiffOn ℝ (∞ : ℕ∞ω) (u ∘ S.Xi1) S.coordinateRoom :=
    (radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original1
      S.original1_admissible s).2.1.comp S.Xi1_smooth S.Xi1_room
  have hvD : ContDiffOn ℝ (∞ : ℕ∞ω) (fderiv ℝ (u ∘ S.Xi1)) S.coordinateRoom :=
    hv.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ (u ∘ S.Xi1)) x :=
    (hvD.contDiffAt (S.coordinateRoom_open.mem_nhds hx)).differentiableAt (by simp)
  have hDiv : coordinateFluxDivergence (metricDivergenceFlux S.g1 (u ∘ S.Xi1)) x = 0 :=
    coordinateFluxDivergence_originalSourceResponse_pullback_eq_zero
      S.hreg S.hcalc S.original1 S.g1 S.original1_admissible
      S.coordinateRoom S.coordinateRoom_open S.Xi1 S.Xi1_smooth S.Xi1_room S.Xi1_jacobian
      S.carrier1 s x hx hSource
  exact hessian_trace_eq_zero_of_harmonic_coordinates S.g1 S.g1_admissible
    (u ∘ S.Xi1) x hD2 (fun j => S.harmonic_coordinates1 j x hx) hDiv

theorem original_second_source_coordinate_nondivergence_eq_zero
    (S : KnownSideSourceData) (s : 𝓓(fixedExteriorSourceOpens, ℝ))
    (x : R3) (hx : x ∈ S.coordinateRoom) (hSource : S.Xi2 x ∉ tsupport s) :
    (∑ i : Fin 3, ∑ j : Fin 3, ((S.g2 x)⁻¹) i j *
      fderiv ℝ (fderiv ℝ
        ((radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s) ∘ S.Xi2)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 := by
  let u : R3 → ℝ :=
    radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
  have hv : ContDiffOn ℝ (∞ : ℕ∞ω) (u ∘ S.Xi2) S.coordinateRoom :=
    (radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original2
      S.original2_admissible s).2.1.comp S.Xi2_smooth S.Xi2_room
  have hvD : ContDiffOn ℝ (∞ : ℕ∞ω) (fderiv ℝ (u ∘ S.Xi2)) S.coordinateRoom :=
    hv.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) S.coordinateRoom_open (by simp)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ (u ∘ S.Xi2)) x :=
    (hvD.contDiffAt (S.coordinateRoom_open.mem_nhds hx)).differentiableAt (by simp)
  have hDiv : coordinateFluxDivergence (metricDivergenceFlux S.g2 (u ∘ S.Xi2)) x = 0 :=
    coordinateFluxDivergence_originalSourceResponse_pullback_eq_zero
      S.hreg S.hcalc S.original2 S.g2 S.original2_admissible
      S.coordinateRoom S.coordinateRoom_open S.Xi2 S.Xi2_smooth S.Xi2_room S.Xi2_jacobian
      S.carrier2 s x hx hSource
  exact hessian_trace_eq_zero_of_harmonic_coordinates S.g2 S.g2_admissible
    (u ∘ S.Xi2) x hD2 (fun j => S.harmonic_coordinates2 j x hx) hDiv

theorem actual_normalized_principal_original_source_hessian_recovery_rows
    (S : KnownSideSourceData) (s : 𝓓(fixedExteriorSourceOpens, ℝ))
    (L lam : ℝ) (y : R3) (hy : lam • y ∈ S.coordinateRoom)
    (hSource1 : S.Xi1 (lam • y) ∉ tsupport s) (hSource2 : S.Xi2 (lam • y) ∉ tsupport s) :
    let v1 : R3 → ℝ :=
      (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s) ∘ S.Xi1
    let v2 : R3 → ℝ :=
      (radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s) ∘ S.Xi2
    (∑ i : Fin 3, ∑ j : Fin 3,
      referenceNormalizedPrincipalDifference S.g1 S.g2 L lam y i j *
        fderiv ℝ (fderiv ℝ v1) (lam • y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
    (∑ i : Fin 3, ∑ j : Fin 3,
      referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam y i j *
        (fderiv ℝ (fderiv ℝ v1) (lam • y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
         fderiv ℝ (fderiv ℝ v2) (lam • y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) ∧
    (∑ i : Fin 3, ∑ j : Fin 3,
      referenceMetric (dilatedMetric S.g1 lam) L y i j *
        referenceNormalizedPrincipalDifference S.g1 S.g2 L lam y i j) = 0 ∧
    (∀ i j : Fin 3,
      referenceNormalizedPrincipalDifference S.g1 S.g2 L lam y i j =
      referenceNormalizedPrincipalDifference S.g1 S.g2 L lam y j i) := by
  intro v1 v2
  -- Actual admissible metrics at the source point `lam • y`.
  have hM1pos : (S.g1 (lam • y)).PosDef := S.g1_admissible.posDef (lam • y)
  have hM2pos : (S.g2 (lam • y)).PosDef := S.g2_admissible.posDef (lam • y)
  have hM1unit : IsUnit (S.g1 (lam • y)).det := isUnit_iff_ne_zero.mpr hM1pos.det_pos.ne'
  have hM1sym (i j : Fin 3) : S.g1 (lam • y) i j = S.g1 (lam • y) j i := by
    simpa using (hM1pos.isHermitian.apply j i)
  have hM1invSym (i j : Fin 3) : (S.g1 (lam • y))⁻¹ i j = (S.g1 (lam • y))⁻¹ j i := by
    simpa using (hM1pos.isHermitian.inv.apply j i)
  have hM2invSym (i j : Fin 3) : (S.g2 (lam • y))⁻¹ i j = (S.g2 (lam • y))⁻¹ j i := by
    simpa using (hM2pos.isHermitian.inv.apply j i)
  -- The first conformal reference metric is a positive multiple of `S.g1 (lam • y)`.
  obtain ⟨a, hA⟩ : ∃ a : ℝ,
      referenceMetric (dilatedMetric S.g1 lam) L y = Real.exp a • S.g1 (lam • y) := by
    first
    | exact ⟨_, rfl⟩
    | exact ⟨2*(-L*referenceCoordinateDepth y), rfl⟩
  have he : Real.exp a ≠ 0 := Real.exp_ne_zero a
  have hLeft : ((Real.exp a)⁻¹ • (S.g1 (lam • y))⁻¹) *
      referenceMetric (dilatedMetric S.g1 lam) L y = 1 := by
    rw [hA, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hM1unit,
      inv_mul_cancel₀ he, one_smul]
  have hAinv : (referenceMetric (dilatedMetric S.g1 lam) L y)⁻¹ =
      (Real.exp a)⁻¹ • (S.g1 (lam • y))⁻¹ :=
    Matrix.inv_eq_left_inv hLeft
  have hAA : (referenceMetric (dilatedMetric S.g1 lam) L y)⁻¹ *
      referenceMetric (dilatedMetric S.g1 lam) L y = 1 := by
    rw [hAinv]
    exact hLeft
  have hAinvEntry (i j : Fin 3) : (referenceMetric (dilatedMetric S.g1 lam) L y)⁻¹ i j =
      (Real.exp a)⁻¹ * (S.g1 (lam • y))⁻¹ i j := by
    rw [hAinv, Matrix.smul_apply, smul_eq_mul]
  have hAsym (i j : Fin 3) : referenceMetric (dilatedMetric S.g1 lam) L y i j =
      referenceMetric (dilatedMetric S.g1 lam) L y j i := by
    rw [hA, Matrix.smul_apply, Matrix.smul_apply, hM1sym i j]
  -- The actual normalization scalar `3 / trace (A * B⁻¹)` is positive, so the trace is nonzero.
  have hc : 0 < 3 / Matrix.trace (referenceMetric (dilatedMetric S.g1 lam) L y *
      (dilatedMetric S.g2 lam y)⁻¹) :=
    normalizedSecondLaplacianScalarJoint_pos S.g1 S.g2 S.g1_admissible S.g2_admissible L (lam, y)
  have hTne : Matrix.trace (referenceMetric (dilatedMetric S.g1 lam) L y *
      (dilatedMetric S.g2 lam y)⁻¹) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hc
    exact lt_irrefl 0 hc
  have hcT : 3 / Matrix.trace (referenceMetric (dilatedMetric S.g1 lam) L y *
      (dilatedMetric S.g2 lam y)⁻¹) * Matrix.trace (referenceMetric (dilatedMetric S.g1 lam) L y *
      (dilatedMetric S.g2 lam y)⁻¹) = 3 := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hTne, mul_one]
  -- The genuine normalized definitions.
  have hDiffEq : referenceNormalizedPrincipalDifference S.g1 S.g2 L lam y =
      (3 / Matrix.trace (referenceMetric (dilatedMetric S.g1 lam) L y *
        (dilatedMetric S.g2 lam y)⁻¹)) • (dilatedMetric S.g2 lam y)⁻¹ -
      (referenceMetric (dilatedMetric S.g1 lam) L y)⁻¹ := rfl
  have hDiffEntry (i j : Fin 3) : referenceNormalizedPrincipalDifference S.g1 S.g2 L lam y i j =
      3 / Matrix.trace (referenceMetric (dilatedMetric S.g1 lam) L y *
        (dilatedMetric S.g2 lam y)⁻¹) * (S.g2 (lam • y))⁻¹ i j -
      (referenceMetric (dilatedMetric S.g1 lam) L y)⁻¹ i j := rfl
  have hbEntry (i j : Fin 3) : referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam y i j =
      3 / Matrix.trace (referenceMetric (dilatedMetric S.g1 lam) L y *
        (dilatedMetric S.g2 lam y)⁻¹) * (S.g2 (lam • y))⁻¹ i j := rfl
  -- Raw original-source nondivergence equations at `lam • y`.
  have h1 : (∑ i : Fin 3, ∑ j : Fin 3, (S.g1 (lam • y))⁻¹ i j *
      fderiv ℝ (fderiv ℝ v1) (lam • y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 :=
    original_first_source_coordinate_nondivergence_eq_zero S s (lam • y) hy hSource1
  have h2 : (∑ i : Fin 3, ∑ j : Fin 3, (S.g2 (lam • y))⁻¹ i j *
      fderiv ℝ (fderiv ℝ v2) (lam • y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 :=
    original_second_source_coordinate_nondivergence_eq_zero S s (lam • y) hy hSource2
  refine ⟨?_, ?_, ?_⟩
  · -- E : H1 = b : (H1 - H2)
    rw [← sub_eq_zero]
    have hSplit :
        (∑ i : Fin 3, ∑ j : Fin 3,
          referenceNormalizedPrincipalDifference S.g1 S.g2 L lam y i j *
            fderiv ℝ (fderiv ℝ v1) (lam • y) (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1)) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam y i j *
            (fderiv ℝ (fderiv ℝ v1) (lam • y) (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1) -
             fderiv ℝ (fderiv ℝ v2) (lam • y) (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1))) =
        3 / Matrix.trace (referenceMetric (dilatedMetric S.g1 lam) L y *
            (dilatedMetric S.g2 lam y)⁻¹) *
          (∑ i : Fin 3, ∑ j : Fin 3, (S.g2 (lam • y))⁻¹ i j *
            fderiv ℝ (fderiv ℝ v2) (lam • y) (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1)) -
        (Real.exp a)⁻¹ *
          (∑ i : Fin 3, ∑ j : Fin 3, (S.g1 (lam • y))⁻¹ i j *
            fderiv ℝ (fderiv ℝ v1) (lam • y) (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1)) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hDiffEntry i j, hbEntry i j, hAinvEntry i j]
      ring
    rw [hSplit, h1, h2]
    ring
  · -- Reference-metric trace row: A : E = (3 / T) * T - 3 = 0.
    rw [matrix_entry_contraction_eq_trace_mul_of_symm (referenceMetric (dilatedMetric S.g1 lam) L y)
        (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam y) hAsym,
      hDiffEq, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, hAA,
      Matrix.trace_one, Matrix.trace_mul_comm (dilatedMetric S.g2 lam y)⁻¹, smul_eq_mul, hcT,
      Fintype.card_fin]
    norm_num
  · -- Symmetry row.
    intro i j
    rw [hDiffEntry i j, hDiffEntry j i, hAinvEntry i j, hAinvEntry j i,
      hM2invSym i j, hM1invSym i j]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
