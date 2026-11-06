import Calderon.ActualSourceChartHarmonicColumns

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Gradient Distributions Matrix BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature MetricVolume MetricOperator ConnectionError

theorem exists_radiusTwoSourceEuclideanCoordinates_allSource_nondivergence
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3))
    (hdet : (Matrix.of (fun i j =>
      d (radiusTwoSmoothSourceResponse hreg hcalc g hg (f i)) p j)).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph R3 R3,
      (e : R3 → R3) = radiusTwoSourceEuclideanCoordinates hreg hcalc g hg f ∧
      p ∈ e.source ∧ radiusTwoSourceEuclideanCoordinates hreg hcalc g hg f p ∈ e.target ∧
      e.source ⊆ (radiusTwoOpens : Set R3) ∧
      ContDiffOn ℝ (∞ : ℕ∞ω)
        (radiusTwoSourceEuclideanCoordinates hreg hcalc g hg f) e.source ∧
      ContDiffOn ℝ (∞ : ℕ∞ω) e.symm e.target ∧
      (∀ z ∈ e.target, IsUnit (coordinateJacobianMatrix e.symm z).det) ∧
      (∀ i j : Fin 3, ContDiffOn ℝ (∞ : ℕ∞ω)
        (fun z => pullbackMetric g e.symm z i j) e.target) ∧
      (∀ z ∈ e.target, (pullbackMetric g e.symm z).PosDef) ∧
      (∀ z ∈ e.target, e.symm z ∉ (fixedExteriorSourceOpens : Set R3) →
        ∀ j : Fin 3, (∑ i : Fin 3,
          fderiv ℝ (fun y => principalCoefficient (pullbackMetric g e.symm) y i j) z
            (EuclideanSpace.single i 1)) = 0) ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ z ∈ e.target,
        e.symm z ∉ (fixedExteriorSourceOpens : Set R3) →
        (∑ i : Fin 3, ∑ j : Fin 3, ((pullbackMetric g e.symm z)⁻¹) i j *
          fderiv ℝ (fderiv ℝ ((radiusTwoSmoothSourceResponse hreg hcalc g hg s) ∘ e.symm)) z
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 := by
  classical
  obtain ⟨e,he,hpSource,hpTarget,hSource,hForward,hInverse,hJac,hBSmooth,hBPos,hColumns⟩ :=
    exists_radiusTwoSourceEuclideanCoordinates_harmonicChart_of_det_ne_zero
      hreg hcalc g hg f p hp hdet
  refine ⟨e,he,hpSource,hpTarget,hSource,hForward,hInverse,hJac,hBSmooth,hBPos,hColumns,?_⟩
  intro s z hz hOutside
  let u : R3 → ℝ := radiusTwoSmoothSourceResponse hreg hcalc g hg s
  let b : MatrixField := pullbackMetric g e.symm
  let v : R3 → ℝ := u ∘ e.symm
  have hXz : e.symm z ∈ (radiusTwoOpens : Set R3) := hSource (e.map_target hz)
  have hu : ContDiffOn ℝ (∞ : ℕ∞ω) u (radiusTwoOpens : Set R3) :=
    (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg s).2.1
  have hv : ContDiffOn ℝ (∞ : ℕ∞ω) v e.target :=
    hu.comp hInverse (fun y hy => hSource (e.map_target hy))
  have hvD : ContDiffOn ℝ (∞ : ℕ∞ω) (fderiv ℝ v) e.target :=
    hv.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) e.open_target (by simp)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hvD.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hbD (i j : Fin 3) : DifferentiableAt ℝ (fun y => b y i j) z :=
    ((hBSmooth i j).contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hbPos : (b z).PosDef := hBPos z hz
  have hNative : nativeMetricDifferential g u (e.symm z) = 0 := by
    change nativeMetricDifferential g
      (radiusTwoSmoothSourceResponse hreg hcalc g hg s) (e.symm z) = 0
    rw [nativeMetricDifferential_radiusTwoSmoothSourceResponse hreg hcalc g hg s (e.symm z) hXz]
    exact image_eq_zero_of_notMem_tsupport (fun h => hOutside (s.tsupport_subset h))
  have hPhysical : coordinateFluxDivergence (metricDivergenceFlux g u) (e.symm z) = 0 := by
    rw [nativeMetricDifferential_eq_neg_coordinateFluxDivergence] at hNative
    exact neg_eq_zero.mp hNative
  have hDiv : coordinateFluxDivergence (metricDivergenceFlux b v) z = 0 := by
    have hCov := coordinateFluxDivergence_pullbackMetric_of_contDiffOn
      g hg.smooth hg.posDef e.symm u e.target (radiusTwoOpens : Set R3)
      e.open_target radiusTwoOpens.isOpen hInverse hu z hz hXz (hJac z hz)
    rw [hPhysical,mul_zero] at hCov
    exact hCov
  have hFlux (i : Fin 3) :
      (fun y => metricDivergenceFlux b v y i) =
      (fun y => vol b y * (matrixOperatorMap ((b y)⁻¹) (gradient v y)) i) := by
    funext y
    simp only [metricDivergenceFlux,principalCoefficient,map_smul,
      ContinuousLinearMap.smul_apply,PiLp.smul_apply,smul_eq_mul]
  have hExpand : coordinateFluxDivergence (metricDivergenceFlux b v) z =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y => principalCoefficient b y i j) z (EuclideanSpace.single i 1) *
          fderiv ℝ v z (EuclideanSpace.single j 1) +
        principalCoefficient b z i j *
          fderiv ℝ (fderiv ℝ v) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
    unfold coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i _
    rw [hFlux i]
    exact derivative_density_gradient_entry b v z hbD hbPos hD2 i
  have hFirst : (∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (fun y => principalCoefficient b y i j) z (EuclideanSpace.single i 1) *
        fderiv ℝ v z (EuclideanSpace.single j 1)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.sum_mul]
    have hC := hColumns z hz hOutside j
    change (∑ i : Fin 3, fderiv ℝ (fun y => principalCoefficient b y i j) z
      (EuclideanSpace.single i 1)) = 0 at hC
    rw [hC,zero_mul]
  have hSecond : (∑ i : Fin 3, ∑ j : Fin 3, principalCoefficient b z i j *
      fderiv ℝ (fderiv ℝ v) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 := by
    simp only [Finset.sum_add_distrib] at hExpand
    rw [hDiv,hFirst,zero_add] at hExpand
    exact hExpand.symm
  have hProduct : vol b z * (∑ i : Fin 3, ∑ j : Fin 3, ((b z)⁻¹) i j *
      fderiv ℝ (fderiv ℝ v) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = 0 := by
    simpa only [principalCoefficient,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc] using hSecond
  have hVol : 0 < vol b z := Real.sqrt_pos.mpr hbPos.det_pos
  exact (mul_eq_zero.mp hProduct).resolve_left hVol.ne'

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSourceEuclideanCoordinates_allSource_nondivergence
