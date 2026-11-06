import Calderon.SourceResponseEuclideanChart
import Calderon.RadiusTwoSmoothSourceClassicalEquation
import Calderon.LocalMetricPullbackDivergence
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Gradient Distributions Matrix BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature MetricVolume MetricOperator ConnectionError

lemma nativeMetricDifferential_eq_neg_coordinateFluxDivergence
    (g : MatrixField) (u : R3 → ℝ) (x : R3) :
    nativeMetricDifferential g u x =
      -coordinateFluxDivergence (metricDivergenceFlux g u) x := by
  have hFlux (i : Fin 3) :
      (fun y => ∑ j : Fin 3, principalCoefficient g y i j *
        fderiv ℝ u y (EuclideanSpace.single j 1)) =
      (fun y => metricDivergenceFlux g u y i) := by
    funext y
    simp only [metricDivergenceFlux,matrixOperator_coordinate,gradient_coordinate,
      MetricVolume.coordinateVector]
  unfold nativeMetricDifferential coordinateFluxDivergence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (fderiv ℝ (fun z => ∑ j : Fin 3, principalCoefficient g z i j *
      fderiv ℝ u z (EuclideanSpace.single j 1)) x) (EuclideanSpace.single i 1) =
    (fderiv ℝ (fun y => metricDivergenceFlux g u y i) x) (EuclideanSpace.single i 1)
  exact congrArg (fun F : R3 → ℝ => fderiv ℝ F x (EuclideanSpace.single i 1)) (hFlux i)

lemma coordinateFluxDivergence_metricDivergenceFlux_coordinate
    (g : MatrixField) (j : Fin 3) (x : R3) :
    coordinateFluxDivergence (metricDivergenceFlux g (fun y => y j)) x =
      ∑ i : Fin 3, fderiv ℝ (fun y => principalCoefficient g y i j) x
        (EuclideanSpace.single i 1) := by
  classical
  have hD (y : R3) : HasFDerivAt (fun z : R3 => z j)
      (EuclideanSpace.proj (𝕜 := ℝ) j : R3 →L[ℝ] ℝ) y := by
    change HasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) j : R3 → ℝ)
      (EuclideanSpace.proj (𝕜 := ℝ) j : R3 →L[ℝ] ℝ) y
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt
  have hEntry (i : Fin 3) :
      (fun y => metricDivergenceFlux g (fun z => z j) y i) =
      (fun y => principalCoefficient g y i j) := by
    funext y
    simp only [metricDivergenceFlux,matrixOperator_coordinate,gradient_coordinate,(hD y).fderiv]
    change (∑ k : Fin 3, principalCoefficient g y i k *
      (EuclideanSpace.single k 1) j) = principalCoefficient g y i j
    simp [PiLp.single_apply]
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  rw [hEntry i]
  rfl

theorem exists_radiusTwoSourceEuclideanCoordinates_harmonicChart_of_det_ne_zero
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
      ∀ z ∈ e.target, e.symm z ∉ (fixedExteriorSourceOpens : Set R3) →
        ∀ j : Fin 3, (∑ i : Fin 3,
          fderiv ℝ (fun y => principalCoefficient (pullbackMetric g e.symm) y i j) z
            (EuclideanSpace.single i 1)) = 0 := by
  classical
  obtain ⟨e,he,hpSource,hpTarget,hSource,hForward,hInverse⟩ :=
    exists_radiusTwoSourceEuclideanCoordinates_localChart_of_det_ne_zero
      hreg hcalc g hg f p hp hdet
  have hESmooth : ContDiffOn ℝ (∞ : ℕ∞ω) (e : R3 → R3) e.source := by
    rw [he]
    exact hForward
  let J : R3 → Matrix (Fin 3) (Fin 3) ℝ := coordinateJacobianMatrix e.symm
  have hJac (z : R3) (hz : z ∈ e.target) : IsUnit (J z).det := by
    have hDE := (hESmooth.contDiffAt (e.open_source.mem_nhds (e.map_target hz))).differentiableAt (by simp)
    have hDX := (hInverse.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp)
    have hNear : (e : R3 → R3) ∘ e.symm =ᶠ[𝓝 z] (fun y : R3 => y) := by
      filter_upwards [e.open_target.mem_nhds hz] with y hy
      exact e.right_inv hy
    have hId : fderiv ℝ (fun y : R3 => y) z = ContinuousLinearMap.id ℝ R3 :=
      (ContinuousLinearMap.id ℝ R3).hasFDerivAt.fderiv
    have hProd : (fderiv ℝ e (e.symm z)).comp (fderiv ℝ e.symm z) =
        ContinuousLinearMap.id ℝ R3 :=
      ((hDE.hasFDerivAt.comp z hDX.hasFDerivAt).fderiv).symm.trans
        (hNear.fderiv_eq.trans hId)
    have hMat := congrArg operatorMatrixMap hProd
    have hOpId : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) =
        (1 : Matrix (Fin 3) (Fin 3) ℝ) := matrixOperatorAlgEquiv.symm.map_one
    rw [operatorMatrixMap_comp,hOpId] at hMat
    have hDet : (operatorMatrixMap (fderiv ℝ e (e.symm z))).det *
        (operatorMatrixMap (fderiv ℝ e.symm z)).det = 1 := by
      simpa only [Matrix.det_mul,Matrix.det_one] using congrArg Matrix.det hMat
    apply isUnit_iff_ne_zero.mpr
    change (coordinateJacobianMatrix e.symm z).det ≠ 0
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap e.symm z]
    intro hZero
    rw [hZero,mul_zero] at hDet
    exact zero_ne_one hDet
  have hBFormula : pullbackMetric g e.symm =
      (fun z => (J z)ᵀ * g (e.symm z) * J z) := by
    funext z
    simp only [pullbackMetric,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,J,coordinateJacobianMatrix_eq_operatorMatrixMap,
      Matrix.mul_assoc]
  have hDXSmooth : ContDiffOn ℝ (∞ : ℕ∞ω) (fderiv ℝ e.symm) e.target :=
    hInverse.fderiv_of_isOpen e.open_target (by simp)
  have hJSmooth (i j : Fin 3) : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun z => J z i j) e.target := by
    change ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun z => (EuclideanSpace.proj i)
        ((fderiv ℝ e.symm z) (EuclideanSpace.single j 1))) e.target
    exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn
      (hDXSmooth.clm_apply contDiffOn_const)
  have hBSmooth (i j : Fin 3) : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun z => pullbackMetric g e.symm z i j) e.target := by
    rw [hBFormula]
    change ContDiffOn ℝ (∞ : ℕ∞ω) (fun z =>
      ∑ l : Fin 3, (∑ k : Fin 3, J z k i * g (e.symm z) k l) * J z l j) e.target
    apply ContDiffOn.sum
    intro l _
    exact (ContDiffOn.sum (fun k _ =>
      (hJSmooth k i).mul ((hg.smooth k l).comp_contDiffOn hInverse))).mul (hJSmooth l j)
  have hBPos (z : R3) (hz : z ∈ e.target) : (pullbackMetric g e.symm z).PosDef := by
    rw [hBFormula]
    have hInject : Function.Injective (J z).mulVec :=
      Matrix.mulVec_injective_of_det_ne_zero (M := J z) (hJac z hz).ne_zero
    have hConj := (hg.posDef (e.symm z)).conjTranspose_mul_mul_same (B := J z) hInject
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hConj
  refine ⟨e,he,hpSource,hpTarget,hSource,hForward,hInverse,hJac,hBSmooth,hBPos,?_⟩
  intro z hz hOutside j
  let u : R3 → ℝ := radiusTwoSmoothSourceResponse hreg hcalc g hg (f j)
  have hXz : e.symm z ∈ (radiusTwoOpens : Set R3) := hSource (e.map_target hz)
  have hu : ContDiffOn ℝ (∞ : ℕ∞ω) u (radiusTwoOpens : Set R3) :=
    (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg (f j)).2.1
  have hNative : nativeMetricDifferential g u (e.symm z) = 0 := by
    change nativeMetricDifferential g
      (radiusTwoSmoothSourceResponse hreg hcalc g hg (f j)) (e.symm z) = 0
    rw [nativeMetricDifferential_radiusTwoSmoothSourceResponse hreg hcalc g hg (f j) (e.symm z) hXz]
    exact image_eq_zero_of_notMem_tsupport (fun h => hOutside ((f j).tsupport_subset h))
  have hDiv : coordinateFluxDivergence (metricDivergenceFlux g u) (e.symm z) = 0 := by
    rw [nativeMetricDifferential_eq_neg_coordinateFluxDivergence] at hNative
    exact neg_eq_zero.mp hNative
  have hCov := coordinateFluxDivergence_pullbackMetric_of_contDiffOn
    g hg.smooth hg.posDef e.symm u e.target (radiusTwoOpens : Set R3)
    e.open_target radiusTwoOpens.isOpen hInverse hu z hz hXz (hJac z hz)
  rw [hDiv,mul_zero] at hCov
  have hCoord : u ∘ e.symm =ᶠ[𝓝 z] (fun y : R3 => y j) := by
    filter_upwards [e.open_target.mem_nhds hz] with y hy
    have hValue := congrArg (fun v : R3 => v j) (e.right_inv hy)
    rw [he] at hValue
    change u (e.symm y) = y j at hValue ⊢
    exact hValue
  have hCong := coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
    (pullbackMetric g e.symm) (u ∘ e.symm) (fun y : R3 => y j) z hCoord
  have hProj : coordinateFluxDivergence
      (metricDivergenceFlux (pullbackMetric g e.symm) (fun y : R3 => y j)) z = 0 :=
    hCong.symm.trans hCov
  rw [← coordinateFluxDivergence_metricDivergenceFlux_coordinate (pullbackMetric g e.symm) j z]
  exact hProj

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.nativeMetricDifferential_eq_neg_coordinateFluxDivergence
#print axioms OAI.AnisotropicCalderon.ExteriorSource.coordinateFluxDivergence_metricDivergenceFlux_coordinate
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSourceEuclideanCoordinates_harmonicChart_of_det_ne_zero
