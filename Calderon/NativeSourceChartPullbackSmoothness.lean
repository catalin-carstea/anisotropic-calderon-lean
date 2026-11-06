import Calderon.MetricPullbackFlux
import Calderon.ClmInheritedStructureData
import Calderon.InheritedNormedStructureData
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.NativeSourceChartCalculus
open ConnectionError MetricOperator DirichletFamily.DriftBootstrap

lemma contDiffOn_native_source_chart_pullbackMetric
    (g : MatrixField) (hg : IsAdmissibleMetric g) (X : R3 → R3)
    (S : Set R3) (hS : IsOpen S) (hX : ContDiffOn ℝ ∞ X S) :
    ContDiffOn ℝ ∞ (pullbackMetric g X) S := by
  have hDX : ContDiffOn ℝ ∞ (fderiv ℝ X) S :=
    hX.fderiv_of_isOpen hS (by simp)
  let A : (R3 →L[ℝ] R3) ≃ₗᵢ[ℝ] (R3 →L[ℝ] R3) := ContinuousLinearMap.adjoint
  have hSmooth := ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := R3 →L[ℝ] R3) (F := R3 →L[ℝ] R3) (n := ∞)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hSmooth
  have hAdj : ContDiffOn ℝ ∞ (fun x => (fderiv ℝ X x).adjoint) S := by
    have hComp := (hSmooth A.toContinuousLinearEquiv.toContinuousLinearMap).comp_contDiffOn hDX
    apply hComp.congr
    intro x hx
    rfl
  have hM : ContDiffOn ℝ ∞ (fun x => metricOperatorField g (X x)) S := by
    simpa only [Function.comp_def] using
      (contDiff_metricOperatorField g hg).comp_contDiffOn hX
  have hP : ContDiffOn ℝ ∞ (fun x => (fderiv ℝ X x).adjoint.comp
      ((metricOperatorField g (X x)).comp (fderiv ℝ X x))) S :=
    hAdj.clm_comp (hM.clm_comp hDX)
  change ContDiffOn ℝ ∞ (fun x => operatorMatrixMap
    ((fderiv ℝ X x).adjoint.comp
      ((metricOperatorField g (X x)).comp (fderiv ℝ X x)))) S
  have hMatrixSmooth := ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := R3 →L[ℝ] R3) (F := Matrix (Fin 3) (Fin 3) ℝ) (n := ∞)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hMatrixSmooth
  have hOut := (hMatrixSmooth operatorMatrixMap).comp_contDiffOn hP
  apply hOut.congr
  intro x hx
  rfl

end OAI.AnisotropicCalderon.NativeSourceChartCalculus
