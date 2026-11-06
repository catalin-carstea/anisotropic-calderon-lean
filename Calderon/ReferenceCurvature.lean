import Calderon.ProfileMetricTensorJets
import Calderon.CoordinateCurvature

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open RadiusProfile MetricOperator CoordinateCurvature

lemma referenceConnection_spatial_fderiv_eq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (z : ℝ × R3) :
    fderiv ℝ (fun y => referenceConnectionFamily g L (z.1,y)) z.2 =
      (fderiv ℝ (referenceConnectionFamily g L) z).comp (ContinuousLinearMap.inr ℝ ℝ R3) := by
  have hp : HasFDerivAt (fun y : R3 => (z.1,y))
      (ContinuousLinearMap.inr ℝ ℝ R3) z.2 := hasFDerivAt_prodMk_right z.1 z.2
  exact (((contDiff_referenceConnectionFamily g hg L).differentiable (by simp) z).hasFDerivAt.comp z.2 hp).fderiv

lemma contDiff_referenceConnection_spatial_fderiv (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 => fderiv ℝ (fun y => referenceConnectionFamily g L (z.1,y)) z.2) := by
  have he : (fun z : ℝ × R3 => fderiv ℝ (fun y => referenceConnectionFamily g L (z.1,y)) z.2) =
      fun z => (fderiv ℝ (referenceConnectionFamily g L) z).comp (ContinuousLinearMap.inr ℝ ℝ R3) :=
    funext (referenceConnection_spatial_fderiv_eq g hg L)
  rw [he]
  exact ((contDiff_referenceConnectionFamily g hg L).fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

theorem exists_referenceConnection_uniform_bounds (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ‖referenceConnectionFamily g L (lam,x)‖ ≤ C ∧
      ‖fderiv ℝ (fun y => referenceConnectionFamily g L (lam,y)) x‖ ≤ D := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (contDiff_referenceConnectionFamily g hg L).continuous.continuousOn
  obtain ⟨D,hD⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (contDiff_referenceConnection_spatial_fderiv g hg L).continuous.continuousOn
  refine ⟨max C 0+1,max D 0+1,by positivity,by positivity,?_⟩
  intro lam hlam x hx
  constructor
  · exact (hC (lam,x) ⟨hlam,hx⟩).trans (by linarith [le_max_left C 0])
  · exact (hD (lam,x) ⟨hlam,hx⟩).trans (by linarith [le_max_left D 0])

def referenceJacobiCurvature (g : MatrixField) (L lam : ℝ) (x v : R3) : R3 →L[ℝ] R3 :=
  curvatureOperator (fun y => referenceConnectionFamily g L (lam,y)) x v

theorem referenceJacobiCurvature_apply (g : MatrixField) (L lam : ℝ) (x v X : R3) :
    referenceJacobiCurvature g L lam x v X =
      (fderiv ℝ (fun y => referenceConnectionFamily g L (lam,y)) x X) v v -
      (fderiv ℝ (fun y => referenceConnectionFamily g L (lam,y)) x v) X v +
      referenceConnectionFamily g L (lam,x) X (referenceConnectionFamily g L (lam,x) v v) -
      referenceConnectionFamily g L (lam,x) v (referenceConnectionFamily g L (lam,x) X v) := by
  exact curvatureOperator_apply _ x v X

theorem exists_referenceJacobiCurvature_uniform_norm_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ v : R3,
      ‖referenceJacobiCurvature g L lam x v‖ ≤ C * ‖v‖^2 := by
  obtain ⟨C,D,hC,hD,hbounds⟩ := exists_referenceConnection_uniform_bounds g hg L K hK
  refine ⟨2*(D+C^2),by positivity,?_⟩
  intro lam hlam x hx v
  exact norm_curvatureOperator_le_of_bounds _ x v C D ‖v‖ hC.le hD.le (norm_nonneg _)
    (hbounds lam hlam x hx).1 (hbounds lam hlam x hx).2 le_rfl

theorem exists_referenceJacobiCurvature_uniform_metric_unit_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ v : R3,
      ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x v,v⟫_ℝ ≤ 1 →
      ‖referenceJacobiCurvature g L lam x v‖ ≤ C := by
  obtain ⟨B,hB,hbounds⟩ := exists_referenceJacobiCurvature_uniform_norm_bound g hg L K hK
  obtain ⟨c,hc,hmetric⟩ := exists_referenceMetric_uniform_quadratic_lower_bound_on_compact g hg L hL K hK
  let D := Real.sqrt (1/c)
  refine ⟨B*D^2+1,by positivity,?_⟩
  intro lam hlam x hx v hv
  have hnorm : ‖v‖ ≤ D := norm_le_sqrt_inv_of_quadratic_unit _ c hc (hmetric lam x hx) v hv
  have hs : ‖v‖^2 ≤ D^2 := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm
  exact (hbounds lam hlam x hx v).trans ((mul_le_mul_of_nonneg_left hs hB.le).trans (by linarith))

end OAI.AnisotropicCalderon.ConformalDepth
