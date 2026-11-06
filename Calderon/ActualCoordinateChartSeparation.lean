import Calderon.MetricPullbackFlux
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Operator.Banach
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise NNReal
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator

theorem exists_coordinate_chart_local_separation
    (X : R3 → R3) (hX : ContDiffAt ℝ ∞ X 0)
    (hJ : IsUnit (coordinateJacobianMatrix X 0).det) :
    ∃ (r c : ℝ), 0 < r ∧ 0 < c ∧ ∀ x ∈ ball (0 : R3) r,
      ∀ y ∈ ball (0 : R3) r, c * dist x y ≤ dist (X x) (X y) := by
  have hU : IsUnit (fderiv ℝ X 0) := by
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap] at hJ
    have hu := (Matrix.isUnit_iff_isUnit_det _).mpr hJ
    have hm := hu.map matrixOperatorAlgEquiv.toMonoidHom
    change IsUnit (matrixOperatorAlgEquiv (matrixOperatorAlgEquiv.symm (fderiv ℝ X 0))) at hm
    simpa only [AlgEquiv.apply_symm_apply] using hm
  let E : R3 ≃L[ℝ] R3 := (LinearEquiv.ofBijective
    (fderiv ℝ X 0).toLinearMap (ContinuousLinearMap.isUnit_iff_bijective.mp hU)).toContinuousLinearEquiv
  have hE : (E : R3 →L[ℝ] R3) = fderiv ℝ X 0 := by rfl
  have hs : HasStrictFDerivAt X (E : R3 →L[ℝ] R3) 0 := by
    rw [hE]
    exact hX.hasStrictFDerivAt (by simp)
  obtain ⟨s,hs0,hsOpen,hApprox⟩ := hs.approximates_deriv_on_open_nhds
  have hNorm : 0 < ‖(E.symm : R3 →L[ℝ] R3)‖₊ := by
    rcases E.subsingleton_or_nnnorm_symm_pos with hSub | hPos
    · exact False.elim (not_subsingleton R3 hSub)
    · exact hPos
  have hHalf : ‖(E.symm : R3 →L[ℝ] R3)‖₊⁻¹ / 2 < ‖(E.symm : R3 →L[ℝ] R3)‖₊⁻¹ :=
    NNReal.half_lt_self (inv_ne_zero hNorm.ne')
  have hAnti := hApprox.antilipschitzWith (Or.inr hHalf)
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (hsOpen.mem_nhds hs0)
  let c : ℝ≥0 := ‖(E.symm : R3 →L[ℝ] R3)‖₊⁻¹ - ‖(E.symm : R3 →L[ℝ] R3)‖₊⁻¹ / 2
  have hc : 0 < c := tsub_pos_iff_lt.mpr hHalf
  refine ⟨r,(c:ℝ),hr,by exact_mod_cast hc,?_⟩
  intro x hx y hy
  have h := hAnti.mul_le_dist (⟨x,hBall hx⟩ : s) (⟨y,hBall hy⟩ : s)
  simpa only [inv_inv,Subtype.dist_eq,Set.domRestrict_apply,c] using h

end OAI.AnisotropicCalderon.ConnectionError
