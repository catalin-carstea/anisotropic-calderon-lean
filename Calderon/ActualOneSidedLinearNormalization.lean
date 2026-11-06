import Calderon.ActualLocalPositiveMetricCarrier
import Calderon.MetricFrameOperator
import Mathlib.Analysis.Calculus.LocalExtr.Basic
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge MetricOperator ConnectionError NormalCoordinatesFrame

theorem metricGramFrame_operator_third_coordinate
    (M : R3 →L[ℝ] R3) (v : R3) :
    frameOperator (metricGramFrame M) v 2 =
      (Real.sqrt (metricPair M (gramThird M) (gramThird M)))⁻¹ * v 2 := by
  rw [frameOperator_apply]
  simp [Fin.sum_univ_three,metricGramFrame,metricNormalize,coordinateVector,
    PiLp.single_apply,gramSecond_two,gramThird_two,mul_comm]

theorem exists_metric_normalizing_linear_equiv_preserving_third_coordinate
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ (A : R3 ≃L[ℝ] R3) (c : ℝ), 0 < c ∧
      pullbackMetric g A 0 = 1 ∧ ∀ v : R3, (A v) 2 = c * v 2 := by
  let M := metricOperatorField g 0
  let e := metricGramFrame M
  have hFrame : IsMetricOrthonormalFrame M e :=
    metricGramFrame_isMetricOrthonormalFrame M (metricOperatorField_symmetric g hg 0)
      (metricOperatorField_pos g hg 0)
  let F := frameOperator e
  have hBij : Function.Bijective F.toLinearMap := frameOperator_bijective M e hFrame
  let A : R3 ≃L[ℝ] R3 := (LinearEquiv.ofBijective F.toLinearMap hBij).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = F := by ext v; rfl
  let c := (Real.sqrt (metricPair M (gramThird M) (gramThird M)))⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr
    (metricOperatorField_pos g hg 0 _ (gramThird_ne_zero M)))
  refine ⟨A,c,hc,?_,?_⟩
  · change operatorMatrixMap ((fderiv ℝ A 0).adjoint.comp
      ((metricOperatorField g (A 0)).comp (fderiv ℝ A 0))) = 1
    have hDA : HasFDerivAt (A : R3 → R3) A.toContinuousLinearMap (0 : R3) := by
      change HasFDerivAt A.toContinuousLinearMap A.toContinuousLinearMap (0 : R3)
      exact A.toContinuousLinearMap.hasFDerivAt
    rw [hDA.fderiv,map_zero,hA]
    change operatorMatrixMap ((frameOperator e).adjoint.comp (M.comp (frameOperator e))) = 1
    rw [frameOperator_pullback_metric M e hFrame]
    exact matrixOperatorAlgEquiv.symm.map_one
  · intro v
    change (A.toContinuousLinearMap v) 2 = c * v 2
    rw [hA]
    exact metricGramFrame_operator_third_coordinate M v

theorem one_sided_separator_preserved_by_positive_triangular_linear_equiv
    (sep : R3 → ℝ) (U W : Set R3) (hU : IsOpen U) (h0 : (0 : R3) ∈ U)
    (hSmooth : ContDiffOn ℝ ∞ sep U) (hZero : sep 0 = 0)
    (hNormal : ∀ v : R3, fderiv ℝ sep 0 v = v 2)
    (hSide : ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ U ∧
      {z ∈ ball (0 : R3) r | sep z < 0} ⊆ W)
    (A : R3 ≃L[ℝ] R3) (c : ℝ) (hc : 0 < c)
    (hThird : ∀ v : R3, (A v) 2 = c * v 2) :
    ContDiffOn ℝ ∞ (fun x => c⁻¹ * sep (A x)) (A ⁻¹' U) ∧
    (fun x => c⁻¹ * sep (A x)) (0 : R3) = 0 ∧
    (∀ v : R3, fderiv ℝ (fun x => c⁻¹ * sep (A x)) 0 v = v 2) ∧
    ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ A ⁻¹' U ∧
      {z ∈ ball (0 : R3) r | c⁻¹ * sep (A z) < 0} ⊆ A ⁻¹' W := by
  have hComp : ContDiffOn ℝ ∞ (fun x => sep (A x)) (A ⁻¹' U) :=
    hSmooth.comp A.toContinuousLinearMap.contDiff.contDiffOn (fun _ hx => hx)
  refine ⟨contDiffOn_const.mul hComp,?_,?_,?_⟩
  · simp only [map_zero,hZero,mul_zero]
  · intro v
    have hDsep := (hSmooth.contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp)
    have hDA : HasFDerivAt (A : R3 → R3) A.toContinuousLinearMap (0 : R3) := by
      change HasFDerivAt A.toContinuousLinearMap A.toContinuousLinearMap (0 : R3)
      exact A.toContinuousLinearMap.hasFDerivAt
    have hSepAtA : HasFDerivAt sep (fderiv ℝ sep 0) (A (0 : R3)) := by
      simpa only [map_zero] using hDsep.hasFDerivAt
    have hComposed : HasFDerivAt (fun x : R3 => sep (A x))
        ((fderiv ℝ sep 0).comp A.toContinuousLinearMap) (0 : R3) :=
      hSepAtA.comp 0 hDA
    have hD : HasFDerivAt (fun x => c⁻¹ * sep (A x))
        (c⁻¹ • (fderiv ℝ sep 0).comp A.toContinuousLinearMap) (0 : R3) := by
      simpa only [map_zero] using
        hComposed.const_mul c⁻¹
    rw [hD.fderiv]
    change c⁻¹ * fderiv ℝ sep 0 (A v) = v 2
    rw [hNormal,hThird,← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]
  · obtain ⟨a,ha,hBall,hNeg⟩ := hSide
    have hOpen : IsOpen (A ⁻¹' ball (0 : R3) a) := isOpen_ball.preimage A.continuous
    have h0Ball : (0 : R3) ∈ A ⁻¹' ball (0 : R3) a := by
      simpa only [mem_preimage,map_zero] using mem_ball_self ha
    obtain ⟨b,hb,hSmall⟩ := Metric.isOpen_iff.mp hOpen 0 h0Ball
    refine ⟨b,hb,(fun _ hx => hBall (hSmall hx)),?_⟩
    intro z hz
    apply hNeg
    refine ⟨hSmall hz.1,?_⟩
    by_contra hNonneg
    have hProduct : 0 ≤ c⁻¹ * sep (A z) := mul_nonneg (inv_nonneg.mpr hc.le) (le_of_not_gt hNonneg)
    exact (not_lt_of_ge hProduct) hz.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
