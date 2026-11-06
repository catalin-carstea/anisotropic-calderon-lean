import Calderon.CollaboratorUCPWeightOct17
import Calderon.MetricHessianQuadratic

/-! Exact local native dictionary for the original strict-weight condition.
No global admissibility of the local coordinate metric is assumed. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped ContDiff Topology Matrix.Norms.Operator
namespace OAI.AnisotropicCalderon
open MetricVolume MetricOperator ConnectionError

theorem Mgrad_inverseMetric_eq_four_coordinateHessian
    (g : MatrixField) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian)
    (xi : Fin 3 → ℝ) :
    Mgrad (fun i j y => (g y)⁻¹ i j)
      (bv (fun i j y => (g y)⁻¹ i j) f) x xi =
      4 * RadiusProfile.coordinateHessian f
        (fun X Y => coordinateConnectionField
          (inverseMetricField (metricOperatorField g)) (metricOperatorField g) x X Y)
        x (matrixOperatorMap ((g x)⁻¹) (WithLp.toLp 2 xi))
          (matrixOperatorMap ((g x)⁻¹) (WithLp.toLp 2 xi)) := by
  classical
  let a : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => (g y)⁻¹ i j
  let p : Fin 3 → ℝ := grad f x
  let Dg : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k => pd i (fun y => g y j k) x
  let H : Fin 3 → Fin 3 → ℝ := fun i j => pd i (pd j f) x
  let B : Fin 3 → ℝ := fun j => bv a f j x
  let V : R3 := matrixOperatorMap ((g x)⁻¹) (WithLp.toLp 2 xi)
  let Gamma : R3 →L[ℝ] R3 →L[ℝ] R3 :=
    coordinateConnectionField (inverseMetricField (metricOperatorField g)) (metricOperatorField g) x
  have hV : ∀ i, V i = ∑ j : Fin 3, a i j x * xi j := fun i => rfl
  have hB : ∀ i, B i = ∑ j : Fin 3, a i j x * p j := fun i => rfl
  have hAsym : ∀ i j, a i j x = a j i x := fun i j => inverseMetric_symmetric g x hp i j
  have hDsym : ∀ i j k, Dg i j k = Dg i k j := fun i j k =>
    metricDerivative_symmetric_local g x (coordinateVector i) hs j k
  have haDiff : ∀ i j, DifferentiableAt ℝ (a i j) x := by
    intro i j
    let E : Mat →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    exact (E.hasFDerivAt.comp x (hasFDerivAt_inverseMetric_matrix g x hg hp)).differentiableAt
  have hpDiff : ∀ j, DifferentiableAt ℝ (pd j f) x := fun j =>
    ((contDiff_pd (i := j) hf).differentiable (by simp)) x
  have hDA : ∀ i j k, pd i (a j k) x =
      -∑ r : Fin 3, ∑ s : Fin 3, a j r x * Dg i r s * a s k x := by
    intro i j k
    exact fderiv_inverseMetric_entry_apply g x (coordinateVector i) hg hp j k
  have hDb : ∀ i j, pd i (bv a f j) x =
      ∑ k : Fin 3, (pd i (a j k) x * p k + a j k x * H i k) := by
    intro i j
    change fderiv ℝ (fun y => ∑ k : Fin 3, a j k y * pd k f y) x
      (coordinateVector i) = _
    have hsum : fderiv ℝ (fun y => ∑ k : Fin 3, a j k y * pd k f y) x =
        ∑ k : Fin 3, fderiv ℝ (fun y => a j k y * pd k f y) x := by
      exact fderiv_fun_sum (A := fun k y => a j k y * pd k f y)
        (fun k _ => (haDiff j k).mul (hpDiff k))
    rw [hsum]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [fderiv_fun_mul (haDiff j k) (hpDiff k)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    dsimp only [p, H, grad, pd, coordinateVector]
    ring
  have hSecond : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have hHsecond : ∀ i j, H i j =
      fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j) := by
    intro i j
    change (fderiv ℝ (fun y => (fderiv ℝ f y) (coordinateVector j)) x)
        (coordinateVector i) = _
    rw [fderiv_clm_apply hSecond (differentiableAt_const _)]
    simp
  have hEntry : ∀ i j, RadiusProfile.coordinateHessian f (fun X Y => Gamma X Y)
      x (coordinateVector i) (coordinateVector j) =
      H i j - ∑ k : Fin 3, metricChristoffel g x i j k * p k := by
    intro i j
    unfold RadiusProfile.coordinateHessian
    rw [← hHsecond i j, covector_coordinate_sum (fderiv ℝ f x)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    unfold metricChristoffel
    simp only [Gamma, coordinateConnectionField_apply,
      inverseMetricField_eq_matrix_inverse_of_posDef g x hp]
  have hHessian : RadiusProfile.coordinateHessian f (fun X Y => Gamma X Y) x V V =
      ∑ i : Fin 3, ∑ j : Fin 3, V i * V j *
        (H i j - ∑ k : Fin 3, metricChristoffel g x i j k * p k) := by
    simpa only [coordinateHessianBilinear_apply, hEntry] using
      bilinear_coordinate_sum (coordinateHessianBilinear f Gamma x) V V
  have hM : Mgrad a (bv a f) x xi =
      4 * (∑ i : Fin 3, V i * (∑ j : Fin 3, pd i (bv a f j) x * xi j)) -
        2 * (∑ j : Fin 3, B j * (∑ i : Fin 3, ∑ k : Fin 3,
          pd j (a i k) x * xi i * xi k)) := by
    simp only [Mgrad, hV, B, Fin.sum_univ_three]
    ring
  have hFirst : ∀ i, (∑ j : Fin 3, pd i (bv a f j) x * xi j) =
      (∑ k : Fin 3, H i k * V k) -
        ∑ r : Fin 3, ∑ s : Fin 3, V r * Dg i r s * B s := by
    intro i
    simp only [hDb, hDA, hV, hB, Fin.sum_univ_three,
      hAsym 1 0, hAsym 2 0, hAsym 2 1]
    ring
  have hSecondTerm : ∀ j, (∑ i : Fin 3, ∑ k : Fin 3, pd j (a i k) x * xi i * xi k) =
      -(∑ r : Fin 3, ∑ s : Fin 3, V r * Dg j r s * V s) := by
    intro j
    simp only [hDA, hV, Fin.sum_univ_three, hAsym 1 0, hAsym 2 0, hAsym 2 1]
    ring
  have hChrist : ∀ i j k, metricChristoffel g x i j k = (1/2 : ℝ) *
      ∑ c : Fin 3, a k c x * (Dg i c j + Dg j c i - Dg c j i) := by
    intro i j k
    exact metricChristoffel_eq g x hg i j k
  have hGamma : (∑ i : Fin 3, ∑ j : Fin 3, V i * V j *
      (∑ k : Fin 3, metricChristoffel g x i j k * p k)) =
      (∑ i : Fin 3, ∑ r : Fin 3, ∑ s : Fin 3, V i * V r * Dg i r s * B s) -
        (1/2 : ℝ) * (∑ j : Fin 3, ∑ r : Fin 3, ∑ s : Fin 3,
          B j * V r * Dg j r s * V s) := by
    simp only [hChrist, hB, Fin.sum_univ_three,
      hAsym 1 0, hAsym 2 0, hAsym 2 1,
      hDsym 0 1 0, hDsym 0 2 0, hDsym 0 2 1,
      hDsym 1 1 0, hDsym 1 2 0, hDsym 1 2 1,
      hDsym 2 1 0, hDsym 2 2 0, hDsym 2 2 1]
    ring
  change Mgrad a (bv a f) x xi =
    4 * RadiusProfile.coordinateHessian f (fun X Y => Gamma X Y) x V V
  rw [hM, hHessian]
  have hSplit : (∑ i : Fin 3, ∑ j : Fin 3, V i * V j *
      (H i j - ∑ k : Fin 3, metricChristoffel g x i j k * p k)) =
      (∑ i : Fin 3, ∑ j : Fin 3, V i * V j * H i j) -
        (∑ i : Fin 3, ∑ j : Fin 3, V i * V j *
          (∑ k : Fin 3, metricChristoffel g x i j k * p k)) := by
    simp only [Fin.sum_univ_three]
    ring
  rw [hSplit, hGamma]
  simp only [hFirst, hSecondTerm]
  simp only [Fin.sum_univ_three]
  ring

end OAI.AnisotropicCalderon

#print axioms OAI.AnisotropicCalderon.Mgrad_inverseMetric_eq_four_coordinateHessian
