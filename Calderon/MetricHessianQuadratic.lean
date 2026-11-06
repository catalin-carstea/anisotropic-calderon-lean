import Calderon.MetricHessianComparison
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open scoped Matrix.Norms.Operator InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.MetricVolume
open Matrix

def coordinateHessianBilinear (f : R3 → ℝ) (Γ : R3 →L[ℝ] R3 →L[ℝ] R3)
    (x : R3) : R3 →L[ℝ] R3 →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x -
    ((ContinuousLinearMap.compL ℝ R3 R3 ℝ) (fderiv ℝ f x)).comp Γ

lemma coordinateHessianBilinear_apply (f : R3 → ℝ)
    (Γ : R3 →L[ℝ] R3 →L[ℝ] R3) (x X Y : R3) :
    coordinateHessianBilinear f Γ x X Y =
      RadiusProfile.coordinateHessian f (fun V W => Γ V W) x X Y := by
  simp [coordinateHessianBilinear, RadiusProfile.coordinateHessian]

lemma bilinear_coordinate_sum (B : R3 →L[ℝ] R3 →L[ℝ] ℝ) (X Y : R3) :
    B X Y = ∑ i : Fin 3, ∑ j : Fin 3,
      X i * Y j * B (coordinateVector i) (coordinateVector j) := by
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr X,
    ← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr Y]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, smul_eq_mul,
    coordinateVector, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bilinear_matrix_quadratic (B : R3 →L[ℝ] R3 →L[ℝ] ℝ) (X : R3) :
    (X : Fin 3 → ℝ) ⬝ᵥ (Matrix.mulVec (fun i j => B (coordinateVector i) (coordinateVector j))
      (X : Fin 3 → ℝ)) = B X X := by
  rw [bilinear_coordinate_sum B X X]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma actualMetricConnection_symmetric_local (g : MatrixField) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian) (X Y : R3) :
    ConnectionError.coordinateConnectionField
      (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
      (MetricOperator.metricOperatorField g) x X Y =
    ConnectionError.coordinateConnectionField
      (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
      (MetricOperator.metricOperatorField g) x Y X := by
  have hm : ∀ᶠ y in 𝓝 x, ∀ V W : R3,
      ⟪MetricOperator.metricOperatorField g y V, W⟫_ℝ =
        ⟪MetricOperator.metricOperatorField g y W, V⟫_ℝ := by
    filter_upwards [hs] with y hy
    intro V W
    have h := Matrix.isSymmetric_toEuclideanLin_iff.mpr hy
    change ⟪(g y).toEuclideanLin V, W⟫_ℝ = ⟪(g y).toEuclideanLin W, V⟫_ℝ
    exact (h V W).trans (real_inner_comm _ _)
  simp only [ConnectionError.coordinateConnectionField_apply]
  apply ConnectionError.coordinateConnection_symmetric
  intro U V W
  exact ConnectionError.inverse_metric_derivative_symmetric _ _ x
    (hasFDerivAt_actualMetricOperator g x hg).differentiableAt.hasFDerivAt hm U V W

lemma metricHessianMatrix_isHermitian (g : MatrixField) (f : R3 → ℝ) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian) (hf : ContDiffAt ℝ 2 f x) :
    (metricHessianMatrix g f x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, metricHessianMatrix,
    RadiusProfile.coordinateHessian]
  rw [(hf.isSymmSndFDerivAt (by simp)).eq (coordinateVector j) (coordinateVector i),
    actualMetricConnection_symmetric_local g x hg hs (coordinateVector j) (coordinateVector i)]

lemma metricHessianMatrix_quadratic (g : MatrixField) (f : R3 → ℝ) (x X : R3) :
    (X : Fin 3 → ℝ) ⬝ᵥ (Matrix.mulVec (metricHessianMatrix g f x) (X : Fin 3 → ℝ)) =
      RadiusProfile.coordinateHessian f
        (fun V W => ConnectionError.coordinateConnectionField
          (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
          (MetricOperator.metricOperatorField g) x V W) x X X := by
  let Γ := ConnectionError.coordinateConnectionField
    (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
    (MetricOperator.metricOperatorField g) x
  have he : (fun i j => coordinateHessianBilinear f Γ x
      (coordinateVector i) (coordinateVector j)) = metricHessianMatrix g f x := by
    ext i j
    exact coordinateHessianBilinear_apply f Γ x (coordinateVector i) (coordinateVector j)
  have h := bilinear_matrix_quadratic (coordinateHessianBilinear f Γ x) X
  rw [he, coordinateHessianBilinear_apply] at h
  exact h

lemma negative_metricHessian_posSemidef_of_quadratic (g : MatrixField) (f : R3 → ℝ)
    (x : R3) (a : ℝ)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian)
    (hf : ContDiffAt ℝ 2 f x)
    (hquad : ∀ X : R3, RadiusProfile.coordinateHessian f
      (fun V W => ConnectionError.coordinateConnectionField
        (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
        (MetricOperator.metricOperatorField g) x V W) x X X ≤
      -a * ⟪MetricOperator.metricOperatorField g x X, X⟫_ℝ) :
    (-metricHessianMatrix g f x - a • g x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((metricHessianMatrix_isHermitian g f x hg hs hf).neg.sub
      (hp.isHermitian.smul (show IsSelfAdjoint a from rfl)))
  intro v
  let X : R3 := WithLp.toLp 2 v
  have h := hquad X
  rw [← metricHessianMatrix_quadratic g f x X] at h
  have he : ⟪MetricOperator.metricOperatorField g x X, X⟫_ℝ =
      v ⬝ᵥ (Matrix.mulVec (g x) v) := by
    change ⟪(g x).toEuclideanLin X, X⟫_ℝ = _
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    rfl
  rw [he] at h
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_neg, dotProduct_smul, smul_eq_mul]
  change 0 ≤ -(v ⬝ᵥ (Matrix.mulVec (metricHessianMatrix g f x) v)) - a * (v ⬝ᵥ (Matrix.mulVec (g x) v))
  change v ⬝ᵥ (Matrix.mulVec (metricHessianMatrix g f x) v) ≤ -a * (v ⬝ᵥ (Matrix.mulVec (g x) v)) at h
  linarith

lemma densityWeightedDivergence_le_of_quadratic_metricHessian_local
    (g : MatrixField) (f : R3 → ℝ) (x : R3) (a : ℝ)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian)
    (hf : ContDiffAt ℝ 2 f x)
    (hquad : ∀ X : R3, RadiusProfile.coordinateHessian f
      (fun V W => ConnectionError.coordinateConnectionField
        (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
        (MetricOperator.metricOperatorField g) x V W) x X X ≤
      -a * ⟪MetricOperator.metricOperatorField g x X, X⟫_ℝ) :
    AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (vol g) (fun y => MetricOperator.matrixOperatorMap ((g y)⁻¹) (gradient f y)) x ≤
      -3 * vol g x * a := by
  apply densityWeightedDivergence_le_of_negative_metricHessian_local g f x a hg hp hs
  · exact (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  · exact negative_metricHessian_posSemidef_of_quadratic g f x a hg hp hs hf hquad

end OAI.AnisotropicCalderon.MetricVolume
