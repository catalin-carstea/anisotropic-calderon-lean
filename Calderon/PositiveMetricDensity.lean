import Calderon.AngularMetricDensity
import Calderon.PositiveConformalMetric

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.AngularPolynomial

lemma contDiff_inverseMetricOperator_of_smooth_posDef (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef) :
    ContDiff ℝ ∞ (inverseMetricOperator g) := by
  have h : ContDiff ℝ ∞ g :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => hs i j))
  exact ConnectionError.contDiff_inverseMetricField _
    (MetricOperator.matrixOperatorMap.contDiff.comp h)
    (fun x => (hp x).isUnit.map MetricOperator.matrixOperatorAlgEquiv.toMonoidHom)

lemma inverseMetricOperator_eq_matrix_inverse_of_posDef (g : MatrixField)
    (hp : ∀ x, (g x).PosDef) (x : R3) :
    inverseMetricOperator g x = MetricOperator.matrixOperatorMap ((g x)⁻¹) := by
  obtain ⟨u, hu⟩ := (hp x).isUnit
  change Ring.inverse (MetricOperator.matrixOperatorAlgEquiv (g x)) =
    MetricOperator.matrixOperatorAlgEquiv ((g x)⁻¹)
  rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  change Ring.inverse ((Units.map MetricOperator.matrixOperatorAlgEquiv.toMonoidHom u).val) =
    ((Units.map MetricOperator.matrixOperatorAlgEquiv.toMonoidHom u)⁻¹).val
  rw [Ring.inverse_unit]

lemma inverseMetricOperator_symmetric_of_posDef (g : MatrixField)
    (hp : ∀ x, (g x).PosDef) (x V W : R3) :
    ⟪inverseMetricOperator g x V, W⟫_ℝ = ⟪inverseMetricOperator g x W, V⟫_ℝ := by
  rw [inverseMetricOperator_eq_matrix_inverse_of_posDef g hp]
  change ⟪(g x)⁻¹.toEuclideanLin V, W⟫_ℝ = ⟪(g x)⁻¹.toEuclideanLin W, V⟫_ℝ
  have h := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hp x).inv.isHermitian
  exact (h V W).trans (real_inner_comm _ _)

lemma coefficientQuadratic_inverseMetricOperator_of_posDef (g : MatrixField)
    (hp : ∀ x, (g x).PosDef) (x V : R3) :
    coefficientQuadratic (inverseMetricOperator g) x V =
      TauCeti.PDE.matrixBilinearForm ((g x)⁻¹) V V := by
  unfold coefficientQuadratic
  rw [inverseMetricOperator_eq_matrix_inverse_of_posDef g hp]
  change ⟪(g x)⁻¹.toEuclideanLin V, V⟫_ℝ = _
  rw [TauCeti.PDE.matrixBilinearForm_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rfl

lemma vol_coefficientQuadratic_inverseMetricOperator_nonneg_of_posDef (g : MatrixField)
    (hp : ∀ x, (g x).PosDef) (x V : R3) :
    0 ≤ vol g x * coefficientQuadratic (inverseMetricOperator g) x V := by
  apply mul_nonneg (EnergyBridge.vol_pos_of_posDef g hp x).le
  rw [coefficientQuadratic_inverseMetricOperator_of_posDef g hp,
    TauCeti.PDE.matrixBilinearForm_apply]
  exact (hp x).inv.posSemidef.dotProduct_mulVec_nonneg (V : Fin 3 → ℝ)

theorem compact_posDef_metric_density_gradient_square_expansion {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (k : ℝ) (u f : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport u) :
    (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x
      (gradient u x + (k * u x) • gradient f x)) =
      (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x (gradient u x)) +
        k ^ 2 * (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x
          (gradient f x) * u x ^ 2) -
        k * (∫ x : R3, densityWeightedDivergence b (vol g)
          (fun y => inverseMetricOperator g y (gradient f y)) x * u x ^ 2) :=
  compact_coefficient_density_gradient_square_expansion b _
    (contDiff_inverseMetricOperator_of_smooth_posDef g hs hp)
    (inverseMetricOperator_symmetric_of_posDef g hp) k u (vol g) (gradient f) hu
    (EnergyBridge.contDiff_vol_of_smooth_posDef g hs hp)
    (hf.gradient_right (m := ∞) (by simp)) hc

theorem compact_posDef_metric_density_gradient_profile_lower_bound {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (k c : ℝ) (hk : 0 ≤ k) (u f beta : R3 → ℝ)
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (hb : Continuous beta)
    (hc : HasCompactSupport u)
    (hdiv : ∀ x, u x ≠ 0 → densityWeightedDivergence b (vol g)
      (fun y => inverseMetricOperator g y (gradient f y)) x ≤ -c * (vol g x * beta x)) :
    (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x (gradient u x)) +
      k ^ 2 * (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x
        (gradient f x) * u x ^ 2) + k * c * (∫ x : R3, (vol g x * beta x) * u x ^ 2) ≤
    (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x
      (gradient u x + (k * u x) • gradient f x)) :=
  compact_coefficient_density_gradient_profile_lower_bound b _
    (contDiff_inverseMetricOperator_of_smooth_posDef g hs hp)
    (inverseMetricOperator_symmetric_of_posDef g hp) k c hk u (vol g) beta (gradient f) hu
    (EnergyBridge.contDiff_vol_of_smooth_posDef g hs hp) hb
    (hf.gradient_right (m := ∞) (by simp)) hc hdiv

lemma inverseMetricOperator_conformalMatrix (g : MatrixField) (a : R3 → ℝ)
    (hp : ∀ x, (g x).PosDef) (x : R3) :
    inverseMetricOperator (EnergyBridge.conformalMatrix g a) x =
      Real.exp (-2 * a x) • inverseMetricOperator g x := by
  rw [inverseMetricOperator_eq_matrix_inverse_of_posDef _
      (EnergyBridge.conformalMatrix_posDef g a hp), EnergyBridge.conformalMatrix_inverse g a hp,
    map_smul, inverseMetricOperator_eq_matrix_inverse_of_posDef g hp]

lemma vol_coefficientQuadratic_conformalMatrix (g : MatrixField) (a : R3 → ℝ)
    (hp : ∀ x, (g x).PosDef) (x V : R3) :
    vol (EnergyBridge.conformalMatrix g a) x *
        coefficientQuadratic (inverseMetricOperator (EnergyBridge.conformalMatrix g a)) x V =
      Real.exp (a x) * (vol g x * coefficientQuadratic (inverseMetricOperator g) x V) := by
  rw [EnergyBridge.vol_conformalMatrix]
  unfold coefficientQuadratic
  rw [inverseMetricOperator_conformalMatrix g a hp]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left,
    starRingEnd_apply, star_trivial]
  have h : Real.exp (3 * a x) * Real.exp (-2 * a x) = Real.exp (a x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (3 * a x) * Real.exp (-2 * a x)) *
      (vol g x * ⟪inverseMetricOperator g x V, V⟫_ℝ) := by ring
    _ = _ := by rw [h]

lemma densityWeightedDivergence_product_rule {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (rho : R3 → ℝ) (A : R3 → R3) (x : R3)
    (hr : DifferentiableAt ℝ rho x) (hA : DifferentiableAt ℝ A x) :
    densityWeightedDivergence b rho A x = ⟪gradient rho x, A x⟫_ℝ +
      rho x * ∑ i, ⟪fderiv ℝ A x (b i), b i⟫_ℝ := by
  have hd (i : ι) : fderiv ℝ (fun y => rho y * ⟪A y, b i⟫_ℝ) x (b i) =
      fderiv ℝ rho x (b i) * ⟪A x, b i⟫_ℝ +
        rho x * ⟪fderiv ℝ A x (b i), b i⟫_ℝ := by
    rw [fderiv_fun_mul hr (hA.inner ℝ (differentiableAt_const (b i)))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_inner_apply ℝ hA (differentiableAt_const (b i))]
    simp only [fderiv_const_apply, zero_apply, inner_zero_right, zero_add]
    ring
  simp only [densityWeightedDivergence, hd, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ i, ⟪gradient rho x, b i⟫_ℝ * ⟪b i, A x⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_gradient_left, real_inner_comm (A x) (b i)]
    _ = _ := b.sum_inner_mul_inner _ _

lemma densityWeightedDivergence_coefficient_product_rule {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (rho : R3 → ℝ) (C : R3 → R3 →L[ℝ] R3)
    (A : R3 → R3) (x : R3) (hr : DifferentiableAt ℝ rho x)
    (hC : DifferentiableAt ℝ C x) (hA : DifferentiableAt ℝ A x) :
    densityWeightedDivergence b rho (fun y => C y (A y)) x =
      ⟪gradient rho x, C x (A x)⟫_ℝ + rho x *
        ∑ i, ⟪fderiv ℝ C x (b i) (A x) + C x (fderiv ℝ A x (b i)), b i⟫_ℝ := by
  rw [densityWeightedDivergence_product_rule b rho _ x hr (hC.clm_apply hA),
    fderiv_clm_apply hC hA]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_comm]

lemma densityWeightedDivergence_mul_density {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (s rho : R3 → ℝ) (A : R3 → R3) (x : R3)
    (hs : DifferentiableAt ℝ s x) (hr : DifferentiableAt ℝ rho x)
    (hA : DifferentiableAt ℝ A x) :
    densityWeightedDivergence b (fun y => s y * rho y) A x =
      s x * densityWeightedDivergence b rho A x + rho x * ⟪gradient s x, A x⟫_ℝ := by
  have hd (i : ι) : (fun y => (s y * rho y) * ⟪A y, b i⟫_ℝ) =
      fun y => s y * (rho y * ⟪A y, b i⟫_ℝ) := by funext y; ring
  have he (i : ι) :
      fderiv ℝ (fun y => s y * (rho y * ⟪A y, b i⟫_ℝ)) x (b i) =
        s x * fderiv ℝ (fun y => rho y * ⟪A y, b i⟫_ℝ) x (b i) +
          (rho x * ⟪A x, b i⟫_ℝ) * fderiv ℝ s x (b i) := by
    have hprofile : DifferentiableAt ℝ (fun y => rho y * ⟪A y, b i⟫_ℝ) x :=
      hr.mul (hA.inner ℝ (differentiableAt_const (b i)))
    rw [fderiv_fun_mul hs hprofile]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  unfold densityWeightedDivergence
  simp only [hd, he, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  calc
    _ = rho x * ∑ i, ⟪gradient s x, b i⟫_ℝ * ⟪b i, A x⟫_ℝ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_gradient_left, real_inner_comm (A x) (b i)]
      ring
    _ = _ := by rw [b.sum_inner_mul_inner]

lemma densityWeightedDivergence_conformalMatrix {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (a f : R3 → ℝ) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (x : R3) :
    densityWeightedDivergence b (vol (EnergyBridge.conformalMatrix g a))
        (fun y => inverseMetricOperator (EnergyBridge.conformalMatrix g a) y (gradient f y)) x =
      Real.exp (a x) * (densityWeightedDivergence b (vol g)
        (fun y => inverseMetricOperator g y (gradient f y)) x +
          vol g x * ⟪gradient a x, inverseMetricOperator g x (gradient f x)⟫_ℝ) := by
  have hflux (i : ι) :
      (fun y => vol (EnergyBridge.conformalMatrix g a) y *
        ⟪inverseMetricOperator (EnergyBridge.conformalMatrix g a) y (gradient f y), b i⟫_ℝ) =
      fun y => (Real.exp (a y) * vol g y) *
        ⟪inverseMetricOperator g y (gradient f y), b i⟫_ℝ := by
    funext y
    rw [EnergyBridge.vol_conformalMatrix, inverseMetricOperator_conformalMatrix g a hp]
    simp only [ContinuousLinearMap.smul_apply, inner_smul_left, starRingEnd_apply, star_trivial]
    have he : Real.exp (3 * a y) * Real.exp (-2 * a y) = Real.exp (a y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (3 * a y) * Real.exp (-2 * a y)) *
        (vol g y * ⟪inverseMetricOperator g y (gradient f y), b i⟫_ℝ) := by ring
      _ = _ := by rw [he]; ring
  have hrewrite : densityWeightedDivergence b (vol (EnergyBridge.conformalMatrix g a))
      (fun y => inverseMetricOperator (EnergyBridge.conformalMatrix g a) y (gradient f y)) x =
      densityWeightedDivergence b (fun y => Real.exp (a y) * vol g y)
        (fun y => inverseMetricOperator g y (gradient f y)) x := by
    simp only [densityWeightedDivergence, hflux]
  rw [hrewrite, densityWeightedDivergence_mul_density b _ _ _ x
    ((ha.differentiable (by simp) x).exp)
    ((EnergyBridge.contDiff_vol_of_smooth_posDef g hs hp).differentiable (by simp) x)
    (((contDiff_inverseMetricOperator_of_smooth_posDef g hs hp).clm_apply
      (hf.gradient_right (m := ∞) (by simp))).differentiable (by simp) x)]
  rw [inner_gradient_left, fderiv_exp (ha.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← inner_gradient_left]
  ring

lemma conformal_metric_divergence_quotient {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (a f : R3 → ℝ) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (x : R3) :
    (vol (EnergyBridge.conformalMatrix g a) x)⁻¹ *
        densityWeightedDivergence b (vol (EnergyBridge.conformalMatrix g a))
          (fun y => inverseMetricOperator (EnergyBridge.conformalMatrix g a) y (gradient f y)) x =
      Real.exp (-2 * a x) * ((vol g x)⁻¹ * densityWeightedDivergence b (vol g)
        (fun y => inverseMetricOperator g y (gradient f y)) x +
          ⟪gradient a x, inverseMetricOperator g x (gradient f x)⟫_ℝ) := by
  rw [EnergyBridge.vol_conformalMatrix, densityWeightedDivergence_conformalMatrix b g hs hp a f ha hf]
  have hv : vol g x ≠ 0 := ne_of_gt (EnergyBridge.vol_pos_of_posDef g hp x)
  have he : (Real.exp (3 * a x))⁻¹ * Real.exp (a x) = Real.exp (-2 * a x) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  rw [mul_inv_rev]
  calc
    _ = ((Real.exp (3 * a x))⁻¹ * Real.exp (a x)) *
      ((vol g x)⁻¹ * densityWeightedDivergence b (vol g)
        (fun y => inverseMetricOperator g y (gradient f y)) x +
        ⟪gradient a x, inverseMetricOperator g x (gradient f x)⟫_ℝ) := by
      field_simp
    _ = _ := by rw [he]

end OAI.AnisotropicCalderon.AngularPolynomial
