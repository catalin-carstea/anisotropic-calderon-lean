import Calderon.StrictWeightHessianDictionary

/-! Exact source metric-unit strictness implies the native raw condition. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Operator
namespace OAI.AnisotropicCalderon
open MetricOperator MetricVolume ConnectionError

theorem strict_weight_inverseMetric_of_unitHessian
    (g : MatrixField) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian)
    (hgrad : grad f x ≠ 0)
    (hunit :
      let b : R3 := matrixOperatorMap ((g x)⁻¹) (WithLp.toLp 2 (grad f x))
      let e : R3 := (Real.sqrt ⟪metricOperatorField g x b, b⟫_ℝ)⁻¹ • b
      ∀ v : R3, ⟪metricOperatorField g x v, e⟫_ℝ = 0 →
        ⟪metricOperatorField g x v, v⟫_ℝ = 1 →
        0 < RadiusProfile.coordinateHessian f
          (fun X Y => coordinateConnectionField
            (inverseMetricField (metricOperatorField g)) (metricOperatorField g) x X Y) x e e +
          RadiusProfile.coordinateHessian f
          (fun X Y => coordinateConnectionField
            (inverseMetricField (metricOperatorField g)) (metricOperatorField g) x X Y) x v v) :
    ∀ xi : Fin 3 → ℝ,
      (∑ j : Fin 3, bv (fun i k y => (g y)⁻¹ i k) f j x * xi j) = 0 →
      quad (fun i j y => (g y)⁻¹ i j) x xi = Nf (fun i j y => (g y)⁻¹ i j) f x →
      0 < Mgrad (fun i j y => (g y)⁻¹ i j)
          (bv (fun i j y => (g y)⁻¹ i j) f) x (grad f x) +
        Mgrad (fun i j y => (g y)⁻¹ i j)
          (bv (fun i j y => (g y)⁻¹ i j) f) x xi := by
  classical
  let a : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => (g y)⁻¹ i j
  let p : Fin 3 → ℝ := grad f x
  let A : Matrix (Fin 3) (Fin 3) ℝ := (g x)⁻¹
  let M : R3 →L[ℝ] R3 := metricOperatorField g x
  let b : R3 := matrixOperatorMap A (WithLp.toLp 2 p)
  let n : ℝ := ⟪M b, b⟫_ℝ
  let t : ℝ := (Real.sqrt n)⁻¹
  let e : R3 := t • b
  let Gamma : R3 →L[ℝ] R3 →L[ℝ] R3 :=
    coordinateConnectionField (inverseMetricField (metricOperatorField g)) (metricOperatorField g) x
  let H : R3 →L[ℝ] R3 →L[ℝ] ℝ := coordinateHessianBilinear f Gamma x
  have hGA : ∀ U : R3, M (matrixOperatorMap A U) = U := by
    have hmat : g x * A = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit)
    have hop : matrixOperatorMap (g x) * matrixOperatorMap A = 1 := by
      change matrixOperatorAlgEquiv (g x) * matrixOperatorAlgEquiv A = 1
      rw [← map_mul, hmat, map_one]
    intro U
    change (matrixOperatorMap (g x) * matrixOperatorMap A) U = U
    rw [hop]
    rfl
  have hBcoord : ∀ i, b i = bv a f i x := fun i => rfl
  have hQuad : ∀ xi : Fin 3 → ℝ,
      ⟪M (matrixOperatorMap A (WithLp.toLp 2 xi)),
        matrixOperatorMap A (WithLp.toLp 2 xi)⟫_ℝ = quad a x xi := by
    intro xi
    rw [hGA]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      Pi.star_apply, star_trivial, dotProduct, matrixOperator_coordinate, quad,
      PiLp.toLp_apply, Fin.sum_univ_three, A, a]
    ring
  have hNQ : Nf a f x = quad a x p := by
    simp only [Nf, bv, p, grad, quad, Fin.sum_univ_three]
    ring
  have hnN : n = Nf a f x := (hQuad p).trans hNQ.symm
  have hn : 0 < n := by
    rw [hnN, hNQ]
    convert hp.inv.dotProduct_mulVec_pos hgrad using 1 <;>
      simp [a, p, quad, dotProduct, Matrix.mulVec, Fin.sum_univ_three] <;> ring
  have hGradient : ∀ Y : R3, ⟪M b, Y⟫_ℝ = fderiv ℝ f x Y := by
    intro Y
    change ⟪M (matrixOperatorMap A (WithLp.toLp 2 p)), Y⟫_ℝ = _
    rw [hGA, covector_coordinate_sum (fderiv ℝ f x) Y]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      Pi.star_apply, star_trivial, dotProduct, p, grad, pd, coordinateVector]
  have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hn)
  have htn : t ^ 2 * n = 1 := by
    simp only [t, inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']
  have heUnit : ⟪M e, e⟫_ℝ = 1 := by
    simp only [e, map_smul, inner_smul_left, inner_smul_right, conj_trivial]
    change t * (t * n) = 1
    nlinarith only [htn]
  have hH : ∀ U V, H U V = RadiusProfile.coordinateHessian f (fun X Y => Gamma X Y) x U V :=
    fun U V => coordinateHessianBilinear_apply f Gamma x U V
  change ∀ v : R3, ⟪M v, e⟫_ℝ = 0 → ⟪M v, v⟫_ℝ = 1 →
    0 < RadiusProfile.coordinateHessian f (fun X Y => Gamma X Y) x e e +
      RadiusProfile.coordinateHessian f (fun X Y => Gamma X Y) x v v at hunit
  intro xi hOrth hNorm
  change (∑ j : Fin 3, bv a f j x * xi j) = 0 at hOrth
  change quad a x xi = Nf a f x at hNorm
  let V : R3 := matrixOperatorMap A (WithLp.toLp 2 xi)
  let v : R3 := t • V
  have hVnorm : ⟪M V, V⟫_ℝ = n := (hQuad xi).trans (hNorm.trans hnN.symm)
  have hVorth : ⟪M V, b⟫_ℝ = 0 := by
    change ⟪M (matrixOperatorMap A (WithLp.toLp 2 xi)), b⟫_ℝ = 0
    rw [hGA]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      Pi.star_apply, star_trivial, dotProduct, hBcoord] using hOrth
  have hvUnit : ⟪M v, v⟫_ℝ = 1 := by
    simp only [v, map_smul, inner_smul_left, inner_smul_right, conj_trivial, hVnorm]
    nlinarith only [htn]
  have hvOrth : ⟪M v, e⟫_ℝ = 0 := by
    simp only [v, e, map_smul, inner_smul_left, inner_smul_right, conj_trivial,
      hVorth, mul_zero]
  have hPositive := hunit v hvOrth hvUnit
  rw [← hH e e, ← hH v v] at hPositive
  simp only [v, e, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at hPositive
  have hScaled : 0 < t ^ 2 * (H b b + H V V) := by nlinarith only [hPositive]
  have hUnscaled : 0 < H b b + H V V := pos_of_mul_pos_right hScaled (sq_nonneg t)
  have hMp : Mgrad a (bv a f) x p = 4 * H b b := by
    simpa only [a, p, b, A, H, Gamma, coordinateHessianBilinear_apply] using
      Mgrad_inverseMetric_eq_four_coordinateHessian g f hf x hg hp hs p
  have hMxi : Mgrad a (bv a f) x xi = 4 * H V V := by
    simpa only [a, V, A, H, Gamma, coordinateHessianBilinear_apply] using
      Mgrad_inverseMetric_eq_four_coordinateHessian g f hf x hg hp hs xi
  change 0 < Mgrad a (bv a f) x p + Mgrad a (bv a f) x xi
  rw [hMp, hMxi]
  nlinarith only [hUnscaled]

end OAI.AnisotropicCalderon

#print axioms OAI.AnisotropicCalderon.strict_weight_inverseMetric_of_unitHessian
