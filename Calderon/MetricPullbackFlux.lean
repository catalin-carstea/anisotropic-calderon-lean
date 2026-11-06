import Calderon.CoordinatePiolaCovariance
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-! Source-only author C2 stage. Exact matrix/gradient/absolute-volume
flux expansion and interfaces were sealed before proof bodies. No physical
harmonic kernel or full moving-trace closure is claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open scoped Matrix
open MetricOperator MetricVolume EnergyBridge

theorem operatorMatrixMap_comp (A B : R3 →L[ℝ] R3) :
    operatorMatrixMap (A.comp B) = operatorMatrixMap A * operatorMatrixMap B := by
  change matrixOperatorAlgEquiv.symm (A * B) =
    matrixOperatorAlgEquiv.symm A * matrixOperatorAlgEquiv.symm B
  exact matrixOperatorAlgEquiv.symm.map_mul A B

theorem operatorMatrixMap_adjoint (A : R3 →L[ℝ] R3) :
    operatorMatrixMap A.adjoint = (operatorMatrixMap A)ᵀ := by
  have hEntry (K : R3 →L[ℝ] R3) (i j : Fin 3) :
      operatorMatrixMap K i j = inner ℝ (K (coordinateVector j)) (coordinateVector i) := by
    have h := matrixOperator_basis_inner (operatorMatrixMap K) i j
    change inner ℝ ((operatorMatrixMap K).toEuclideanLin (coordinateVector j))
      (coordinateVector i) = _ at h
    rw [operatorMatrixMap_apply] at h
    exact h.symm
  ext i j
  change operatorMatrixMap A.adjoint i j = operatorMatrixMap A j i
  rw [hEntry,hEntry,ContinuousLinearMap.adjoint_inner_left]
  exact real_inner_comm _ _

theorem sqrt_det_matrix_congruence (M J : Matrix (Fin 3) (Fin 3) ℝ) :
    Real.sqrt (Jᵀ * M * J).det = |J.det| * Real.sqrt M.det := by
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  have hprod : J.det * M.det * J.det = J.det^2 * M.det := by ring
  rw [hprod,Real.sqrt_mul (sq_nonneg J.det),Real.sqrt_sq_eq_abs]

theorem principalCoefficient_matrix_congruence_flux
    (M J : Matrix (Fin 3) (Fin 3) ℝ) (hJ : IsUnit J.det) :
    (Real.sqrt (Jᵀ * M * J).det • (Jᵀ * M * J)⁻¹) * Jᵀ =
      |J.det| • (J⁻¹ * (Real.sqrt M.det • M⁻¹)) := by
  rw [sqrt_det_matrix_congruence,Matrix.mul_inv_rev,Matrix.mul_inv_rev,Matrix.smul_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul Jᵀ
    (by simpa only [Matrix.det_transpose] using hJ),Matrix.mul_one]
  simp only [Matrix.mul_smul,smul_smul]

def pullbackMetric (g : MatrixField) (X : R3 → R3) : MatrixField :=
  fun x => operatorMatrixMap ((fderiv ℝ X x).adjoint.comp
    ((metricOperatorField g (X x)).comp (fderiv ℝ X x)))

theorem gradient_comp_eq_adjoint (X : R3 → R3) (u : R3 → ℝ)
    (hX : ContDiff ℝ ∞ X) (hu : ContDiff ℝ ∞ u) (x : R3) :
    gradient (u ∘ X) x = (fderiv ℝ X x).adjoint (gradient u (X x)) := by
  apply ext_inner_right ℝ
  intro V
  rw [inner_gradient_left,ContinuousLinearMap.adjoint_inner_left,inner_gradient_left]
  rw [fderiv_comp (𝕜 := ℝ) (f := X) (g := u) (x := x) (hu.differentiable (by simp) (X x)) (hX.differentiable (by simp) x)]
  rfl

theorem matrixOperatorMap_mul_apply (M N : Matrix (Fin 3) (Fin 3) ℝ) (V : R3) :
    matrixOperatorMap (M*N) V = matrixOperatorMap M (matrixOperatorMap N V) := by
  have h : matrixOperatorMap (M*N) = (matrixOperatorMap M).comp (matrixOperatorMap N) := by
    change matrixOperatorAlgEquiv (M*N) = matrixOperatorAlgEquiv M * matrixOperatorAlgEquiv N
    exact matrixOperatorAlgEquiv.map_mul M N
  rw [h]
  rfl

theorem metricDivergenceFlux_pullbackMetric (g : MatrixField)
    (X : R3 → R3) (u : R3 → ℝ) (hX : ContDiff ℝ ∞ X) (hu : ContDiff ℝ ∞ u)
    (x : R3) (hJ : IsUnit (coordinateJacobianMatrix X x).det) :
    metricDivergenceFlux (pullbackMetric g X) (u ∘ X) x =
      |(coordinateJacobianMatrix X x).det| •
        matrixOperatorMap ((coordinateJacobianMatrix X x)⁻¹) (metricDivergenceFlux g u (X x)) := by
  let A := coordinateJacobianMatrix X x
  have hG : pullbackMetric g X x = Aᵀ * g (X x) * A := by
    simp only [pullbackMetric,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,A,coordinateJacobianMatrix_eq_operatorMatrixMap,Matrix.mul_assoc]
  have hAT : matrixOperatorMap Aᵀ = (fderiv ℝ X x).adjoint := by
    dsimp only [A]
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap,← operatorMatrixMap_adjoint]
    apply ContinuousLinearMap.ext
    intro V
    exact operatorMatrixMap_apply _ V
  rw [metricDivergenceFlux,gradient_comp_eq_adjoint X u hX hu x]
  change matrixOperatorMap (Real.sqrt (pullbackMetric g X x).det • (pullbackMetric g X x)⁻¹)
      ((fderiv ℝ X x).adjoint (gradient u (X x))) =
    |A.det| • matrixOperatorMap A⁻¹
      (matrixOperatorMap (Real.sqrt (g (X x)).det • (g (X x))⁻¹) (gradient u (X x)))
  rw [← hAT,← matrixOperatorMap_mul_apply,hG,principalCoefficient_matrix_congruence_flux _ A hJ]
  simp only [map_smul,ContinuousLinearMap.smul_apply,matrixOperatorMap_mul_apply]

end OAI.AnisotropicCalderon.ConnectionError
