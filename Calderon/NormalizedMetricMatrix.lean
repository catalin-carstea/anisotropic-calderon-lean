import Calderon.ActualNormalizedGeodesicEllipticity

set_option autoImplicit false
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError

def operatorMatrixMap : (R3 →L[ℝ] R3) →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  matrixOperatorAlgEquiv.symm.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap

theorem operatorMatrixMap_apply (H : R3 →L[ℝ] R3) (u : R3) :
    (operatorMatrixMap H).toEuclideanLin u = H u := by
  change matrixOperatorAlgEquiv (matrixOperatorAlgEquiv.symm H) u = H u
  rw [matrixOperatorAlgEquiv.apply_symm_apply]

theorem operatorMatrixMap_metricOperatorField (g : MatrixField) (y : R3) :
    operatorMatrixMap (metricOperatorField g y) = g y :=
  matrixOperatorAlgEquiv.symm_apply_apply (g y)

theorem operatorMatrixMap_isHermitian (H : R3 →L[ℝ] R3)
    (hsym : ∀ u v, inner ℝ (H u) v = inner ℝ (H v) u) :
    (operatorMatrixMap H).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  intro u v
  rw [operatorMatrixMap_apply,operatorMatrixMap_apply]
  exact (hsym u v).trans (real_inner_comm _ _)

theorem operatorMatrixMap_posDef (H : R3 →L[ℝ] R3)
    (hsym : ∀ u v, inner ℝ (H u) v = inner ℝ (H v) u)
    (hpos : ∀ u : R3, u ≠ 0 → 0 < inner ℝ (H u) u) :
    (operatorMatrixMap H).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (operatorMatrixMap_isHermitian H hsym)
  intro x hx
  let u : R3 := WithLp.toLp 2 x
  have hu : u ≠ 0 := by
    intro hz
    apply hx
    exact congrArg WithLp.ofLp hz
  have hp := hpos u hu
  rw [← operatorMatrixMap_apply H u] at hp
  simpa [u,EuclideanSpace.inner_eq_star_dotProduct,Matrix.toEuclideanLin,
    Matrix.toLpLin_apply,dotProduct_comm] using hp

def normalizedEndpointMetricMatrix (Θ : R3 × R3 → R3) (M : R3 → R3 →L[ℝ] R3)
    (p : (R3 × ℝ) × R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  operatorMatrixMap (normalizedEndpointMetric Θ M p)

theorem contDiff_normalizedEndpointMetricMatrix (Θ : R3 × R3 → R3)
    (M : R3 → R3 →L[ℝ] R3) (hΘ : ContDiff ℝ ∞ Θ) (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (normalizedEndpointMetricMatrix Θ M) :=
  operatorMatrixMap.contDiff.comp (contDiff_normalizedEndpointMetric Θ M hΘ hM)

theorem normalizedEndpointMetric_symmetric (Θ : R3 × R3 → R3)
    (M : R3 → R3 →L[ℝ] R3)
    (hsym : ∀ x u v, inner ℝ (M x u) v = inner ℝ (M x v) u)
    (p : (R3 × ℝ) × R3) (u v : R3) :
    inner ℝ (normalizedEndpointMetric Θ M p u) v =
      inner ℝ (normalizedEndpointMetric Θ M p v) u := by
  rw [normalizedEndpointMetric_inner,normalizedEndpointMetric_inner]
  exact hsym _ _ _

theorem normalizedEndpointMetricMatrix_isHermitian (Θ : R3 × R3 → R3)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : (R3 × ℝ) × R3) :
    (normalizedEndpointMetricMatrix Θ (metricOperatorField g) p).IsHermitian :=
  operatorMatrixMap_isHermitian _
    (normalizedEndpointMetric_symmetric Θ _ (metricOperatorField_symmetric g hg) p)

theorem normalizedEndpointMetricMatrix_posDef (Θ : R3 × R3 → R3)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : (R3 × ℝ) × R3)
    (hJ : Function.Injective (normalizedEndpointDerivative Θ p)) :
    (normalizedEndpointMetricMatrix Θ (metricOperatorField g) p).PosDef :=
  operatorMatrixMap_posDef _
    (normalizedEndpointMetric_symmetric Θ _ (metricOperatorField_symmetric g hg) p)
    (normalizedEndpointMetric_pos Θ _ p (metricOperatorField_pos g hg) hJ)

theorem normalizedEndpointMetricMatrix_zero (Θ : R3 × R3 → R3) (g : MatrixField)
    (y z : R3) (hzero : Θ (y,0) = y)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0)) :
    normalizedEndpointMetricMatrix Θ (metricOperatorField g) ((y,0),z) = g y := by
  rw [normalizedEndpointMetricMatrix,normalizedEndpointMetric_zero Θ _ y z hzero hD,
    operatorMatrixMap_metricOperatorField]
end OAI.AnisotropicCalderon.MetricOperator
