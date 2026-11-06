import Calderon.NormalizedMetricMatrix
import Calderon.MetricUniform

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError

theorem matrixOperator_inner (A : Matrix (Fin 3) (Fin 3) ℝ) (u v : R3) :
    inner ℝ (matrixOperatorMap A v) u = u ⬝ᵥ (A *ᵥ v) := by
  change inner ℝ (A.toEuclideanLin v) u = u ⬝ᵥ (A *ᵥ v)
  simp [EuclideanSpace.inner_eq_star_dotProduct,Matrix.toEuclideanLin,Matrix.toLpLin_apply]

theorem matrixOperator_posDef (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosDef)
    (u : R3) (hu : u ≠ 0) : 0 < inner ℝ (matrixOperatorMap A u) u := by
  rw [matrixOperator_inner]
  apply hA.dotProduct_mulVec_pos
  intro hz
  apply hu
  ext i
  exact congrFun hz i

theorem exists_compact_matrix_uniformlyElliptic {P : Type*} [TopologicalSpace P]
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : Continuous a)
    (q : Set P) (hq : IsCompact q) (K : Set R3) (hK : IsCompact K)
    (hpos : ∀ p ∈ q ×ˢ K, (a p).PosDef) :
    ∃ lam Lam : ℝ, ∀ p ∈ q,
      TauCeti.PDE.UniformlyEllipticOn K (fun z => a (p,z)) lam Lam := by
  obtain ⟨lam,U,hlam,_,hB⟩ := exists_compact_operator_ellipticity
    (fun p => matrixOperatorMap (a p)) (matrixOperatorMap.continuous.comp ha)
    (q ×ˢ K) (hq.prod hK) (fun p hp => matrixOperator_posDef (a p) (hpos p hp))
  refine ⟨lam,max U lam,?_⟩
  intro p hp
  refine ⟨hlam,le_max_right _ _,?_⟩
  intro z hz
  obtain ⟨hlo,hup⟩ := hB (p,z) ⟨hp,hz⟩
  constructor
  · intro ξ
    simpa only [matrixOperator_inner,Matrix.toQuadraticForm'_apply] using hlo ξ
  · intro η ξ
    have h := hup ξ η
    rw [matrixOperator_inner] at h
    calc
      |η ⬝ᵥ (a (p,z) *ᵥ ξ)| ≤ U * ‖ξ‖ * ‖η‖ := h
      _ ≤ max U lam * ‖ξ‖ * ‖η‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg ξ)) (norm_nonneg η)
      _ = max U lam * ‖η‖ * ‖ξ‖ := by ring
end OAI.AnisotropicCalderon.MetricOperator
