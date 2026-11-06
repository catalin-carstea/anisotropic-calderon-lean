import Calderon.ActualFramedPositiveMetric
import Calderon.ConformalReferenceOperators
import Calderon.WeightedMatrixCalculus
import Calderon.CompactInverseDerivativeBounds
import Mathlib.Analysis.Calculus.Gradient.Basic
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator DirichletFamily

def normalizedConformalDriftBase
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (Theta : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3) (p : (R3 × ℝ) × R3) : R3 :=
  matrixOperatorMap ((H p)⁻¹) ((framedNormalizedEndpointDerivative Theta F p).adjoint
    (gradient conformalReferenceCoordinateDepth (framedScaledEndpoint Theta F p)))

def normalizedConformalDrift
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (Theta : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3) (L : ℝ)
    (p : (R3 × ℝ) × R3) : R3 :=
  (-L*p.1.2) • normalizedConformalDriftBase H Theta F p

theorem contDiff_conformalReferenceDepthGradient :
    ContDiff ℝ ∞ (gradient conformalReferenceCoordinateDepth) :=
  (InnerProductSpace.toDual ℝ R3).symm.contDiff.comp
    (contDiff_conformalReferenceCoordinateDepth.fderiv_right (by simp))

theorem contDiff_normalizedConformalDriftBase
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ContDiff ℝ ∞ H) (hp : ∀ p, (H p).PosDef)
    (Theta : R3 × R3 → R3) (hTheta : ContDiff ℝ ∞ Theta)
    (F : R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (normalizedConformalDriftBase H Theta F) := by
  have hA : ContDiff ℝ ∞ (fun J : R3 →L[ℝ] R3 => J.adjoint) :=
    (ContinuousLinearMap.adjoint : (R3 →L[ℝ] R3) ≃ₗᵢ[ℝ] (R3 →L[ℝ] R3)).contDiff
  exact (matrixOperatorMap.contDiff.comp (contDiff_matrixFamily_inverse H hH hp)).clm_apply
    ((hA.comp (contDiff_framedNormalizedEndpointDerivative Theta F hTheta hF)).clm_apply
      (contDiff_conformalReferenceDepthGradient.comp (contDiff_framedScaledEndpoint Theta F hTheta hF)))

theorem contDiff_normalizedConformalDrift
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ContDiff ℝ ∞ H) (hp : ∀ p, (H p).PosDef)
    (Theta : R3 × R3 → R3) (hTheta : ContDiff ℝ ∞ Theta)
    (F : R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F) (L : ℝ) :
    ContDiff ℝ ∞ (normalizedConformalDrift H Theta F L) :=
  (contDiff_const.mul contDiff_fst.snd).smul
    (contDiff_normalizedConformalDriftBase H hH hp Theta hTheta F hF)

theorem matrixOperatorMap_inverse_cancel (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hp : H.PosDef) (v : R3) : matrixOperatorMap H (matrixOperatorMap (H⁻¹) v) = v := by
  change (matrixOperatorAlgEquiv H * matrixOperatorAlgEquiv (H⁻¹)) v = v
  rw [← map_mul,Matrix.mul_nonsing_inv H ((isUnit_iff_ne_zero).mpr (ne_of_gt hp.det_pos)),map_one]
  rfl

theorem normalizedConformalDriftBase_metric_identity
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hp : ∀ p, (H p).PosDef) (Theta : R3 × R3 → R3)
    (F : R3 → R3 →L[ℝ] R3) (p : (R3 × ℝ) × R3) :
    matrixOperatorMap (H p) (normalizedConformalDriftBase H Theta F p) =
      (framedNormalizedEndpointDerivative Theta F p).adjoint
        (gradient conformalReferenceCoordinateDepth (framedScaledEndpoint Theta F p)) :=
  matrixOperatorMap_inverse_cancel (H p) (hp p) _

theorem normalizedConformalDrift_local_metric_identity
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hp : ∀ p, (H p).PosDef) (Theta : R3 × R3 → R3)
    (M F : R3 → R3 →L[ℝ] R3) (L : ℝ) (p : (R3 × ℝ) × R3)
    (heq : H p = framedNormalizedEndpointMetricMatrix Theta M F p) :
    framedNormalizedEndpointMetric Theta M F p (normalizedConformalDrift H Theta F L p) =
      (-L*p.1.2) • ((framedNormalizedEndpointDerivative Theta F p).adjoint
        (gradient conformalReferenceCoordinateDepth (framedScaledEndpoint Theta F p))) := by
  have h := normalizedConformalDriftBase_metric_identity H hp Theta F p
  rw [heq] at h
  change (operatorMatrixMap (framedNormalizedEndpointMetric Theta M F p)).toEuclideanLin
    (normalizedConformalDriftBase H Theta F p) = _ at h
  rw [operatorMatrixMap_apply] at h
  simp only [normalizedConformalDrift,map_smul,h]

theorem normalizedConformalDrift_zero
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (Theta : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3) (L : ℝ) (y z : R3) :
    normalizedConformalDrift H Theta F L ((y,0),z) = 0 := by
  simp [normalizedConformalDrift]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_normalizedConformalDrift_zero
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ContDiff ℝ ∞ H) (hp : ∀ p, (H p).PosDef)
    (Theta : R3 × R3 → R3) (hTheta : ContDiff ℝ ∞ Theta)
    (F : R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F) (L : ℝ) (y z : R3) :
    HasDerivAt (fun r : ℝ => normalizedConformalDrift H Theta F L ((y,r),z))
      (-L • normalizedConformalDriftBase H Theta F ((y,0),z)) 0 := by
  have hb : ContDiff ℝ ∞ (fun r : ℝ => normalizedConformalDriftBase H Theta F ((y,r),z)) :=
    (contDiff_normalizedConformalDriftBase H hH hp Theta hTheta F hF).comp
      ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hd := ((hasDerivAt_id (0 : ℝ)).fun_smul
    ((hb.differentiable (by simp) 0).hasDerivAt)).fun_const_smul (-L)
  simpa only [normalizedConformalDrift,Pi.smul_apply,smul_smul,
    zero_smul,one_smul,zero_add,id_eq] using hd

theorem exists_compact_normalizedConformalDrift_bounds
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ContDiff ℝ ∞ H) (hp : ∀ p, (H p).PosDef)
    (Theta : R3 × R3 → R3) (hTheta : ContDiff ℝ ∞ Theta)
    (F : R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F) (L : ℝ)
    (q : Set ((R3 × ℝ) × R3)) (hq : IsCompact q) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ n : ℕ, n ≤ N → ∀ p ∈ q, ‖iteratedFDeriv ℝ n (normalizedConformalDriftBase H Theta F) p‖ ≤ C) ∧
      ∀ p ∈ q, ‖normalizedConformalDrift H Theta F L p‖ ≤ |L| * C*|p.1.2| := by
  have hb := contDiff_normalizedConformalDriftBase H hH hp Theta hTheta F hF
  obtain ⟨C,hC,hder⟩ := exists_compact_iteratedFDeriv_bound
    (normalizedConformalDriftBase H Theta F) q hq (fun _ _ => hb.contDiffAt) N
  obtain ⟨D,hval⟩ := hq.exists_bound_of_continuousOn hb.continuous.continuousOn
  let K := max C (max D 0)
  refine ⟨K,le_trans hC (le_max_left _ _),?_,?_⟩
  · intro n hn p hpq
    exact (hder n hn p hpq).trans (le_max_left _ _)
  · intro p hpq
    have hv : ‖normalizedConformalDriftBase H Theta F p‖ ≤ K :=
      (hval p hpq).trans ((le_max_left D 0).trans (le_max_right C (max D 0)))
    calc
      _ = |L| * |p.1.2| * ‖normalizedConformalDriftBase H Theta F p‖ := by
        simp only [normalizedConformalDrift,norm_smul,Real.norm_eq_abs,abs_mul,abs_neg]
      _ ≤ |L| * |p.1.2| * K := mul_le_mul_of_nonneg_left hv (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by ring
end OAI.AnisotropicCalderon.ConnectionError
