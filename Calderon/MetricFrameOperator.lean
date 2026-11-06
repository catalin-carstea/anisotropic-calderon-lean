import Calderon.SmoothCoordinateMetricFrame
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.NormalCoordinatesFrame

def frameOperator (e : Fin 3 → R3) : R3 →L[ℝ] R3 :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).smulRight (e i)

theorem frameOperator_apply (e : Fin 3 → R3) (v : R3) :
    frameOperator e v = ∑ i : Fin 3, v i • e i := by
  simp [frameOperator,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply]

theorem frameOperator_coordinateVector (e : Fin 3 → R3) (j : Fin 3) :
    frameOperator e (coordinateVector j) = e j := by
  rw [frameOperator_apply]
  simp [coordinateVector,PiLp.single_apply]

theorem metric_inner_frameOperator (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (u v : R3) :
    inner ℝ (M (frameOperator e u)) (frameOperator e v) = inner ℝ u v := by
  rw [frameOperator_apply,frameOperator_apply]
  simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  have he' : ∀ i j, inner ℝ (M (e i)) (e j) = if i=j then 1 else 0 := he
  simp_rw [he']
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]

theorem frameOperator_injective (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : Function.Injective (frameOperator e) := by
  intro u v huv
  have hz : frameOperator e (u-v) = 0 := by rw [map_sub,huv,sub_self]
  have h := metric_inner_frameOperator M e he (u-v) (u-v)
  have hi : inner ℝ (u-v) (u-v) = 0 := by
    simpa only [hz,map_zero,inner_zero_left] using h.symm
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hi)

theorem frameOperator_bijective (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : Function.Bijective (frameOperator e) :=
  ⟨frameOperator_injective M e he,
    (frameOperator e).toLinearMap.surjective_of_injective (frameOperator_injective M e he)⟩

theorem frameOperator_pullback_metric (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) :
    (frameOperator e).adjoint.comp (M.comp (frameOperator e)) = ContinuousLinearMap.id ℝ R3 := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  change inner ℝ ((frameOperator e).adjoint (M (frameOperator e u))) v = inner ℝ u v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact metric_inner_frameOperator M e he u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_frameOperator (e : E → Fin 3 → R3)
    (he : ∀ i, ContDiff ℝ ∞ (fun x => e x i)) :
    ContDiff ℝ ∞ (fun x => frameOperator (e x)) := by
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.smulRight (he i)

theorem contDiff_metricGramFrameOperator (M : E → R3 →L[ℝ] R3)
    (hM : ContDiff ℝ ∞ M)
    (hp : ∀ x, ∀ v : R3, v ≠ 0 → 0 < metricPair (M x) v v) :
    ContDiff ℝ ∞ (fun x => frameOperator (metricGramFrame (M x))) :=
  contDiff_frameOperator _ (contDiff_metricGramFrame M hM hp)

end OAI.AnisotropicCalderon.NormalCoordinatesFrame
