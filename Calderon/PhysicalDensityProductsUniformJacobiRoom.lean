import Calderon.JointConformalReferenceFramedDriftData
import Calderon.ActualCompactNormalChart
import Calderon.SphereHarmonicBridge
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Tactic

/-!
Uniform invertibility of the actual normalized endpoint Jacobian, obtained
from the coercive actual normal metric in the original framed drift data.
The signed pointwise statement and the uniform positive-radius consequence
use the existing Euclidean structures on `R3`.
-/

open Set Metric
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

namespace OAI.AnisotropicCalderon.ConnectionError

/-- The original framed drift data make the actual normalized Jacobian
invertible throughout their signed center-radius-angular room. -/
theorem referenceFramedNormalizedJacobian_isInvertible_of_joint_framed_drift_data
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : y ∈ closedBall y0 ρ)
    (r : ℝ) (hr : |r| ≤ ρ)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))).IsInvertible := by
  classical
  have hCoeff : ConformalReferencePositiveCoefficientData g L y0 Φ B ε C ρ H a w :=
    hData.1
  have hMetric : ConformalReferenceFramedNormalMetricData g L y0 Φ B ε C :=
    hCoeff.1
  have hρ : 0 < ρ := hCoeff.2.1
  have hρε : 4 * ρ ≤ ε := hCoeff.2.2.1
  have hρε' : ρ ≤ ε := by linarith
  have hyε : ‖y - y0‖ ≤ ε := by
    exact le_trans (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy) hρε'
  have hrε : |r| ≤ ε := le_trans hr hρε'
  have hRoom := hMetric.2.2.2.2.2.2.1
  obtain ⟨_, _, _, _, _, _, hLower, _⟩ := hRoom q hq y hyε r hrε z hz
  let J : R3 →L[ℝ] R3 := referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))
  have hKernel : ∀ u : R3, J u = 0 → u = 0 := by
    intro u hu
    have hBound := hLower u
    dsimp only [J, referenceFramedNormalizedJacobian,
      conformalReferenceGramFrameOperatorJoint, conformalReferenceOperatorJoint] at hu
    rw [conformalReferenceFramedNormalMetric_eq,
      framedNormalizedEndpointMetric_inner] at hBound
    simp only [hu, inner_zero_right] at hBound
    have hNormSq : ‖u‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖u‖]
    have hNorm : ‖u‖ = 0 := by
      nlinarith [norm_nonneg u]
    exact norm_eq_zero.mp hNorm
  have hInjective : Function.Injective J := by
    intro u v huv
    have hSub : J (u - v) = 0 := by
      rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hKernel (u - v) hSub)
  have hSurjective : Function.Surjective J :=
    LinearMap.surjective_of_injective (f := J.toLinearMap) hInjective
  have hKer : J.ker = ⊥ := LinearMap.ker_eq_bot.mpr hInjective
  have hRange : J.range = ⊤ := LinearMap.range_eq_top.mpr hSurjective
  change J.IsInvertible
  exact ⟨ContinuousLinearEquiv.ofBijective J hKer hRange,
    ContinuousLinearEquiv.coe_ofBijective J hKer hRange⟩

/-- A radius chosen before `q`, `R`, `y` and the unit direction supplies the
third original Products room conjunct, without a regularity premise on `R`. -/
theorem exists_referenceFramedNormalizedJacobian_uniform_room
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) :
    ∃ dJ : ℝ, 0 < dJ ∧ dJ ≤ ρ ∧ dJ ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ,
        ∀ y ∈ closedBall y0 ρ, 0 < R y → R y ≤ dJ →
          ∀ ξ : UnitSphere,
            (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible := by
  have hρ : 0 < ρ := hData.1.2.1
  refine ⟨min ρ 1, lt_min hρ zero_lt_one, min_le_left _ _, min_le_right _ _, ?_⟩
  intro q hq R y hy hRpos hRd ξ
  have hr : |R y| ≤ ρ := by
    rw [abs_of_pos hRpos]
    exact le_trans hRd (min_le_left ρ 1)
  have hξ : ‖ξ.val‖ = (1 : ℝ) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ξ.property
  have hz : ξ.val ∈ closedBall (0 : R3) 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hξ] using
      (by norm_num : (1 : ℝ) ≤ 2)
  exact referenceFramedNormalizedJacobian_isInvertible_of_joint_framed_drift_data
    g L y0 Φ B ε C ρ H a w hData q hq y hy (R y) hr ξ.val hz

end OAI.AnisotropicCalderon.ConnectionError
