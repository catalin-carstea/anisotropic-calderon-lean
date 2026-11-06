import Calderon.CoordinateConnection
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI.AnisotropicCalderon.ConformalDepth
open OAI.AnisotropicCalderon.ConnectionError
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def metricGradient (Q : E →L[ℝ] E) (T : E →L[ℝ] ℝ) : E :=
  Q ((InnerProductSpace.toDual ℝ E).symm T)

lemma inner_metricGradient (Q M : E →L[ℝ] E) (T : E →L[ℝ] ℝ)
    (hMQ : ∀ z, M (Q z) = z) (Z : E) :
    inner ℝ (M (metricGradient Q T)) Z = T Z := by
  simp only [metricGradient, hMQ, InnerProductSpace.toDual_symm_apply]

noncomputable def conformalMetricDerivative (a L : ℝ) (M : E →L[ℝ] E)
    (D : E →L[ℝ] (E →L[ℝ] E)) (T : E →L[ℝ] ℝ) : E →L[ℝ] (E →L[ℝ] E) :=
  a • D + ((-2*L*a) • T).smulRight M

noncomputable def conformalConnection (L : ℝ) (Q M : E →L[ℝ] E)
    (D : E →L[ℝ] (E →L[ℝ] E)) (T : E →L[ℝ] ℝ) (X Y : E) : E :=
  coordinateConnection Q D X Y - L •
    (T X • Y + T Y • X - (inner ℝ (M X) Y) • metricGradient Q T)

theorem coordinateConnection_conformal (a L : ℝ) (Q M : E →L[ℝ] E)
    (D : E →L[ℝ] (E →L[ℝ] E)) (T : E →L[ℝ] ℝ) (ha : a ≠ 0)
    (hQM : ∀ z, Q (M z) = z) (hMQ : ∀ z, M (Q z) = z)
    (hsym : ∀ X Y, inner ℝ (M X) Y = inner ℝ (M Y) X) (X Y : E) :
    coordinateConnection (a⁻¹ • Q) (conformalMetricDerivative a L M D T) X Y =
      conformalConnection L Q M D T X Y := by
  have hMQ' : ∀ z, (a • M) ((a⁻¹ • Q) z) = z := by
    intro z
    simp only [smul_apply, map_smul, hMQ, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hM : M (coordinateConnection (a⁻¹ • Q)
        (conformalMetricDerivative a L M D T) X Y) =
      M (conformalConnection L Q M D T X Y) := by
    apply ext_inner_right ℝ
    intro Z
    have hg := coordinateConnection_koszul Q M D hMQ X Y Z
    have hγ := coordinateConnection_koszul (a⁻¹ • Q) (a • M)
      (conformalMetricDerivative a L M D T) hMQ' X Y Z
    have hXZ := hsym X Z
    have hYZ := hsym Y Z
    simp only [conformalMetricDerivative, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, map_smul, inner_add_left,
      real_inner_smul_left, smul_eq_mul] at hγ
    have hR : inner ℝ (M (conformalConnection L Q M D T X Y)) Z =
        inner ℝ (M (coordinateConnection Q D X Y)) Z - L *
          (T X * inner ℝ (M Y) Z + T Y * inner ℝ (M X) Z -
            inner ℝ (M X) Y * T Z) := by
      simp only [conformalConnection, map_sub, map_smul, map_add,
        inner_sub_left, inner_add_left, real_inner_smul_left,
        inner_metricGradient Q M T hMQ]
    rw [hR]
    have heq : a * (2 * inner ℝ (M (coordinateConnection (a⁻¹ • Q)
        (conformalMetricDerivative a L M D T) X Y)) Z -
        2 * (inner ℝ (M (coordinateConnection Q D X Y)) Z - L *
          (T X * inner ℝ (M Y) Z + T Y * inner ℝ (M X) Z -
            inner ℝ (M X) Y * T Z))) = 0 := by
      dsimp only [conformalMetricDerivative]
      linear_combination hγ - a * hg
    have hz := (mul_eq_zero.mp heq).resolve_left ha
    linarith
  calc
    _ = Q (M (coordinateConnection (a⁻¹ • Q)
          (conformalMetricDerivative a L M D T) X Y)) := (hQM _).symm
    _ = Q (M (conformalConnection L Q M D T X Y)) := congrArg Q hM
    _ = _ := hQM _

theorem hasFDerivAt_conformalMetric (L : ℝ) (t : E → ℝ)
    (M : E → E →L[ℝ] E) (x : E) (T : E →L[ℝ] ℝ)
    (D : E →L[ℝ] (E →L[ℝ] E)) (ht : HasFDerivAt t T x)
    (hM : HasFDerivAt M D x) :
    HasFDerivAt (fun y => Real.exp (-2*L*t y) • M y)
      (conformalMetricDerivative (Real.exp (-2*L*t x)) L (M x) D T) x := by
  have ha := (ht.const_smul (-2*L)).exp
  have h := ha.smul hM
  convert! h using 1 <;>
    simp only [conformalMetricDerivative, Pi.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  ring

#print axioms coordinateConnection_conformal
#print axioms hasFDerivAt_conformalMetric
end OAI.AnisotropicCalderon.ConformalDepth
