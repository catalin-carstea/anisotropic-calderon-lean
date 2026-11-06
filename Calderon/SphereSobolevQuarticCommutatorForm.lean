import Calderon.SphereSobolevPairing
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Native two-endpoint quartic weak form. This module proves its boundedness; the
identification with the pivot commutator and the squared-norm equality on finite inputs
are separate graph statements. No invariant finite-core assumption. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma commutator_sq_eq_four_words {R : Type*} [Ring R] (X Y : R) :
    X^2 * Y^2 - Y^2 * X^2 =
      X * (X*Y-Y*X) * Y + X * Y * (X*Y-Y*X) +
      (X*Y-Y*X) * Y * X + Y * (X*Y-Y*X) * X := by
  noncomm_ring

lemma abs_sphereSobolevDualPairing_comp_apply_le
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (B D : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (u : SphereSobolev (3/2 : ℝ)) :
    |sphereSobolevDualPairing (-(1/2 : ℝ)) (A (B u)) (D u)| ≤
      ‖A‖ * ‖B‖ * ‖D‖ * ‖u‖^2 := by
  calc
    _ ≤ ‖A (B u)‖ * ‖D u‖ := abs_sphereSobolevDualPairing_le _ _ _
    _ ≤ (‖A‖ * ‖B u‖) * ‖D u‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
    _ ≤ (‖A‖ * (‖B‖ * ‖u‖)) * (‖D‖ * ‖u‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (B.le_opNorm _) A.opNorm_nonneg)
        (D.le_opNorm _) (norm_nonneg _)
        (mul_nonneg A.opNorm_nonneg (mul_nonneg B.opNorm_nonneg (norm_nonneg u)))
    _ = _ := by ring

def sphereSobolevQuarticCommutatorWeakForm
    (SHigh SdagHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (SLow SdagLow : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (CHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (CLow : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (u : SphereSobolev (3/2 : ℝ)) : ℝ :=
  sphereSobolevDualPairing (-(1/2 : ℝ)) (CLow (SHigh u)) (SHigh u) +
  sphereSobolevDualPairing (-(1/2 : ℝ)) (SLow (CHigh u)) (SHigh u) +
  sphereSobolevDualPairing (-(1/2 : ℝ)) (SdagLow (CHigh u)) (SdagHigh u) +
  sphereSobolevDualPairing (-(1/2 : ℝ)) (CLow (SdagHigh u)) (SdagHigh u)

lemma abs_sphereSobolevQuarticCommutatorWeakForm_le
    (SHigh SdagHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (SLow SdagLow : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (CHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (CLow : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (u : SphereSobolev (3/2 : ℝ)) :
    |sphereSobolevQuarticCommutatorWeakForm SHigh SdagHigh SLow SdagLow CHigh CLow u| ≤
      (‖CLow‖ * (‖SHigh‖^2 + ‖SdagHigh‖^2) +
        ‖CHigh‖ * (‖SLow‖ * ‖SHigh‖ + ‖SdagLow‖ * ‖SdagHigh‖)) * ‖u‖^2 := by
  have h1 := abs_sphereSobolevDualPairing_comp_apply_le CLow SHigh SHigh u
  have h2 := abs_sphereSobolevDualPairing_comp_apply_le SLow CHigh SHigh u
  have h3 := abs_sphereSobolevDualPairing_comp_apply_le SdagLow CHigh SdagHigh u
  have h4 := abs_sphereSobolevDualPairing_comp_apply_le CLow SdagHigh SdagHigh u
  let a := sphereSobolevDualPairing (-(1/2 : ℝ)) (CLow (SHigh u)) (SHigh u)
  let b := sphereSobolevDualPairing (-(1/2 : ℝ)) (SLow (CHigh u)) (SHigh u)
  let c := sphereSobolevDualPairing (-(1/2 : ℝ)) (SdagLow (CHigh u)) (SdagHigh u)
  let d := sphereSobolevDualPairing (-(1/2 : ℝ)) (CLow (SdagHigh u)) (SdagHigh u)
  have hAbs : |a+b+c+d| ≤ |a|+|b|+|c|+|d| := by
    have h12 := abs_add_le a b
    have h123 := abs_add_le (a+b) c
    have h1234 := abs_add_le (a+b+c) d
    linarith
  have hSum : |a|+|b|+|c|+|d| ≤
      ‖CLow‖*‖SHigh‖*‖SHigh‖*‖u‖^2 +
      ‖SLow‖*‖CHigh‖*‖SHigh‖*‖u‖^2 +
      ‖SdagLow‖*‖CHigh‖*‖SdagHigh‖*‖u‖^2 +
      ‖CLow‖*‖SdagHigh‖*‖SdagHigh‖*‖u‖^2 :=
    add_le_add (add_le_add (add_le_add h1 h2) h3) h4
  change |a+b+c+d| ≤ _
  exact (hAbs.trans hSum).trans_eq (by ring)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.commutator_sq_eq_four_words
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.abs_sphereSobolevDualPairing_comp_apply_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevQuarticCommutatorWeakForm
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.abs_sphereSobolevQuarticCommutatorWeakForm_le
