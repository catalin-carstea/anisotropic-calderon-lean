import Calderon.AngularCoefficient
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MeasureTheory

def weightedBaseDerivativePlus (k : ℝ) (a u : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv u x + k * a x * u x

def weightedBaseDerivativeMinus (k : ℝ) (a u : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv u x + k * a x * u x

lemma compact_base_cross_term (u a : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport u) :
    (∫ x : ℝ, a x * (2 * u x * deriv u x)) = -(∫ x : ℝ, deriv a x * u x ^ 2) := by
  have hu' : Differentiable ℝ u := hu.differentiable (by norm_num)
  have ha' : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hda : Continuous (deriv a) := ha.continuous_deriv (by norm_num)
  have h0 : Integrable (fun x : ℝ => a x * (u x * u x)) := by
    exact (ha.continuous.mul (hu.continuous.mul hu.continuous)).integrable_of_hasCompactSupport
      (hc.mul_right.mul_left)
  have h1 : Integrable (fun x : ℝ => deriv a x * (u x * u x)) := by
    exact (hda.mul (hu.continuous.mul hu.continuous)).integrable_of_hasCompactSupport
      (hc.mul_right.mul_left)
  have h2' : Integrable (fun x : ℝ => a x * (u x * (2 * deriv u x))) := by
    exact (ha.continuous.mul (hu.continuous.mul (continuous_const.mul hdu))).integrable_of_hasCompactSupport
      (hc.mul_right.mul_left)
  have h2 : Integrable (fun x : ℝ => a x * (2 * u x * deriv u x)) := by
    convert h2' using 1
    funext x
    ring
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := a) (v := fun x => u x * u x) (u' := deriv a) (v' := fun x => 2 * u x * deriv u x)
    (fun x hx => (ha' x).hasDerivAt)
    (fun x hx => by
      convert ((hu' x).hasDerivAt.mul (hu' x).hasDerivAt) using 1 <;> ring)
    h2 h1 h0
  simpa only [pow_two] using hparts

lemma compact_base_square_integrable (u : ℝ → ℝ) (hu : Continuous u)
    (hc : HasCompactSupport u) : Integrable (fun x => u x ^ 2) := by
  have hsupport : HasCompactSupport (fun x : ℝ => u x ^ 2) := by
    simpa only [pow_two] using
      (show HasCompactSupport (fun x : ℝ => u x * u x) from hc.mul_right)
  exact (hu.pow 2).integrable_of_hasCompactSupport hsupport

lemma compact_base_cross_integrable (u a : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (ha : Continuous a) (hc : HasCompactSupport u) :
    Integrable (fun x : ℝ => a x * (2 * u x * deriv u x)) := by
  have hdu := hu.continuous_deriv (by norm_num)
  have h : Integrable (fun x : ℝ => a x * (u x * (2 * deriv u x))) :=
    (ha.mul (hu.continuous.mul (continuous_const.mul hdu))).integrable_of_hasCompactSupport
      (hc.mul_right.mul_left)
  convert h using 1
  funext x
  ring

lemma weightedBaseDerivativePlus_square_integrable (k : ℝ) (a u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (ha : Continuous a) (hc : HasCompactSupport u) :
    Integrable (fun x => weightedBaseDerivativePlus k a u x ^ 2) := by
  have hdu := hu.continuous_deriv (by norm_num)
  have hcont : Continuous (weightedBaseDerivativePlus k a u) :=
    hdu.add ((continuous_const.mul ha).mul hu.continuous)
  have hku : HasCompactSupport (fun x => k * a x * u x) := hc.mul_left
  have hsupport : HasCompactSupport (weightedBaseDerivativePlus k a u) := hc.deriv.add hku
  exact compact_base_square_integrable _ hcont hsupport

lemma weightedBaseDerivativeMinus_square_integrable (k : ℝ) (a u : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (ha : Continuous a) (hc : HasCompactSupport u) :
    Integrable (fun x => weightedBaseDerivativeMinus k a u x ^ 2) := by
  have hdu := hu.continuous_deriv (by norm_num)
  have hcont : Continuous (weightedBaseDerivativeMinus k a u) :=
    hdu.neg.add ((continuous_const.mul ha).mul hu.continuous)
  have hku : HasCompactSupport (fun x => k * a x * u x) := hc.mul_left
  have hsupport : HasCompactSupport (weightedBaseDerivativeMinus k a u) := hc.deriv.neg.add hku
  exact compact_base_square_integrable _ hcont hsupport

theorem compact_base_weighted_square_difference (k : ℝ) (u a : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport u) :
    (∫ x : ℝ, weightedBaseDerivativeMinus k a u x ^ 2) =
      (∫ x : ℝ, weightedBaseDerivativePlus k a u x ^ 2) +
        2 * k * (∫ x : ℝ, deriv a x * u x ^ 2) := by
  have hplus := weightedBaseDerivativePlus_square_integrable k a u hu ha.continuous hc
  have hcross := (compact_base_cross_integrable u a hu ha.continuous hc).const_mul (2 * k)
  have hpoint : (fun x => weightedBaseDerivativeMinus k a u x ^ 2) =
      fun x => weightedBaseDerivativePlus k a u x ^ 2 - 2 * k * (a x * (2 * u x * deriv u x)) := by
    funext x
    simp only [weightedBaseDerivativeMinus, weightedBaseDerivativePlus]
    ring
  rw [hpoint, integral_sub hplus hcross, integral_const_mul, compact_base_cross_term u a hu ha hc]
  ring

theorem compact_base_weighted_square_expansion (k : ℝ) (u a : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport u) :
    (∫ x : ℝ, weightedBaseDerivativePlus k a u x ^ 2) =
      (∫ x : ℝ, deriv u x ^ 2) + k ^ 2 * (∫ x : ℝ, a x ^ 2 * u x ^ 2) -
        k * (∫ x : ℝ, deriv a x * u x ^ 2) := by
  have hderiv := compact_base_square_integrable (deriv u) (hu.continuous_deriv (by norm_num)) hc.deriv
  have hsupport : HasCompactSupport (fun x : ℝ => u x ^ 2) := by
    simpa only [pow_two] using
      (show HasCompactSupport (fun x : ℝ => u x * u x) from hc.mul_right)
  have havalue : Integrable (fun x => a x ^ 2 * u x ^ 2) := by
    exact ((ha.continuous.pow 2).mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport
      hsupport.mul_left
  have hvalue := havalue.const_mul (k ^ 2)
  have hcross := (compact_base_cross_integrable u a hu ha.continuous hc).const_mul k
  have hpoint : (fun x => weightedBaseDerivativePlus k a u x ^ 2) =
      fun x => (deriv u x ^ 2 + k ^ 2 * (a x ^ 2 * u x ^ 2)) +
        k * (a x * (2 * u x * deriv u x)) := by
    funext x
    simp only [weightedBaseDerivativePlus]
    ring
  rw [hpoint, integral_add (f := fun x : ℝ => deriv u x ^ 2 + k ^ 2 * (a x ^ 2 * u x ^ 2))
    (g := fun x : ℝ => k * (a x * (2 * u x * deriv u x)))
    (hderiv.add hvalue) hcross, integral_add hderiv hvalue,
    integral_const_mul, integral_const_mul, compact_base_cross_term u a hu ha hc]
  ring

theorem compact_base_weighted_gradient_lower_bound (k : ℝ) (hk : 0 ≤ k) (u a : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport u)
    (ha' : ∀ x, deriv a x ≤ 0) :
    (∫ x : ℝ, deriv u x ^ 2) + k ^ 2 * (∫ x : ℝ, a x ^ 2 * u x ^ 2) ≤
      ∫ x : ℝ, weightedBaseDerivativePlus k a u x ^ 2 := by
  have hi : (∫ x : ℝ, deriv a x * u x ^ 2) ≤ 0 :=
    integral_nonpos_of_ae (Filter.Eventually.of_forall fun x => mul_nonpos_of_nonpos_of_nonneg (ha' x) (sq_nonneg _))
  rw [compact_base_weighted_square_expansion k u a hu ha hc]
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hk hi
  linarith

end OAI.AnisotropicCalderon.AngularPolynomial
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_base_cross_term

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_base_weighted_square_difference
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_base_weighted_square_expansion
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_base_weighted_gradient_lower_bound
