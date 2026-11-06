import Calderon.HarmonicDerivativeOperator
import Calderon.SphereRotationCore

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.HarmonicDerivativeBounds
open SphereHarmonic SphereHilbertDecomposition HarmonicDerivativeOperator
  SmoothSphereRotationProjection SphereDerivativeAdjoint AngularPolynomial

local instance (k : ℕ) : CompleteSpace (harmonicSphereSubspace k) :=
  completeSpace_harmonicSphereSubspace k

/-- The probability-sphere gradient identity also includes linear harmonics. -/
lemma sum_norm_sq_polynomialDerivative (hF : SphereFischerInner) (m : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous (m+1)) :
    (∑ i : Fin 3, ‖polynomialSphereL2 (pderiv i p)‖^2) =
      (((m:ℝ)+1)*(3+2*(m:ℝ))) * ‖polynomialSphereL2 p‖^2 := by
  simp_rw [polynomialSphereL2_norm_sq hF m _
    (pderiv_harmonicHomogeneous_succ m _ p hp)]
  rw [polynomialSphereL2_norm_sq hF (m+1) p hp]
  unfold normalizedFischerSquare normalizedFischerInner
  rw [← Finset.sum_div,sum_fischerInner_pderiv_self hp.1,
    sphereNormalization_succ]
  have hN : sphereNormalization 3 m ≠ 0 :=
    ne_of_gt (sphereNormalization_pos (by norm_num) m)
  simp only [Fintype.card_fin,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  have hc : (3:ℝ)+2*(m:ℝ) ≠ 0 := by positivity
  field_simp [hN,hc]
  <;> ring

lemma sum_norm_sq_harmonicDerivative (hF : SphereFischerInner) (m : ℕ)
    (u : harmonicSphereSubspace (m+1)) :
    (∑ i : Fin 3, ‖harmonicDerivative hF m i u‖^2) =
      (((m:ℝ)+1)*(3+2*(m:ℝ))) * ‖u‖^2 := by
  rcases harmonicPolynomialSphereMap_surjective (m+1) u with ⟨p,rfl⟩
  simp_rw [harmonicDerivative_apply_image]
  exact sum_norm_sq_polynomialDerivative hF m p p.property

attribute [local irreducible] harmonicDerivative harmonicDerivativeAdjoint

lemma norm_harmonicDerivative_apply_le (hF : SphereFischerInner) (m : ℕ)
    (i : Fin 3) (u : harmonicSphereSubspace (m+1)) :
    ‖harmonicDerivative hF m i u‖ ≤ (2*((m:ℝ)+1))*‖u‖ := by
  have hs : ‖harmonicDerivative hF m i u‖^2 ≤
      ∑ j : Fin 3, ‖harmonicDerivative hF m j u‖^2 :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 3 => ‖harmonicDerivative hF m j u‖^2)
      (fun j _ => sq_nonneg ‖harmonicDerivative hF m j u‖) (Finset.mem_univ i)
  rw [sum_norm_sq_harmonicDerivative] at hs
  have hc : ((m:ℝ)+1)*(3+2*(m:ℝ)) ≤ (2*((m:ℝ)+1))^2 := by
    nlinarith [show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m]
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖u‖)
  have hn : 0 ≤ (2*((m:ℝ)+1))*‖u‖ := by positivity
  nlinarith [norm_nonneg (harmonicDerivative hF m i u)]

lemma norm_harmonicDerivative_le (hF : SphereFischerInner) (m : ℕ) (i : Fin 3) :
    ‖harmonicDerivative hF m i‖ ≤ 2*((m:ℝ)+1) := by
  apply (harmonicDerivative hF m i).opNorm_le_bound (by positivity)
  exact norm_harmonicDerivative_apply_le hF m i

lemma norm_harmonicDerivativeAdjoint_le (hF : SphereFischerInner) (m : ℕ) (i : Fin 3) :
    ‖harmonicDerivativeAdjoint hF m i‖ ≤ 2*((m:ℝ)+1) := by
  rw [harmonicDerivativeAdjoint_eq_adjoint,
    ContinuousLinearMap.adjoint.norm_map]
  exact norm_harmonicDerivative_le hF m i

lemma norm_harmonicDerivativeAdjoint_apply_le (hF : SphereFischerInner) (m : ℕ)
    (i : Fin 3) (u : harmonicSphereSubspace m) :
    ‖harmonicDerivativeAdjoint hF m i u‖ ≤ (2*((m:ℝ)+1))*‖u‖ :=
  (harmonicDerivativeAdjoint hF m i).le_of_opNorm_le
    (norm_harmonicDerivativeAdjoint_le hF m i) u

end OAI.AnisotropicCalderon.HarmonicDerivativeBounds
