import Calderon.SphereDerivativeAdjoint
import Calderon.SphereRotationCore

/-! Exact polynomial block algebra for the genuine native angular transpose. -/
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial HarmonicCoordinateCompatibility SphereDerivativeAdjoint

lemma sum_polynomialRotation_pderiv_harmonic
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k)
    (i : Fin 3) :
    (∑ j : Fin 3, polynomialRotation j i (pderiv j p)) =
      C ((k : ℝ)-1) * pderiv i p := by
  cases k with
  | zero =>
    rw [eq_C_of_harmonicHomogeneous_zero p hp]
    simp only [pderiv_C,polynomialRotation,map_zero,mul_zero,sub_self,
      Finset.sum_const_zero]
  | succ m =>
    have he : (∑ j : Fin 3, X j * pderiv j (pderiv i p)) =
        C (m : ℝ) * pderiv i p := by
      simpa only [Nat.add_sub_cancel,nsmul_eq_mul,map_natCast] using
        (hp.1.pderiv (i := i)).sum_X_mul_pderiv
    have hLap : (∑ j : Fin 3, pderiv j (pderiv j p)) = 0 := hp.2
    have hForm : (∑ j : Fin 3, polynomialRotation j i (pderiv j p)) =
        (∑ j : Fin 3, X j * pderiv j (pderiv i p)) -
          X i * (∑ j : Fin 3, pderiv j (pderiv j p)) := by
      simp only [polynomialRotation,Finset.sum_sub_distrib,Finset.mul_sum]
      apply congrArg₂ (fun a b : MvPolynomial (Fin 3) ℝ => a-b) ?_ rfl
      apply Finset.sum_congr rfl
      intro j hj
      rw [pderiv_pderiv_comm i j]
    rw [hForm,he,hLap,mul_zero,sub_zero]
    congr 2
    push_cast
    ring

lemma sum_polynomialRotation_coordinateHarmonicRaising
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k)
    (i : Fin 3) :
    (∑ j : Fin 3, polynomialRotation j i (coordinateHarmonicRaising k j p)) =
      -C ((k : ℝ)+2) * coordinateHarmonicRaising k i p := by
  have he : (∑ j : Fin 3, X j * pderiv j p) = C (k : ℝ) * p := by
    simpa only [nsmul_eq_mul,map_natCast] using hp.1.sum_X_mul_pderiv
  have hX : (∑ j : Fin 3, polynomialRotation j i (X j*p)) =
      radiusSq * pderiv i p - C ((k : ℝ)+2) * (X i*p) := by
    simp only [Fin.sum_univ_three,map_natCast] at he
    fin_cases i
    · simp [polynomialRotation,Fin.sum_univ_three,pderiv_mul,pderiv_X,radiusSq,map_natCast,map_ofNat]
      linear_combination -(X (0 : Fin 3))*he
    · simp [polynomialRotation,Fin.sum_univ_three,pderiv_mul,pderiv_X,radiusSq,map_natCast,map_ofNat]
      linear_combination -(X (1 : Fin 3))*he
    · simp [polynomialRotation,Fin.sum_univ_three,pderiv_mul,pderiv_X,radiusSq,map_natCast,map_ofNat]
      linear_combination -(X (2 : Fin 3))*he
  have hSplit : (∑ j : Fin 3, polynomialRotation j i (coordinateHarmonicRaising k j p)) =
      (∑ j : Fin 3, polynomialRotation j i (X j*p)) -
        C ((2*(k : ℝ)+1)⁻¹) * radiusSq *
          (∑ j : Fin 3, polynomialRotation j i (pderiv j p)) := by
    simp only [coordinateHarmonicRaising,polynomialRotation,Fin.sum_univ_three,
      map_sub,pderiv_mul,pderiv_C,pderiv_radiusSq,zero_mul,zero_add]
    ring
  have hn : (2*(k : ℝ)+1) ≠ 0 := by positivity
  have hc : C ((2*(k : ℝ)+1)⁻¹) * C (2*(k : ℝ)+1) =
      (1 : MvPolynomial (Fin 3) ℝ) := by
    rw [← map_mul,inv_mul_cancel₀ hn,map_one]
  rw [hSplit,hX,sum_polynomialRotation_pderiv_harmonic k p hp i]
  simp only [coordinateHarmonicRaising,map_add,map_sub,map_mul,map_ofNat,map_natCast,map_one] at hc ⊢
  linear_combination -(radiusSq * pderiv i p)*hc

lemma neg_sum_polynomialRotation_coordinateHarmonicRaising_add_degree
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k)
    (i : Fin 3) :
    -(∑ j : Fin 3, polynomialRotation j i (coordinateHarmonicRaising k j p)) +
      C ((k : ℝ)+1) * coordinateHarmonicRaising k i p =
        sphereDerivativeAdjoint k i p := by
  rw [sum_polynomialRotation_coordinateHarmonicRaising k p hp i]
  unfold sphereDerivativeAdjoint
  simp only [map_add,map_mul,map_ofNat,map_natCast,map_one]
  ring

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sum_polynomialRotation_pderiv_harmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sum_polynomialRotation_coordinateHarmonicRaising
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.neg_sum_polynomialRotation_coordinateHarmonicRaising_add_degree
