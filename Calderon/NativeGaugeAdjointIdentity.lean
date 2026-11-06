import Calderon.ActualReferenceLowerBoundaryTranspose
import Calderon.SphereSobolevDualOrthogonalPullback

/-! Full upfront: actual-gradient-drift-author-oct15-v001/
EXPANSION-native-gauge-adjoint-algebra-v009.md. Conditional native pivot algebra;
actual coefficient/solution graphs remain separately proved obligations. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

variable (A T N : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
  (M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
  (Mn : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
  (hM : ∀ u : SphereSobolev (1/2 : ℝ), ∀ v : SphereSobolev (-(1/2 : ℝ)),
    sphereSobolevDualPairing (1/2 : ℝ) (M u) v = sphereSobolevDualPairing (1/2 : ℝ) u (Mn v))
  (hN : N = Mn.comp A+T)
  (hSym : ∀ f z : SphereSobolev (1/2 : ℝ),
    sphereSobolevDualPairing (1/2 : ℝ) z (N f) = sphereSobolevDualPairing (1/2 : ℝ) f (N z))

attribute [local irreducible] sphereLowerDistributionalTranspose

include hM hN hSym

lemma lower_distributionalTranspose_mul_eq_of_symmetric_weighted_operator :
    (sphereLowerDistributionalTranspose A).comp M = Mn.comp A+T-sphereLowerDistributionalTranspose T := by
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro z
  have hAt := sphereSobolevDualPairing_lower_distributionalTranspose A z (M f)
  have hTt := sphereSobolevDualPairing_lower_distributionalTranspose T z f
  have hNz := congrArg (fun R : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => R z) hN
  have hNf := congrArg (fun R : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => R f) hN
  have hz := congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => sphereSobolevDualPairing (1/2 : ℝ) f v) hNz
  have hf := congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => sphereSobolevDualPairing (1/2 : ℝ) z v) hNf
  have hMm := hM f (A z)
  have hSN := hSym f z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    sphereSobolevDualPairing, inner_add_right] at hz hf
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, sphereSobolevDualPairing, inner_add_right, inner_sub_right]
  simp only [sphereSobolevDualPairing] at hAt hTt hMm hSN
  linarith

lemma lower_distributionalTranspose_sub_eq_of_right_inverse
    (W : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (hInv : M.comp W = ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ))) :
    sphereLowerDistributionalTranspose A-A =
      (Mn.comp A-A.comp M+T-sphereLowerDistributionalTranspose T).comp W := by
  have hRel := lower_distributionalTranspose_mul_eq_of_symmetric_weighted_operator A T N M Mn hM hN hSym
  apply ContinuousLinearMap.ext
  intro f
  have hi : M (W f) = f := congrArg
    (fun R : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => R f) hInv
  have hr := congrArg
    (fun R : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => R (W f)) hRel
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply] at hr ⊢
  have hr' : sphereLowerDistributionalTranspose A f =
      Mn (A (W f))+T (W f)-sphereLowerDistributionalTranspose T (W f) :=
    (congrArg (sphereLowerDistributionalTranspose A) hi).symm.trans hr
  have hLeft := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => z-A f) hr'
  have hRight := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
    Mn (A (W f))-z+T (W f)-sphereLowerDistributionalTranspose T (W f)) (congrArg A hi)
  have hGroup : (Mn (A (W f))+T (W f)-sphereLowerDistributionalTranspose T (W f))-A f =
      Mn (A (W f))-A f+T (W f)-sphereLowerDistributionalTranspose T (W f) := by abel
  exact hLeft.trans (hGroup.trans hRight.symm)

lemma lower_distributionalTranspose_sub_eq_of_native_commutator
    (W : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (hInv : M.comp W = ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)))
    (J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (B : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (hB : J.comp B=A.comp M-Mn.comp A) :
    sphereLowerDistributionalTranspose A-A =
      (-(J.comp B)+T-sphereLowerDistributionalTranspose T).comp W := by
  have hNeg : Mn.comp A-A.comp M = -(J.comp B) := by rw [hB]; abel
  exact (lower_distributionalTranspose_sub_eq_of_right_inverse A T N M Mn hM hN hSym W hInv).trans
    (congrArg (fun R : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      (R+T-sphereLowerDistributionalTranspose T).comp W) hNeg)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.lower_distributionalTranspose_mul_eq_of_symmetric_weighted_operator
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.lower_distributionalTranspose_sub_eq_of_right_inverse
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.lower_distributionalTranspose_sub_eq_of_native_commutator
