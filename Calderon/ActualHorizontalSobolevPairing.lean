import Calderon.ActualHorizontalSobolevConnection
import Calderon.SphereSobolevHalfDualRotationPairing
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
HORIZONTAL-PAIRING-EXPANSION-v001.md. Genuine native mixed-endpoint value pairing. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

theorem sphereSobolevDualPairing_half_value_inclusion_transfer
    (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u) v =
    sphereSobolevDualPairing (1/2 : ℝ) u
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v) := by
  rw [sphereSobolevDualPairing_eq_tsum, sphereSobolevDualPairing_eq_tsum]
  apply tsum_congr
  intro k
  simp only [sphereSobolevCoefficientL_inclusion]
  have hIndex (a b : ℝ) (hab : a = b) :
      (sphereSobolevCoefficientL a k : SphereSobolev (1/2 : ℝ) →L[ℝ] harmonicSphereSubspace k) =
      (sphereSobolevCoefficientL b k : SphereSobolev (1/2 : ℝ) →L[ℝ] harmonicSphereSubspace k) := by
    cases hab
    rfl
  exact congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] harmonicSphereSubspace k =>
    ⟪sphereSobolevCoefficientL (1/2 : ℝ) k u,T v⟫_ℝ)
    (hIndex (-(-(1/2 : ℝ))) (1/2 : ℝ) (neg_neg _))

theorem fderiv_sphereSobolevHalfValuePairing
    (v u : R3 → SphereSobolev (1/2 : ℝ)) (y X : R3)
    (hv : DifferentiableAt ℝ v y) (hu : DifferentiableAt ℝ u y) :
    fderiv ℝ (fun x => sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (v x)) (u x)) y X =
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (fderiv ℝ v y X)) (u y) +
    sphereSobolevDualPairing (1/2 : ℝ) (v y)
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (fderiv ℝ u y X)) := by
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hJ := J.hasFDerivAt.comp y hv.hasFDerivAt
  have hD := fderiv_inner_apply ℝ hJ.differentiableAt hu X
  have hDerivative : fderiv ℝ (fun x => J (v x)) y = J.comp (fderiv ℝ v y) := hJ.fderiv
  have hD' : fderiv ℝ (fun x => ⟪J (v x),u x⟫_ℝ) y X =
      ⟪J (v y),fderiv ℝ u y X⟫_ℝ + ⟪J (fderiv ℝ v y X),u y⟫_ℝ := by
    simpa only [Function.comp_def, hDerivative, ContinuousLinearMap.comp_apply] using hD
  have hTransfer := sphereSobolevDualPairing_half_value_inclusion_transfer
    (v y) (fderiv ℝ u y X)
  change ⟪J (v y),fderiv ℝ u y X⟫_ℝ = ⟪v y,J (fderiv ℝ u y X)⟫_ℝ at hTransfer
  change fderiv ℝ (fun x => ⟪J (v x),u x⟫_ℝ) y X =
    ⟪J (fderiv ℝ v y X),u y⟫_ℝ + ⟪v y,J (fderiv ℝ u y X)⟫_ℝ
  exact hD'.trans ((congrArg (fun z : ℝ => z + ⟪J (fderiv ℝ v y X),u y⟫_ℝ)
    hTransfer).trans (add_comm _ _))

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SmoothMetricFrame MovingFrameConnection

theorem sphereSobolevDualPairing_referenceLowerHorizontalAngular_skew
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3)
    (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (referenceLowerHorizontalAngularL g L q y i u) v =
    -sphereSobolevDualPairing (1/2 : ℝ) u
      (referenceLowerHorizontalAngularL g L q y i v) := by
  have hSkew (a b : Fin 3) :
      ⟪sphereSobolevRotationL (1/2 : ℝ) a b u,v⟫_ℝ =
      -⟪u,sphereSobolevRotationL (1/2 : ℝ) a b v⟫_ℝ :=
    sphereSobolevDualPairing_half_rotation_skew a b u v
  simp only [referenceLowerHorizontalAngularL, sphereSobolevDualPairing,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    hSkew, mul_neg, Finset.sum_neg_distrib]

attribute [local irreducible] referenceHighHorizontalAngularL referenceLowerHorizontalAngularL

theorem sphereSobolevDualPairing_referenceHighHorizontalAngular_skew
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3)
    (u v : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighHorizontalAngularL g L q y i u))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v) =
    -sphereSobolevDualPairing (1/2 : ℝ)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighHorizontalAngularL g L q y i v)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hCompatible (a : SphereSobolev (3/2 : ℝ)) :
      J (referenceHighHorizontalAngularL g L q y i a) =
      referenceLowerHorizontalAngularL g L q y i (I a) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A a)
      (referenceHorizontalAngularL_high_lower_compatibility g L q y i)
  calc
    _ = sphereSobolevDualPairing (-(1/2 : ℝ))
        (referenceLowerHorizontalAngularL g L q y i (I u)) (I v) :=
      congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
        sphereSobolevDualPairing (-(1/2 : ℝ)) z (I v)) (hCompatible u)
    _ = -sphereSobolevDualPairing (1/2 : ℝ) (I u)
        (referenceLowerHorizontalAngularL g L q y i (I v)) :=
      sphereSobolevDualPairing_referenceLowerHorizontalAngular_skew g L q y i (I u) (I v)
    _ = _ := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      -sphereSobolevDualPairing (1/2 : ℝ) (I u) z) (hCompatible v).symm

attribute [local irreducible] referenceHighHorizontalAction referenceMetricGramFrame
  sphereSobolevInclusionL sphereSobolevDualPairing

theorem fderiv_referenceHighHorizontalValuePairing
    (g : MatrixField) (L q : ℝ) (v u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i : Fin 3) (hv : DifferentiableAt ℝ v y) (hu : DifferentiableAt ℝ u y) :
    fderiv ℝ (fun x : R3 => sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (v x)))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u x))) y
      (referenceMetricGramFrame g L (q,y) i) =
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighHorizontalAction g L q v y i))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y)) +
    sphereSobolevDualPairing (1/2 : ℝ)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (v y))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighHorizontalAction g L q u y i)) := by
  trace "high horizontal pairing: proof entered"
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let e := referenceMetricGramFrame g L (q,y) i
  let a : ℝ := ⟪J (I (fderiv ℝ v y e)),I (u y)⟫_ℝ
  let b : ℝ := ⟪I (v y),J (I (fderiv ℝ u y e))⟫_ℝ
  let c : ℝ := ⟪J (referenceHighHorizontalAngularL g L q y i (v y)),I (u y)⟫_ℝ
  let d : ℝ := ⟪I (v y),J (referenceHighHorizontalAngularL g L q y i (u y))⟫_ℝ
  have hvI := I.hasFDerivAt.comp y hv.hasFDerivAt
  have huI := I.hasFDerivAt.comp y hu.hasFDerivAt
  have hD := fderiv_sphereSobolevHalfValuePairing
    (fun x => I (v x)) (fun x => I (u x)) y e hvI.differentiableAt huI.differentiableAt
  have hvD : fderiv ℝ (fun x => I (v x)) y = I.comp (fderiv ℝ v y) := hvI.fderiv
  have huD : fderiv ℝ (fun x => I (u x)) y = I.comp (fderiv ℝ u y) := huI.fderiv
  have hDerivative : fderiv ℝ (fun x : R3 => sphereSobolevDualPairing (-(1/2 : ℝ))
      (J (I (v x))) (I (u x))) y e = a+b := by
    simpa only [hvD, huD, ContinuousLinearMap.comp_apply, sphereSobolevDualPairing] using hD
  trace "high horizontal pairing: derivative graph"
  have hSkew : c = -d := by
    have h := sphereSobolevDualPairing_referenceHighHorizontalAngular_skew g L q y i (v y) (u y)
    simpa only [sphereSobolevDualPairing] using h
  trace "high horizontal pairing: angular cancellation"
  have hExpansion : sphereSobolevDualPairing (-(1/2 : ℝ))
      (J (referenceHighHorizontalAction g L q v y i)) (I (u y)) +
      sphereSobolevDualPairing (1/2 : ℝ) (I (v y))
        (J (referenceHighHorizontalAction g L q u y i)) = (a+c)+(b+d) := by
    simp only [referenceHighHorizontalAction, sphereSobolevDualPairing,
      map_add, inner_add_left, inner_add_right]
    rfl
  trace "high horizontal pairing: target expansion"
  have hAlgebra : a+b = (a+c)+(b+d) := by
    rw [hSkew]
    abel
  exact hDerivative.trans (hAlgebra.trans hExpansion.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_half_value_inclusion_transfer
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.fderiv_sphereSobolevHalfValuePairing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceLowerHorizontalAngular_skew
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceHighHorizontalAngular_skew
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.fderiv_referenceHighHorizontalValuePairing
