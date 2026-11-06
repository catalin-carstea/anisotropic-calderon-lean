import Calderon.ActualHorizontalSobolevPairing

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
MIXED-HORIZONTAL-PAIRING-EXPANSION-v001.md. Genuine mixed-endpoint horizontal product rule. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SmoothMetricFrame MovingFrameConnection

attribute [local irreducible] referenceHighHorizontalAngularL referenceLowerHorizontalAngularL
  referenceHighHorizontalAction referenceLowerHorizontalAction referenceMetricGramFrame
  sphereSobolevInclusionL sphereSobolevDualPairing

theorem sphereSobolevDualPairing_referenceMixedHorizontalAngular_skew
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3)
    (v : SphereSobolev (1/2 : ℝ)) (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (referenceLowerHorizontalAngularL g L q y i v)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
    -sphereSobolevDualPairing (1/2 : ℝ) v
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighHorizontalAngularL g L q y i u)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hCompatible : J (referenceHighHorizontalAngularL g L q y i u) =
      referenceLowerHorizontalAngularL g L q y i (I u) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A u)
      (referenceHorizontalAngularL_high_lower_compatibility g L q y i)
  exact (sphereSobolevDualPairing_referenceLowerHorizontalAngular_skew g L q y i v (I u)).trans
    (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      -sphereSobolevDualPairing (1/2 : ℝ) v z) hCompatible.symm)

theorem fderiv_referenceMixedHorizontalValuePairing
    (g : MatrixField) (L q : ℝ) (v : R3 → SphereSobolev (1/2 : ℝ))
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hv : DifferentiableAt ℝ v y) (hu : DifferentiableAt ℝ u y) :
    fderiv ℝ (fun x : R3 => sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (v x))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u x))) y
      (referenceMetricGramFrame g L (q,y) i) =
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (referenceLowerHorizontalAction g L q v y i)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y)) +
    sphereSobolevDualPairing (1/2 : ℝ) (v y)
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighHorizontalAction g L q u y i)) := by
  trace "mixed horizontal pairing: proof entered"
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let e := referenceMetricGramFrame g L (q,y) i
  let a : ℝ := ⟪J (fderiv ℝ v y e),I (u y)⟫_ℝ
  let b : ℝ := ⟪v y,J (I (fderiv ℝ u y e))⟫_ℝ
  let c : ℝ := ⟪referenceLowerHorizontalAngularL g L q y i (v y),I (u y)⟫_ℝ
  let d : ℝ := ⟪v y,J (referenceHighHorizontalAngularL g L q y i (u y))⟫_ℝ
  have huI := I.hasFDerivAt.comp y hu.hasFDerivAt
  have hD := fderiv_sphereSobolevHalfValuePairing v (fun x => I (u x)) y e hv huI.differentiableAt
  have huD : fderiv ℝ (fun x => I (u x)) y = I.comp (fderiv ℝ u y) := huI.fderiv
  have hDerivative : fderiv ℝ (fun x : R3 => sphereSobolevDualPairing (-(1/2 : ℝ))
      (J (v x)) (I (u x))) y e = a+b := by
    simpa only [huD, ContinuousLinearMap.comp_apply, sphereSobolevDualPairing] using hD
  trace "mixed horizontal pairing: derivative graph"
  have hSkew : c = -d := by
    have h := sphereSobolevDualPairing_referenceMixedHorizontalAngular_skew g L q y i (v y) (u y)
    simpa only [sphereSobolevDualPairing] using h
  trace "mixed horizontal pairing: angular cancellation"
  have hExpansion : sphereSobolevDualPairing (-(1/2 : ℝ))
      (referenceLowerHorizontalAction g L q v y i) (I (u y)) +
      sphereSobolevDualPairing (1/2 : ℝ) (v y)
        (J (referenceHighHorizontalAction g L q u y i)) = (a+c)+(b+d) := by
    simp only [referenceHighHorizontalAction, referenceLowerHorizontalAction,
      sphereSobolevDualPairing, map_add, inner_add_left, inner_add_right]
    rfl
  trace "mixed horizontal pairing: target expansion"
  have hAlgebra : a+b = (a+c)+(b+d) := by
    rw [hSkew]
    abel
  exact hDerivative.trans (hAlgebra.trans hExpansion.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceMixedHorizontalAngular_skew
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.fderiv_referenceMixedHorizontalValuePairing
