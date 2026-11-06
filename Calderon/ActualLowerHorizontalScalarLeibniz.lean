import Calderon.ActualCovariantDensityFirstActions

/-! The actual radius derivative term is retained in the ordered physical operator. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SmoothMetricFrame MovingFrameConnection

attribute [local irreducible] referenceMetricGramFrame referenceLowerHorizontalAngularL
  sphereSobolevInclusionL referenceLowerHorizontalAction

lemma referenceLowerHorizontalAction_smul
    (g : MatrixField) (L q : ℝ) (c : R3 → ℝ)
    (v : R3 → SphereSobolev (1/2 : ℝ)) (y : R3) (i : Fin 3)
    (hc : DifferentiableAt ℝ c y) (hv : DifferentiableAt ℝ v y) :
    referenceLowerHorizontalAction g L q (fun x => c x • v x) y i =
      c y • referenceLowerHorizontalAction g L q v y i +
        fderiv ℝ c y (referenceMetricGramFrame g L (q,y) i) •
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (v y) := by
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let e := referenceMetricGramFrame g L (q,y) i
  let Ω := referenceLowerHorizontalAngularL g L q y i
  have hProduct := congrArg
    (fun A : R3 →L[ℝ] SphereSobolev (1/2 : ℝ) => Iout (A e))
      (hc.hasFDerivAt.smul hv.hasFDerivAt).fderiv
  have hDerivative : Iout (fderiv ℝ (fun x => c x • v x) y e) =
      c y • Iout (fderiv ℝ v y e) + fderiv ℝ c y e • Iout (v y) := by
    simpa only [Pi.smul_def', ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      map_add, map_smul] using hProduct
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b)
    hDerivative (Ω.map_smul (c y) (v y))
  unfold referenceLowerHorizontalAction
  calc
    _ = (c y • Iout (fderiv ℝ v y e) + fderiv ℝ c y e • Iout (v y)) +
        c y • Ω (v y) := hCombined
    _ = _ := by
      simp only [referenceLowerHorizontalAction, Iout, e, Ω, smul_add]
      abel

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerHorizontalAction_smul
