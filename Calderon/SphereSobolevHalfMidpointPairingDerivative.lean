import Calderon.NativeHarmonicHalfCoarseDualPairing
import Calderon.OperatorCurveFixedArgumentDerivative
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevInclusionL
lemma sphereSobolevHalfMidpointPairing_deriv
    (A : ℝ → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (M : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hA : DifferentiableAt ℝ A 0) (hM : DifferentiableAt ℝ M 0)
    (u v : SphereSobolev 1)
    (hPair : ∀ θ : ℝ, sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
      (A θ (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,M θ v⟫_ℝ) :
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
      (deriv A 0 (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,deriv M 0 v⟫_ℝ := by
  let I := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let Z := sphereSobolevInclusionL 1 0 (by norm_num)
  have hEvalHalf := OAI.AnisotropicCalderon.OperatorCurveDerivative.hasDerivAt_clm_fixed_argument_of_differentiableAt
    (X := SphereSobolev (1/2:ℝ)) (Y := SphereSobolev (-(1/2:ℝ)))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hEvalHalf
  have hAe : HasDerivAt (fun θ : ℝ => A θ (I u)) (deriv A 0 (I u)) 0 :=
    hEvalHalf A 0 hA (I u)
  have hEvalMid := OAI.AnisotropicCalderon.OperatorCurveDerivative.hasDerivAt_clm_fixed_argument_of_differentiableAt
    (X := SphereSobolev 1) (Y := SphereSobolev 0)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hEvalMid
  have hMe : HasDerivAt (fun θ : ℝ => M θ v) (deriv M 0 v) 0 :=
    hEvalMid M 0 hM v
  have hLeft : HasDerivAt (fun θ : ℝ => sphereSobolevDualPairing (1/2:ℝ) (I v) (A θ (I u)))
      (sphereSobolevDualPairing (1/2:ℝ) (I v) (deriv A 0 (I u))) 0 := by
    simpa only [sphereSobolevDualPairing,inner_zero_left,add_zero] using
      (hasDerivAt_const (0:ℝ) (I v)).inner ℝ hAe
  have hRight : HasDerivAt (fun θ : ℝ => ⟪Z u,M θ v⟫_ℝ) ⟪Z u,deriv M 0 v⟫_ℝ 0 := by
    simpa only [inner_zero_left,add_zero] using (hasDerivAt_const (0:ℝ) (Z u)).inner ℝ hMe
  have hEq := congrArg (fun f : ℝ → ℝ => deriv f 0) (funext hPair)
  exact hLeft.deriv.symm.trans (hEq.trans hRight.deriv)
end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevHalfMidpointPairing_deriv
