import Calderon.ActualMixedKernelSameGlobalFiveHalfDensity

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic

attribute [local irreducible] sphereSobolevInclusionL

lemma sphereSobolevInclusionL_sameCutoff_fiveHalf_field
    (chi : R3 → ℝ) (hchiSupp : tsupport chi ⊆ interior cylinder)
    (Psi5 : R3 → SphereSobolev (5/2 : ℝ))
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hInc : ∀ y ∈ cylinder,
      sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y) = Psi y) :
    (fun y => sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (chi y • Psi5 y)) =
      (fun y => chi y • Psi y) := by
  have h := smul_sphereSobolevInclusionL_same_global_native_mixed_kernel_fiveHalf_density
    chi Psi Psi5 hchiSupp hInc
  funext y
  rw [map_smul]
  exact congrFun h y

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
