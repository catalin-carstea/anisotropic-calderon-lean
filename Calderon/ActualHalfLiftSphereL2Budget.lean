import Calderon.SphereSobolevHalfWeightedGraphLowering
import Calderon.ActualUniformWeightedBaseBudget
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic WeightedBaseSpectral
attribute [local irreducible] sphereSobolevInclusionL harmonicSphereSubspace

theorem norm_sphereL2_of_same_negative_graph_half_lift
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (W:SphereL2) (v:SphereSobolev (1/2:ℝ))
    (hEq:sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD W)=
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v):
    ‖W‖ ≤ ‖sphereSobolevHalfToSphereL2L hO hD‖*‖v‖ := by
  have hZero:sphereSobolevZeroEquiv hO hD W=
      sphereSobolevZeroEquiv hO hD (sphereSobolevHalfToSphereL2L hO hD v) := by
    apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
    exact hEq.trans (sphereSobolevHalfToSphereL2L_negative_compatibility hO hD v).symm
  have he:W=sphereSobolevHalfToSphereL2L hO hD v := (sphereSobolevZeroEquiv hO hD).injective hZero
  rw [he]
  exact (sphereSobolevHalfToSphereL2L hO hD).le_opNorm v

theorem exists_uniform_referenceBaseLift_bound_of_half_lift_graph_budget
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L B:ℝ):
    ∃ C:ℝ,1 ≤ C ∧ ∀ q∈Icc (0:ℝ) 1,∀ (W:R3→SphereL2) (hW:Continuous W) (hWc:HasCompactSupport W),
      tsupport W⊆closedBall (0:R3) B → ∀ D:ℝ,0 ≤ D →
      (∀ y∈closedBall (0:R3) B,∃ v:SphereSobolev (1/2:ℝ),‖v‖ ≤ D ∧
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (W y))=
        sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v) →
      ‖referenceBaseLift g hg L q W hW hWc‖ ≤ C*D := by
  obtain ⟨A,hA,HA⟩ := exists_uniform_referenceBaseLift_bound_of_supported_pointwise_bound g hg L B
  let T:=sphereSobolevHalfToSphereL2L hO hD
  let C:ℝ := max (A*‖T‖) 1
  refine ⟨C,le_max_right _ _,?_⟩
  intro q hq W hW hWc hSupp D hD0 hGraph
  have hPoint:∀ y∈closedBall (0:R3) B,‖W y‖ ≤ ‖T‖*D := by
    intro y hy
    obtain ⟨v,hv,he⟩ := hGraph y hy
    exact (norm_sphereL2_of_same_negative_graph_half_lift hO hD (W y) v he).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg T))
  exact (HA q hq W hW hWc hSupp (‖T‖*D) (mul_nonneg (norm_nonneg _) hD0) hPoint).trans
    (by rw [← mul_assoc];exact mul_le_mul_of_nonneg_right (le_max_left _ _) hD0)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
