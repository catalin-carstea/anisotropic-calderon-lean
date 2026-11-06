import Calderon.SphereSobolevInclusion
import Mathlib.Topology.Algebra.Support

/-! Full before-source: actual-physical-full-allocation-author-oct16-v001/
EXPANSION-bundled-linear-section-support-v036.md. Actual bundled linear maps preserve input support. -/
set_option autoImplicit false
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma tsupport_clm_comp_apply_subset
    {X E F G : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : F →L[ℝ] G) (T : X → E →L[ℝ] F) (U : X → E) :
    tsupport (fun x => S (T x (U x))) ⊆ tsupport U := by
  apply closure_minimal ?_ (isClosed_tsupport U)
  intro x hx
  by_contra hOutside
  have hU0 : U x = 0 := image_eq_zero_of_notMem_tsupport hOutside
  have hCompositeZero : S (T x (U x)) = 0 := by
    simp only [hU0,map_zero]
  exact hx hCompositeZero

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
