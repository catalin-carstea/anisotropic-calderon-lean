import Mathlib.Analysis.Normed.Operator.Basic

/-! Before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-abstract-scaled-map-three-sum-v005.md. Elementary algebra on abstract vectors. -/
set_option autoImplicit false

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma smul_map_add_add {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (c : ℝ) (d v k : E) :
    c • T ((d+v)+k) = (c • T d+c • T v)+c • T k := by
  rw [T.map_add,T.map_add,smul_add,smul_add]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smul_map_add_add
