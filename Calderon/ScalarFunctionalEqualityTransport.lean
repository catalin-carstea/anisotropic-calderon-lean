import Mathlib.Data.Real.Basic

/-! EXPANSION.json precedes this scalar equality transport. -/
set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ExteriorSource

lemma scalarFunction_eq_of_pointwise_eq {V : Type*} (J C : V → ℝ)
    (hJC : ∀ w, J w = C w) {u v : V} (hEqual : J v = J u) : C v = C u :=
  (hJC v).symm.trans (hEqual.trans (hJC u))

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.scalarFunction_eq_of_pointwise_eq
