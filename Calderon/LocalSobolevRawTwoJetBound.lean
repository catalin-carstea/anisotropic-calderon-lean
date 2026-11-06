import Calderon.RadiusTwoSmoothSourceJetLinear
import TauCeti.Analysis.Sobolev.Wkp.Classical

/-!
UNADOPTED STANDARD-LITERATURE CANDIDATE; definition only, no inhabitant,
axiom, source-jet endpoint, or change to Main. EXPANSION.json gives the complete
McLean 3.16/3.20/3.26 plus native-graph transport derivation. This draft has not
been compiled. A radius-dependent constant is allowed and is chosen before
both the native Sobolev element and its smooth interior representative.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal ContDiff

namespace OAI.AnisotropicCalderon.ExteriorSource.Literature

/-- A fixed-ball interior raw 2-jet bound for the ACTUAL native order-five norm.
The codomain is the existing nested-product raw jet, with its literal product
and continuous-linear-map norms. No boundary condition or PDE is assumed. -/
def LocalSobolevRawTwoJetBound : Prop :=
  ∀ (p : R3) (r : ℝ), 0 < r →
    let U : Opens R3 := ⟨ball p r, isOpen_ball⟩
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : TauCeti.Wkp (volume : Measure R3) U 2 5) (uSmooth : R3 → ℝ),
        ContDiffOn ℝ ∞ uSmooth (U : Set R3) →
        ((TauCeti.Wkp.value 5 u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict U]
          uSmooth) →
        ‖((uSmooth p,
          (fderiv ℝ uSmooth p,
            fderiv ℝ (fderiv ℝ uSmooth) p)) : RadiusTwoRawTwoJet)‖ ≤ C * ‖u‖

end OAI.AnisotropicCalderon.ExteriorSource.Literature

#print axioms OAI.AnisotropicCalderon.ExteriorSource.Literature.LocalSobolevRawTwoJetBound
