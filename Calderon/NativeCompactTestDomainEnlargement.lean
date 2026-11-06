import Calderon.RadiusTwoNativeTestDilation
import TauCeti.Analysis.Sobolev.W1p.Extension

/-! EXPANSION.json precedes genuine actual test-function enlargement and native zero-extension. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma testFunction_monoCLM_coe_of_le (U Omega : Opens R3) (hSub : U ≤ Omega)
    (phi : 𝓓(U, ℝ)) :
    ((TestFunction.monoCLM ℝ phi : 𝓓(Omega, ℝ)) : R3 → ℝ) = (phi : R3 → ℝ) := by
  rw [TestFunction.monoCLM_apply]
  simp [hSub]

lemma nativeZeroTestLinear_extendByZeroL_eq_mono (U Omega : Opens R3) (hSub : U ≤ Omega)
    (phi : 𝓓(U, ℝ)) :
    (TauCeti.W1p0.extendByZeroL hSub (nativeZeroTestLinear U phi) :
      TauCeti.W1p (volume : Measure R3) Omega 2) =
      (nativeZeroTestLinear Omega (TestFunction.monoCLM ℝ phi) :
        TauCeti.W1p (volume : Measure R3) Omega 2) := by
  have hCo := TauCeti.W1p0.coe_extendByZeroL hSub (nativeZeroTestLinear U phi)
  have hJet := TauCeti.Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ
    (mu := (volume : Measure R3)) (p := (2 : ℝ≥0∞)) hSub phi
  apply Subtype.ext
  exact hCo.trans hJet

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.testFunction_monoCLM_coe_of_le
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.nativeZeroTestLinear_extendByZeroL_eq_mono
