import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes this exact unbundled scalar energy normalization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource

theorem nativePrincipalEnergy_eq_gradient_setIntegral
    (Omega : Opens R3) (A : MatrixField)
    (U V : TauCeti.W1p (volume : Measure R3) Omega 2) :
    TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ) U V =
      ∫ x in Omega, TauCeti.PDE.matrixBilinearForm (A x)
        (TauCeti.W1p.gradient V x) (TauCeti.W1p.gradient U x) ∂(volume : Measure R3) := by
  rw [TauCeti.PDE.energyFormH1_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.jetField_apply,Pi.zero_apply,
      TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,inner_zero_left,
      mul_zero,zero_mul,add_zero])

end OAI.AnisotropicCalderon.ExteriorSource
