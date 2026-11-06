import Calderon.NativePrincipalEnergyGradientForm
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Full EXPANSION.json precedes this native/classical gradient uniqueness helper. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal ContDiff InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource

theorem native_gradient_ae_eq_gradient_of_contDiffOn_value
    (Omega OmegaOuter : Opens R3) (hSub : Omega ≤ OmegaOuter)
    (u : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) (G : R3 → ℝ)
    (hG : ContDiffOn ℝ ∞ G (Omega : Set R3))
    (hValue : (TauCeti.W1p.value u : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict Omega] G) :
    (TauCeti.W1p.gradient u : R3 → R3)
      =ᵐ[(volume : Measure R3).restrict Omega] gradient G := by
  have hWeak : TauCeti.HasWeakFDerivOn (volume : Measure R3) Omega G
      (fun x => innerSL ℝ (TauCeti.W1p.gradient u x)) :=
    ((TauCeti.W1p.hasWeakFDerivOn u).mono hSub).congr_ae hValue
  have hDcont : ContinuousOn (fderiv ℝ G) (Omega : Set R3) :=
    hG.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)
  have hClassical : (fun x => innerSL ℝ (TauCeti.W1p.gradient u x))
      =ᵐ[(volume : Measure R3).restrict Omega] fderiv ℝ G :=
    hWeak.ae_eq_fderiv (hDcont.locallyIntegrableOn Omega.isOpen.measurableSet)
      (fun x hx => (hG.contDiffAt (Omega.isOpen.mem_nhds hx)).differentiableAt (by simp))
  filter_upwards [hClassical] with x hx
  apply (InnerProductSpace.toDual ℝ R3).injective
  change innerSL ℝ (TauCeti.W1p.gradient u x) =
    InnerProductSpace.toDual ℝ R3 (gradient G x)
  exact hx.trans (toDual_gradient (𝕜 := ℝ) (F := R3) (f := G) (x := x)).symm

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.native_gradient_ae_eq_gradient_of_contDiffOn_value
