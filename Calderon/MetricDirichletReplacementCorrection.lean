import Calderon.TauBoundaryEnergyData
import Calderon.NativeSmoothBoundaryZeroClosure

/-! EXPANSION.json precedes the literal original-metric correction and energy identities. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def metricDirichletReplacementCorrection
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (f : SmoothData) : BallH1Zero :=
  affineDirichletCorrection g₂ f (memLp_metricEnergyIntegrand g₂ hg₂)
      (isCoercive_metricEnergyForm g₂ hg₂) -
    affineDirichletCorrection g₁ f (memLp_metricEnergyIntegrand g₁ hg₁)
      (isCoercive_metricEnergyForm g₁ hg₁)

lemma metricDirichletReplacementCorrection_coe
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (f : SmoothData) :
    (metricDirichletReplacementCorrection g₁ g₂ hg₁ hg₂ f : BallH1) =
      metricDirichletSolution g₂ hg₂ f - metricDirichletSolution g₁ hg₁ f := by
  let z₁ : BallH1Zero := affineDirichletCorrection g₁ f
    (memLp_metricEnergyIntegrand g₁ hg₁) (isCoercive_metricEnergyForm g₁ hg₁)
  let z₂ : BallH1Zero := affineDirichletCorrection g₂ f
    (memLp_metricEnergyIntegrand g₂ hg₂) (isCoercive_metricEnergyForm g₂ hg₂)
  have h₁ : metricDirichletSolution g₁ hg₁ f = smoothSobolev f + (z₁ : BallH1) := rfl
  have h₂ : metricDirichletSolution g₂ hg₂ f = smoothSobolev f + (z₂ : BallH1) := rfl
  change (z₂ : BallH1) - (z₁ : BallH1) = _
  rw [h₂,h₁]
  abel

lemma metricDirichletSolution_self_energy_eq_of_minimalEnergy_eq
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (f : SmoothData) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g₂) 0 0
      (metricDirichletSolution g₂ hg₂ f) (metricDirichletSolution g₂ hg₂ f) =
    TauCeti.PDE.energyFormH1 (principalCoefficient g₁) 0 0
      (metricDirichletSolution g₁ hg₁ f) (metricDirichletSolution g₁ hg₁ f) := by
  change smoothBoundaryPairing g₂ hg₂ f f = smoothBoundaryPairing g₁ hg₁ f f
  exact (smoothBoundaryPairing_self smoothBoundaryZeroClosure_constructive g₂ hg₂ f).trans
    ((hΛ f.1 f.2).symm.trans
      (smoothBoundaryPairing_self smoothBoundaryZeroClosure_constructive g₁ hg₁ f).symm)

end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.metricDirichletReplacementCorrection
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.metricDirichletReplacementCorrection_coe
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.metricDirichletSolution_self_energy_eq_of_minimalEnergy_eq
