import Calderon.RadiusTwoCompactMetricSourceIdentification
import Calderon.RadiusTwoNativeMetricEnergySymmetry

/-! EXPANSION.json precedes transposition against any genuine native zero element. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoCompactTest_energy_transposition
    (g : MatrixField) (hg : IsAdmissibleMetric g) (w : RadiusTwoH1Zero)
    (φ : 𝓓(radiusTwoOpens, ℝ)) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (w : RadiusTwoH1) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
      ∫ z in radiusTwoOpens, (radiusTwoCompactMetricTestDensity g hg φ).1 z *
        TauCeti.W1p.value (w : RadiusTwoH1) z ∂(volume : Measure R3) := by
  have hSource :
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing (radiusTwoCompactMetricTestDensity g hg φ)) : RadiusTwoH1)
        (w : RadiusTwoH1) =
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) (w : RadiusTwoH1) :=
    congrArg (fun u : RadiusTwoH1Zero =>
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (u : RadiusTwoH1) (w : RadiusTwoH1))
      (radiusTwoSourceSolution_compactMetricTest g hg φ)
  calc
    _ = TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) (w : RadiusTwoH1) :=
      radiusTwoMetricEnergy_symm g hg _ _
    _ = TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing (radiusTwoCompactMetricTestDensity g hg φ)) : RadiusTwoH1)
        (w : RadiusTwoH1) := hSource.symm
    _ = _ := radiusTwoSourceSolution_smooth_equation g hg (radiusTwoCompactMetricTestDensity g hg φ) w

end OAI.AnisotropicCalderon.ExteriorSource
