import Calderon.RadiusTwoNativeSourceSolution
import Calderon.RadiusTwoNativeCutoffTestProduct
import TauCeti.Analysis.PDE.DirichletProblem

/-! Full EXPANSION.json precedes finite-source cutoff localization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Distributions Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoSourceSolution_cutoff_test_energy_zero
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : RadiusTwoL2)
    (η : 𝓓(radiusTwoOpens, ℝ))
    {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |η x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient (η : R3 → ℝ) x‖ ≤ M)
    (hVanish : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, η x * f x = 0)
    (φ : 𝓓(radiusTwoOpens, ℝ)) :
    let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 :=
      TauCeti.W1p.contDiffSMulL (η : R3 → ℝ) η.contDiff hM hAbs hGrad
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (radiusTwoSourceSolution g hg f : RadiusTwoH1)
      (S (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1)) = 0 := by
  trace "PROOFENTER finite-source cutoff zero test"
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 :=
    TauCeti.W1p.contDiffSMulL (η : R3 → ℝ) η.contDiff hM hAbs hGrad
  let Φ : 𝓓(radiusTwoOpens, ℝ) := radiusTwoTestProduct η φ
  have hProduct : S (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
      (nativeZeroTestLinear radiusTwoOpens Φ : RadiusTwoH1) :=
    nativeZeroTest_radiusTwoTestProduct η φ hM hAbs hGrad
  have hCompact :=
    ((TauCeti.PDE.isWeakSolutionDirichlet_iff_forall_testFunction
      (memLp_radiusTwoMetricEnergyIntegrand g hg) f (radiusTwoSourceSolution g hg f)).mp
        (radiusTwoSourceSolution_equation g hg f)) Φ
  trace "COMPACT SOURCE EQUATION finite-source cutoff zero test"
  have hIntegral : (∫ x in radiusTwoOpens, f x * Φ x ∂(volume : Measure R3)) = 0 := by
    calc
      _ = ∫ _x in radiusTwoOpens, (0 : ℝ) ∂(volume : Measure R3) := by
        apply integral_congr_ae
        filter_upwards [hVanish] with x hx
        change f x * (η x * φ x) = 0
        calc
          _ = (η x * f x) * φ x := by ring
          _ = 0 := by rw [hx,zero_mul]
      _ = 0 := by simp only [integral_zero]
  change TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
    (radiusTwoSourceSolution g hg f : RadiusTwoH1)
    (S (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1)) = 0
  rw [hProduct]
  calc
    _ = TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (radiusTwoSourceSolution g hg f : RadiusTwoH1)
        (TauCeti.W1p.ofTestFunctionₗ volume radiusTwoOpens 2 Φ) :=
      congrArg (fun v : RadiusTwoH1 => TauCeti.PDE.energyFormH1 (principalCoefficient g)
        (0 : R3 → R3) (0 : R3 → ℝ) (radiusTwoSourceSolution g hg f : RadiusTwoH1) v)
        (nativeZeroTestLinear_coe radiusTwoOpens Φ)
    _ = ∫ x in radiusTwoOpens, f x * Φ x ∂(volume : Measure R3) := hCompact
    _ = 0 := hIntegral

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution_cutoff_test_energy_zero
