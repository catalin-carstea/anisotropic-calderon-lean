import Calderon.EnergyBridge
import TauCeti.Analysis.PDE.EnergyForm.Sobolev

noncomputable section
open MeasureTheory
open scoped Distributions ENNReal

namespace OAI.AnisotropicCalderon.EnergyBridge

/-- The exact frozen ball, bundled for the existing Sobolev API. -/
def ballOpens : TopologicalSpace.Opens R3 := ⟨B, Metric.isOpen_ball⟩

@[simp] theorem coe_ballOpens : (ballOpens : Set R3) = B := rfl

/-- The existing embedding of a genuine test function in the exact ball. -/
def testFunctionSobolev (φ : 𝓓(ballOpens, ℝ)) :
    TauCeti.W1p (volume : Measure R3) ballOpens 2 :=
  TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 φ

/-- The test-function subset is a subset of the exact frozen zero-exterior perturbations. -/
theorem testFunction_mem_smoothZeroExterior (φ : 𝓓(ballOpens, ℝ)) :
    (φ : R3 → ℝ) ∈ smoothZeroExterior := by
  refine ⟨φ.contDiff, ?_⟩
  intro x hx
  apply φ.zero_on_compl
  change x ∉ B
  simpa [B, mem_ball_zero_iff] using not_lt.mpr hx

/-- The existing Sobolev jet has the exact frozen classical jet almost everywhere. -/
theorem jetField_testFunctionSobolev_ae (φ : 𝓓(ballOpens, ℝ)) :
    TauCeti.PDE.jetField (testFunctionSobolev φ) =ᵐ[(volume : Measure R3).restrict B]
      energyJet (φ : R3 → ℝ) := by
  have hv := TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ
  have hg := TauCeti.gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ
  filter_upwards [hv, hg] with x hx hy
  simp only [TauCeti.PDE.jetField_apply, testFunctionSobolev,
    TauCeti.W1p.value_ofTestFunctionₗ, TauCeti.W1p.gradient_ofTestFunctionₗ,
    hx, hy, energyJet, energyGradient_eq_gradient]

/-- Test functions genuinely lie in Tau Ceti's closed zero-boundary Sobolev submodule. -/
theorem testFunctionSobolev_mem_w1p0 (φ : 𝓓(ballOpens, ℝ)) :
    testFunctionSobolev φ ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
  TauCeti.W1p.ofTestFunctionₗ_mem_w1p0Submodule φ

/-- A concrete energy-form bridge for the genuine test-function subset. -/
theorem energy_testFunction_eq_energyFormH1 (g : MatrixField) (φ : 𝓓(ballOpens, ℝ)) :
    energy g (φ : R3 → ℝ) = TauCeti.PDE.energyFormH1
      (principalCoefficient g) (fun _ => 0) (fun _ => 0)
      (testFunctionSobolev φ) (testFunctionSobolev φ) := by
  rw [energy_eq_energyFormIntegral]
  unfold TauCeti.PDE.energyFormH1 TauCeti.PDE.energyFormIntegral
  apply integral_congr_ae
  filter_upwards [jetField_testFunctionSobolev_ae φ] with x hx
  rw [hx]

end OAI.AnisotropicCalderon.EnergyBridge

#print axioms OAI.AnisotropicCalderon.EnergyBridge.energy_testFunction_eq_energyFormH1
#print axioms OAI.AnisotropicCalderon.EnergyBridge.testFunctionSobolev_mem_w1p0
