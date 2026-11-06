import Calderon.RadiusTwoFiniteSourceCutoffZeroTest
import Calderon.RadiusTwoCutoffSourceEquationOfZeroTest

/-! Full EXPANSION.json precedes identification with the EXISTING source solver. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Distributions Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoSourceSolution_cutoff_eq_sourceSolution
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : RadiusTwoL2)
    (η : 𝓓(radiusTwoOpens, ℝ))
    {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |η x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient (η : R3 → ℝ) x‖ ≤ M)
    (hVanish : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, η x * f x = 0) :
    TauCeti.W1p.contDiffSMulL (η : R3 → ℝ) η.contDiff hM hAbs hGrad
      (radiusTwoSourceSolution g hg f : RadiusTwoH1) =
      (radiusTwoSourceSolution g hg (radiusTwoFixedRowCutoffForcingLp g hg
        ⟨η,η.contDiff⟩ (radiusTwoSourceSolution g hg f : RadiusTwoH1)) : RadiusTwoH1) := by
  trace "PROOFENTER finite-source cutoff existing solver"
  let u : RadiusTwoH1Zero := radiusTwoSourceSolution g hg f
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 :=
    TauCeti.W1p.contDiffSMulL (η : R3 → ℝ) η.contDiff hM hAbs hGrad
  let h : RadiusTwoL2 := radiusTwoFixedRowCutoffForcingLp g hg ⟨η,η.contDiff⟩ (u : RadiusTwoH1)
  have hMem : S (u : RadiusTwoH1) ∈ TauCeti.w1p0Submodule
      (volume : Measure R3) radiusTwoOpens 2 :=
    TauCeti.W1p.contDiffSMul_mem_w1p0Submodule η.contDiff hM hAbs hGrad u.property
  let z : RadiusTwoH1Zero := ⟨S (u : RadiusTwoH1),hMem⟩
  have hWeak : TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) h z := by
    apply (TauCeti.PDE.isWeakSolutionDirichlet_iff_forall_testFunction
      (memLp_radiusTwoMetricEnergyIntegrand g hg) h z).mpr
    intro φ
    have hZero := radiusTwoSourceSolution_cutoff_test_energy_zero
      g hg f η hM hAbs hGrad hVanish φ
    have hCompact := radiusTwoMetric_cutoff_sourceEquation_of_zero_test
      g hg ⟨η,η.contDiff⟩ hM hAbs hGrad (u : RadiusTwoH1) φ hZero
    change TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (S (u : RadiusTwoH1)) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
      ∫ x in radiusTwoOpens, h x * φ x ∂(volume : Measure R3) at hCompact
    have hNative :
        TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
          (S (u : RadiusTwoH1)) (TauCeti.W1p.ofTestFunctionₗ volume radiusTwoOpens 2 φ) =
        TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
          (S (u : RadiusTwoH1)) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) :=
      congrArg (fun v : RadiusTwoH1 => TauCeti.PDE.energyFormH1 (principalCoefficient g)
        (0 : R3 → R3) (0 : R3 → ℝ) (S (u : RadiusTwoH1)) v)
        (nativeZeroTestLinear_coe radiusTwoOpens φ).symm
    exact hNative.trans hCompact
  trace "NATIVE WEAK EQUATION finite-source cutoff existing solver"
  have hIdentity : z = radiusTwoSourceSolution g hg h := eq_radiusTwoSourceSolution g hg h z hWeak
  exact congrArg (fun v : RadiusTwoH1Zero => (v : RadiusTwoH1)) hIdentity

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution_cutoff_eq_sourceSolution
