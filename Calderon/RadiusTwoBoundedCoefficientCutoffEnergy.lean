import Calderon.RadiusTwoCutoffEnergyIntegrandCancellation

/-! EXPANSION.json precedes the focused actual arbitrary-coefficient energy cancellation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily.DriftBootstrap
attribute [local irreducible] TauCeti.W1p.contDiffSMulL TauCeti.PDE.energyFormH1

run_cmd Lean.logInfo "BEFORE HEADER actual bounded-coefficient cutoff energy"

theorem radiusTwoBoundedCoefficientEnergy_smoothCutoff_difference
    (A : MatrixField)
    (hcoeff : MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (A x) (0 : R3) (0 : ℝ)) ⊤
      ((volume : Measure R3).restrict radiusTwoOpens))
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient χ x‖ ≤ M)
    (u v : RadiusTwoH1) :
    let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ hχ hM hAbs hGrad
    TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ) (S u) v -
      TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ) u (S v) =
        ∫ x in radiusTwoOpens,
          TauCeti.W1p.value u x * TauCeti.PDE.matrixBilinearForm (A x)
            (TauCeti.W1p.gradient v x) (gradient χ x) -
          TauCeti.W1p.value v x * TauCeti.PDE.matrixBilinearForm (A x)
            (gradient χ x) (TauCeti.W1p.gradient u x) ∂(volume : Measure R3) := by
  trace "PROOFENTER actual bounded-coefficient cutoff energy"
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ hχ hM hAbs hGrad
  have hi1 := TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff (S u) v
  have hi2 := TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff u (S v)
  trace "INTEGRABILITY actual bounded-coefficient cutoff energy"
  change TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ) (S u) v -
    TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ) u (S v) = _
  rw [TauCeti.PDE.energyFormH1_def,TauCeti.PDE.energyFormH1_def]
  simp only [Pi.zero_apply]
  rw [← integral_sub hi1 hi2]
  trace "INTEGRAL REWRITE actual bounded-coefficient cutoff energy"
  apply integral_congr_ae
  exact radiusTwoBoundedCoefficient_cutoff_integrand_difference_ae A χ hχ hM hAbs hGrad u v

end OAI.AnisotropicCalderon.ExteriorSource
