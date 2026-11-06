import Calderon.RadiusTwoSmoothValueMultiplier

/-! EXPANSION.json separates this genuine limit-algebra auxiliary from actual
source-family convergence discharge. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Gradient InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem value_radiusTwoCutoff_limit_eq_mul
    (χ : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ.1 x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient χ.1 x‖ ≤ M)
    (u : ℕ → RadiusTwoH1) (w : RadiusTwoH1) (K : RadiusTwoL2)
    (hValues : Tendsto (fun n : ℕ => TauCeti.W1p.value (u n)) atTop (𝓝 K))
    (hCutoff : Tendsto (fun n : ℕ => TauCeti.W1p.contDiffSMulL χ.1 χ.2 hM hAbs hGrad (u n))
      atTop (𝓝 w)) :
    (TauCeti.W1p.value w : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      (fun x : R3 => χ.1 x * K x) := by
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ.1 χ.2 hM hAbs hGrad
  let R : RadiusTwoL2 →L[ℝ] RadiusTwoL2 := radiusTwoSmoothValueMultiplierL χ hM hAbs
  have hNative : Tendsto (fun n : ℕ => TauCeti.W1p.value (S (u n)))
      atTop (𝓝 (TauCeti.W1p.value w)) := by
    have h := ((TauCeti.W1p.valueL (mu := (volume : Measure R3))
      (Omega := radiusTwoOpens) (p := 2)).continuous.tendsto w).comp hCutoff
    simpa only [S,Function.comp_def,TauCeti.W1p.valueL_apply] using h
  have hProduct : Tendsto (fun n : ℕ => R (TauCeti.W1p.value (u n))) atTop (𝓝 (R K)) := by
    simpa only [Function.comp_def] using (R.continuous.tendsto K).comp hValues
  have hSequence : (fun n : ℕ => TauCeti.W1p.value (S (u n))) =
      (fun n : ℕ => R (TauCeti.W1p.value (u n))) :=
    funext (fun n => value_contDiffSMulL_eq_radiusTwoSmoothValueMultiplier χ hM hAbs hGrad (u n))
  rw [hSequence] at hNative
  have hEq : TauCeti.W1p.value w = R K := tendsto_nhds_unique hNative hProduct
  rw [hEq]
  exact radiusTwoSmoothValueMultiplierL_apply_ae χ hM hAbs K

end OAI.AnisotropicCalderon.ExteriorSource
