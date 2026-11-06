import Calderon.RadiusTwoNativeTestDilation
import TauCeti.Analysis.Sobolev.W1p.Multiplication

/-! EXPANSION.json precedes literal native multiplication of actual compact tests. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal Distributions Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

def radiusTwoTestProduct (η φ : 𝓓(radiusTwoOpens, ℝ)) : 𝓓(radiusTwoOpens, ℝ) := by
  have hSupport : Function.support (fun x : R3 => η x * φ x) ⊆ tsupport (η : R3 → ℝ) := by
    intro x hx
    apply subset_tsupport (η : R3 → ℝ)
    intro hzero
    exact hx (by
      change η x * φ x = 0
      rw [hzero,zero_mul])
  exact ⟨fun x => η x * φ x,η.contDiff.mul φ.contDiff,
    η.hasCompactSupport.mono' hSupport,
    (closure_minimal hSupport (isClosed_tsupport (η : R3 → ℝ))).trans η.tsupport_subset⟩

theorem tsupport_radiusTwoTestProduct_subset_left (η φ : 𝓓(radiusTwoOpens, ℝ)) :
    tsupport (radiusTwoTestProduct η φ : R3 → ℝ) ⊆ tsupport (η : R3 → ℝ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  change η x * φ x ≠ 0 at hx
  apply subset_tsupport (η : R3 → ℝ)
  intro hzero
  exact hx (by rw [hzero,zero_mul])

theorem nativeZeroTest_radiusTwoTestProduct
    (η φ : 𝓓(radiusTwoOpens, ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |η x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient (η : R3 → ℝ) x‖ ≤ M) :
    TauCeti.W1p.contDiffSMulL (η : R3 → ℝ) η.contDiff hM hAbs hGrad
      (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
      (nativeZeroTestLinear radiusTwoOpens (radiusTwoTestProduct η φ) : RadiusTwoH1) := by
  rw [TauCeti.W1p.contDiffSMulL_apply,nativeZeroTestLinear_coe,nativeZeroTestLinear_coe]
  exact TauCeti.W1p.contDiffSMul_ofTestFunctionₗ η.contDiff hM hAbs hGrad φ
    (radiusTwoTestProduct η φ) rfl

end OAI.AnisotropicCalderon.ExteriorSource
