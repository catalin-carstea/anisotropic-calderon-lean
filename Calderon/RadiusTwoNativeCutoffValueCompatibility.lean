import Calderon.RadiusTwoNativeSourceFoundation
import TauCeti.Analysis.Sobolev.W1p.Multiplication

/-! EXPANSION.json precedes actual native cutoff value injectivity. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoNativeCutoff_eq_of_same_value
    (K : RadiusTwoL2) (η : SmoothData) (χ : R3 → ℝ)
    (v w : RadiusTwoH1Zero)
    (hV : (TauCeti.W1p.value (v : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => η.1 z * K z))
    (hW : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => χ z * K z))
    (hOne : ∀ z ∈ tsupport η.1, χ z = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |η.1 x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient η.1 x‖ ≤ M) :
    TauCeti.W1p.contDiffSMulL η.1 η.2 hM hAbs hGrad (w : RadiusTwoH1) =
      (v : RadiusTwoH1) := by
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  have hMul := TauCeti.W1p.value_contDiffSMul_ae η.2 hM hAbs hGrad (w : RadiusTwoH1)
  filter_upwards [hMul,hV,hW] with z hMul hVz hWz
  change TauCeti.W1p.value (TauCeti.W1p.contDiffSMul η.1 η.2 hM hAbs hGrad
    (w : RadiusTwoH1)) z = TauCeti.W1p.value (v : RadiusTwoH1) z
  rw [hMul,hVz,hWz]
  simp only [smul_eq_mul]
  by_cases hz : η.1 z = 0
  · rw [hz,zero_mul,zero_mul]
  · rw [hOne z (subset_tsupport η.1 hz),one_mul]

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNativeCutoff_eq_of_same_value
