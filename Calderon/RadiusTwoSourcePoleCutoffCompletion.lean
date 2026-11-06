import Calderon.RadiusTwoSourcePoleCutoffCauchy
import Calderon.RadiusTwoNativeZeroSequenceCompletion

/-! EXPANSION.json distinguishes this genuine conditional completion auxiliary
from the separate actual smooth-delta discharge. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ContDiff Gradient ENNReal InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoSource_poleCutoff_zero_limit
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hCompact : HasCompactSupport χ)
    (M : ℝ) (hM : 0 ≤ M) (hAbs : ∀ x : R3, |χ x| ≤ M)
    (hGrad : ∀ x : R3, ‖gradient χ x‖ ≤ M) (ρ : ℕ → RadiusTwoL2)
    (hAnn : ∀ᶠ n in atTop, ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      χ x * ρ n x = 0)
    (hValue : CauchySeq (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1))) :
    let T : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ hχ hM
      (fun x _ => hAbs x) (fun x _ => hGrad x)
    ∃ w : RadiusTwoH1Zero, Tendsto (fun n : ℕ =>
      T (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1)) atTop (𝓝 (w : RadiusTwoH1)) := by
  trace "PROOFENTER original radius-two cutoff completion caller"
  let T : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ hχ hM
    (fun x _ => hAbs x) (fun x _ => hGrad x)
  have hCauchy : CauchySeq (fun n : ℕ => T
      (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1)) :=
    cauchySeq_radiusTwoSource_poleCutoff g hg χ hχ hCompact M hM hAbs hGrad ρ hAnn hValue
  apply exists_radiusTwoNativeZero_sequence_limit
    (fun n : ℕ => T (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1)) hCauchy
  intro n
  exact TauCeti.W1p.contDiffSMul_mem_w1p0Submodule hχ hM
    (fun x _ => hAbs x) (fun x _ => hGrad x) (radiusTwoSourceSolution g hg (ρ n)).property

end OAI.AnisotropicCalderon.ExteriorSource
