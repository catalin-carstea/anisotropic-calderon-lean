import Calderon.RadiusTwoSourcePoleCutoffDifference
import Calderon.CauchySequenceSquaredDifferenceTransport

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ContDiff Gradient ENNReal InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem cauchySeq_radiusTwoSource_poleCutoff
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
    CauchySeq (fun n : ℕ => T (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1)) := by
  trace "PROOFENTER actual radius-two cutoff Cauchy"
  let T : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ hχ hM
    (fun x _ => hAbs x) (fun x _ => hGrad x)
  let u (n : ℕ) : RadiusTwoH1 := (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1)
  obtain ⟨lam,Lam,hlam,hLam,hDifference⟩ :=
    exists_radiusTwoSource_poleCutoff_difference_bound g hg
  let C : ℝ := M ^ 2 * (3 + 2 * (2 * Lam / lam) ^ 2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 < C+1 := by linarith
  obtain ⟨N0,hN0⟩ := eventually_atTop.1 hAnn
  have hCauchy : CauchySeq (fun n : ℕ => T (u n)) := by
    apply cauchySeq_of_eventual_sq_norm_sub_le_mul
      (fun n : ℕ => T (u n)) (fun n : ℕ => TauCeti.W1p.value (u n)) C hC N0 hValue
    intro m hm n hn
    exact hDifference χ hχ hCompact M hM hAbs hGrad (ρ m) (ρ n) (hN0 m hm) (hN0 n hn)
  trace "PROOFEND actual radius-two cutoff Cauchy"
  exact hCauchy

end OAI.AnisotropicCalderon.ExteriorSource
