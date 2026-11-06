import Calderon.RadiusTwoSourcePoleCutoffGraph
import Calderon.RadiusTwoBoundedSourceOperator

/-! EXPANSION.json precedes the actual cutoff-difference graph estimate. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff Gradient ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoSource_poleCutoff_difference_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ lam Lam : ℝ, 0 < lam ∧ 0 ≤ Lam ∧
      ∀ (χ : R3 → ℝ) (hχ : ContDiff ℝ ∞ χ), HasCompactSupport χ →
      ∀ (M : ℝ) (hM : 0 ≤ M) (hAbs : ∀ x : R3, |χ x| ≤ M)
        (hGrad : ∀ x : R3, ‖gradient χ x‖ ≤ M) (f h : RadiusTwoL2),
      (∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, χ x * f x = 0) →
      (∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, χ x * h x = 0) →
      let T : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ hχ hM
        (fun x _ => hAbs x) (fun x _ => hGrad x)
      ‖T (radiusTwoSourceSolution g hg f : RadiusTwoH1) -
          T (radiusTwoSourceSolution g hg h : RadiusTwoH1)‖ ^ 2 ≤
        M ^ 2 * (3 + 2 * (2 * Lam / lam) ^ 2) *
          ‖TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) -
            TauCeti.W1p.value (radiusTwoSourceSolution g hg h : RadiusTwoH1)‖ ^ 2 := by
  obtain ⟨lam,Lam,hlam,hLam,hGraph⟩ := exists_radiusTwoSource_poleCutoff_graph_bound g hg
  refine ⟨lam,Lam,hlam,hLam,?_⟩
  intro χ hχ hCompact M hM hAbs hGrad f h hf hh
  let T : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ hχ hM
    (fun x _ => hAbs x) (fun x _ => hGrad x)
  have hAnn : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, χ x * (f-h) x = 0 := by
    filter_upwards [hf,hh,Lp.coeFn_sub f h] with x hfx hhx hsub
    change (f-h) x = f x - h x at hsub
    rw [hsub,mul_sub,hfx,hhx,sub_self]
  have hU : (radiusTwoSourceSolution g hg (f-h) : RadiusTwoH1) =
      (radiusTwoSourceSolution g hg f : RadiusTwoH1) -
        (radiusTwoSourceSolution g hg h : RadiusTwoH1) := by
    simpa only [radiusTwoSourceSolutionL_apply,Submodule.coe_sub] using
      congrArg (fun v : RadiusTwoH1Zero => (v : RadiusTwoH1))
        ((radiusTwoSourceSolutionL g hg).map_sub f h)
  have hT : T (radiusTwoSourceSolution g hg (f-h) : RadiusTwoH1) =
      T (radiusTwoSourceSolution g hg f : RadiusTwoH1) -
        T (radiusTwoSourceSolution g hg h : RadiusTwoH1) := by
    exact (congrArg T hU).trans (T.map_sub
      (radiusTwoSourceSolution g hg f : RadiusTwoH1)
      (radiusTwoSourceSolution g hg h : RadiusTwoH1))
  have hValue : TauCeti.W1p.value (radiusTwoSourceSolution g hg (f-h) : RadiusTwoH1) =
      TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) -
        TauCeti.W1p.value (radiusTwoSourceSolution g hg h : RadiusTwoH1) := by
    exact (congrArg (TauCeti.W1p.valueL (mu := (volume : Measure R3))
      (Omega := radiusTwoOpens) (p := 2)) hU).trans
      ((TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := radiusTwoOpens) (p := 2)).map_sub
        (radiusTwoSourceSolution g hg f : RadiusTwoH1)
        (radiusTwoSourceSolution g hg h : RadiusTwoH1))
  have hBound := (hGraph χ hχ hCompact M hM hAbs hGrad (f-h) hAnn).2
  change ‖T (radiusTwoSourceSolution g hg f : RadiusTwoH1) -
      T (radiusTwoSourceSolution g hg h : RadiusTwoH1)‖ ^ 2 ≤ _
  calc
    _ = ‖T (radiusTwoSourceSolution g hg (f-h) : RadiusTwoH1)‖ ^ 2 :=
      (congrArg (fun z : RadiusTwoH1 => ‖z‖ ^ 2) hT).symm
    _ ≤ M ^ 2 * (3 + 2 * (2 * Lam / lam) ^ 2) *
        ‖TauCeti.W1p.value (radiusTwoSourceSolution g hg (f-h) : RadiusTwoH1)‖ ^ 2 := hBound
    _ = _ := congrArg (fun z : RadiusTwoL2 =>
      M ^ 2 * (3 + 2 * (2 * Lam / lam) ^ 2) * ‖z‖ ^ 2) hValue

end OAI.AnisotropicCalderon.ExteriorSource
