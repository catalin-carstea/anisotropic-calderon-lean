import Calderon.RadiusTwoCommonDeltaCutoffAnnihilation
import Calderon.RadiusTwoSourcePoleCutoffCompletion
import Calderon.RadiusTwoCutoffLimitValueIdentification

/-! Full EXPANSION.json precedes actual convergence retaining the SAME row. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoCommonLimit_zero_cutoff_convergence
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (χ : SmoothData) (hCompact : HasCompactSupport χ.1)
    (M : ℝ) (hM : 0 ≤ M) (hAbs : ∀ x : R3, |χ.1 x| ≤ M)
    (hGrad : ∀ x : R3, ‖gradient χ.1 x‖ ≤ M)
    (hVan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : R3,
      dist ((1/2 : ℝ) • z) q < δ → χ.1 z = 0) :
    let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ.1 χ.2 hM
      (fun x _ => hAbs x) (fun x _ => hGrad x)
    ∃ w : RadiusTwoH1Zero,
      Tendsto (fun n : ℕ => S
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
          ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
            (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
        atTop (𝓝 (w : RadiusTwoH1)) ∧
      (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => χ.1 z * K z) := by
  let ψ (n : ℕ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  let u (n : ℕ) : RadiusTwoH1 :=
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩) : RadiusTwoH1)
  have hAnn := radiusTwoCommonNormalizedDeltaSequence_eventually_annihilated a ha ha1 q hq χ hVan
  obtain ⟨w,hw⟩ := exists_radiusTwoSource_poleCutoff_zero_limit g hg χ.1 χ.2 hCompact M hM hAbs hGrad
    (fun n : ℕ => smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩) hAnn hLimit.cauchySeq
  refine ⟨w,hw,?_⟩
  exact value_radiusTwoCutoff_limit_eq_mul χ hM (fun x _ => hAbs x) (fun x _ => hGrad x)
    u (w : RadiusTwoH1) K hLimit hw

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoCommonLimit_zero_cutoff_convergence
