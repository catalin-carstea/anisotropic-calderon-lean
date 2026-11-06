import Calderon.RadiusTwoNormalizedH2SourceOperator
import Calderon.NativeH2PointEvaluation

/-! EXPANSION.json precedes this derived interior L2 Riesz row.
It does not assert a classical Green kernel or zero boundary at the pole. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local irreducible] TauCeti.sobolevStage radiusTwoSourceSolution radiusTwoNativeZeroDilation

theorem exists_radiusTwoInteriorRieszSourceRow
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a) :
    ∃ K : RadiusTwoL2, ∀ (f : RadiusTwoL2) (U : BallSobolev 2),
      TauCeti.Wkp.firstOrder 1 U =
        (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) : BallH1) →
      ∀ F : R3 → ℝ, Continuous F →
        (∀ᵐ y ∂(volume : Measure R3).restrict ballOpens, y ∈ closedBall (0 : R3) a →
          F y = TauCeti.Wkp.value 2 U y) →
        (∫ y in radiusTwoOpens, K y * f y ∂(volume : Measure R3)) = F q := by
  let P : (BallSobolev 2 →L[ℝ] ℝ) → Prop := fun L =>
    ∀ (U : BallSobolev 2) (F : R3 → ℝ), Continuous F →
      (∀ᵐ y ∂(volume : Measure R3).restrict ballOpens, y ∈ closedBall (0 : R3) a →
        F y = TauCeti.Wkp.value 2 U y) → L U = F q
  have hPoint : ∃ L : BallSobolev 2 →L[ℝ] ℝ, P L :=
    exists_nativeH2_innerPointEvaluation hcalc a ha ha1 q hq
  trace "RIESZ POINT FUNCTIONAL TYPED"
  refine Exists.elim hPoint ?_
  intro L hL
  trace "RIESZ POINT FUNCTIONAL ELIMINATED"
  obtain ⟨R,hR⟩ := exists_radiusTwoNormalizedH2SourceOperator hreg g hg
  trace "RIESZ ACTUAL H2 SOURCE OPERATOR OBTAINED"
  let ell : StrongDual ℝ RadiusTwoL2 := L.comp R
  let K : RadiusTwoL2 := (InnerProductSpace.toDual ℝ RadiusTwoL2).symm ell
  trace "RIESZ ROW DEFINED"
  refine ⟨K,?_⟩
  intro f U hU F hF hFA
  have hUR : U = R f := by
    apply TauCeti.Wkp.ext 2
    have hFirst : TauCeti.Wkp.firstOrder 1 U = TauCeti.Wkp.firstOrder 1 (R f) :=
      hU.trans (hR f).symm
    simpa only [TauCeti.Wkp.value_firstOrder] using congrArg TauCeti.W1p.value hFirst
  trace "RIESZ NATIVE H2 UNIQUENESS DERIVED"
  have hEval : L (R f) = F q := by
    rw [← hUR]
    exact hL U F hF hFA
  calc
    (∫ y in radiusTwoOpens, K y * f y ∂(volume : Measure R3)) = ⟪K,f⟫_ℝ := by
      rw [L2.inner_def]
      simp only [Real.inner_apply]
    _ = ell f := InnerProductSpace.toDual_symm_apply
    _ = L (R f) := rfl
    _ = F q := hEval

end OAI.AnisotropicCalderon.ExteriorSource
