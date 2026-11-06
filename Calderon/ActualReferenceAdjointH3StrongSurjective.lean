import Calderon.ActualReferenceAdjointH3SolutionPair
import Calderon.ActualReferenceAdjointH3Dirichlet

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- Surjectivity at H³ comes from the SAME order-zero adjoint solution and
its proved H³ regularity, then exact P1→P0 lowering. -/
theorem referenceAdjointStrongDirichletFamilyOne_surjective
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (p : ℝ × (R3 × ℝ))
    (hA0 : (referenceAdjointStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    Function.Surjective (referenceAdjointStrongDirichletFamilyOne
      g L y0 Φ B ε C ρ H a w hData hcalc p) := by
  intro f
  obtain ⟨U0,hA0U0,U3,hU3⟩ := exists_referenceAdjointH3_solution_pair
    g L y0 Φ B ε C ρ H a w hData hcalc hreg p hA0 f
  have hm : U3 ∈ strongDirichletSubmodule 1 := by
    apply (mem_strongDirichletSubmodule 1 U3).mpr
    change TauCeti.Wkp.firstOrder 2 U3 ∈
      TauCeti.w1p0Submodule volume ballOpens 2
    rw [hU3]
    exact (strongDirichletProjectionL 0 U0).2
  let U1 : StrongDirichletSpace 1 := ⟨U3,hm⟩
  have hLow : (⟨nativeLowerOrderL 2 (U1 : BallSobolev 3),
      nativeLowerOrder_mem_strongDirichlet_zero U1⟩ : StrongDirichletSpace 0) = U0 := by
    apply Subtype.ext
    apply TauCeti.Wkp.ext 2
    have hFirst : TauCeti.Wkp.firstOrder 2 U3 =
        TauCeti.Wkp.firstOrder 1 (U0 : BallSobolev 2) :=
      hU3.trans (strongDirichletProjectionL_apply 0 U0)
    have hv : TauCeti.Wkp.value 2 (nativeLowerOrderL 2 (U1 : BallSobolev 3)) =
        TauCeti.Wkp.value 2 (U0 : BallSobolev 2) :=
      congrArg TauCeti.W1p.value hFirst
    exact hv
  refine ⟨U1,?_⟩
  apply TauCeti.Wkp.ext 1
  calc
    TauCeti.Wkp.value 1
        (referenceAdjointStrongDirichletFamilyOne
          g L y0 Φ B ε C ρ H a w hData hcalc p U1) =
      TauCeti.Wkp.value 0
        (referenceAdjointStrongDirichletFamily
          g L y0 Φ B ε C ρ H a w hData hcalc p
            ⟨nativeLowerOrderL 2 (U1 : BallSobolev 3),
              nativeLowerOrder_mem_strongDirichlet_zero U1⟩) :=
      value_referenceAdjointStrongDirichletFamilyOne_eq_zero
        g L y0 Φ B ε C ρ H a w hData hcalc p U1
    _ = TauCeti.Wkp.value 0
        (referenceAdjointStrongDirichletFamily
          g L y0 Φ B ε C ρ H a w hData hcalc p U0) := by rw [hLow]
    _ = TauCeti.Wkp.value 0 (nativeLowerOrderL 0 f) :=
      congrArg (TauCeti.Wkp.value 0) hA0U0
    _ = TauCeti.Wkp.value 1 f := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
