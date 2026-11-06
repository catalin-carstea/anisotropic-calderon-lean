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

/-- Injectivity at order one follows from exact order-lowering and the
established SAME full adjoint order-zero inverse. -/
theorem referenceAdjointStrongDirichletFamilyOne_injective
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hA0 : (referenceAdjointStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    Function.Injective (referenceAdjointStrongDirichletFamilyOne
      g L y0 Φ B ε C ρ H a w hData hcalc p) := by
  intro U V hUV
  let U0 : StrongDirichletSpace 0 :=
    ⟨nativeLowerOrderL 2 (U : BallSobolev 3),
      nativeLowerOrder_mem_strongDirichlet_zero U⟩
  let V0 : StrongDirichletSpace 0 :=
    ⟨nativeLowerOrderL 2 (V : BallSobolev 3),
      nativeLowerOrder_mem_strongDirichlet_zero V⟩
  have hLowValue : TauCeti.Wkp.value 0
      (referenceAdjointStrongDirichletFamily
        g L y0 Φ B ε C ρ H a w hData hcalc p U0) =
      TauCeti.Wkp.value 0
      (referenceAdjointStrongDirichletFamily
        g L y0 Φ B ε C ρ H a w hData hcalc p V0) := by
    calc
      _ = TauCeti.Wkp.value 1
        (referenceAdjointStrongDirichletFamilyOne
          g L y0 Φ B ε C ρ H a w hData hcalc p U) :=
        (value_referenceAdjointStrongDirichletFamilyOne_eq_zero
          g L y0 Φ B ε C ρ H a w hData hcalc p U).symm
      _ = TauCeti.Wkp.value 1
        (referenceAdjointStrongDirichletFamilyOne
          g L y0 Φ B ε C ρ H a w hData hcalc p V) :=
        congrArg (TauCeti.Wkp.value 1) hUV
      _ = _ := value_referenceAdjointStrongDirichletFamilyOne_eq_zero
        g L y0 Φ B ε C ρ H a w hData hcalc p V
  have hLow : U0 = V0 := hA0.injective (TauCeti.Wkp.ext 0 hLowValue)
  apply Subtype.ext
  apply TauCeti.Wkp.ext_lowerOrder 2
  exact congrArg Subtype.val hLow

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
