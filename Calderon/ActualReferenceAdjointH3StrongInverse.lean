import Calderon.ActualReferenceAdjointH3StrongInjective
import Calderon.ActualReferenceAdjointH3StrongSurjective
import Calderon.ActualReferenceAdjointStrongInverse

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

/-- The SAME full order-one reference adjoint is invertible on the established
weak invertible locus; this is derived from the order-zero inverse and H³
regularity, with no new inverse premise. -/
theorem referenceAdjointStrongDirichletFamilyOne_isInvertible
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (referenceAdjointStrongDirichletFamilyOne
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible := by
  letI : CompleteSpace (StrongDirichletSpace 1) := instCompleteSpaceStrongDirichletSpace 1
  have hA0 := referenceAdjointStrongDirichletFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg p hOriginal
  let A := referenceAdjointStrongDirichletFamilyOne
    g L y0 Φ B ε C ρ H a w hData hcalc p
  have hinj : Function.Injective A :=
    referenceAdjointStrongDirichletFamilyOne_injective
      g L y0 Φ B ε C ρ H a w hData hcalc p hA0
  have hsurj : Function.Surjective A :=
    referenceAdjointStrongDirichletFamilyOne_surjective
      g L y0 Φ B ε C ρ H a w hData hcalc hreg p hA0
  have hker : A.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : A.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  exact ⟨ContinuousLinearEquiv.ofBijective A hker hrange,
    ContinuousLinearEquiv.coe_ofBijective A hker hrange⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
