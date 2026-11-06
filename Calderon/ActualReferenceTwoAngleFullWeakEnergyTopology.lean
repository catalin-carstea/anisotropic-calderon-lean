import Calderon.ActualReferenceTwoAngleWeakOperator
import Calderon.NativeFullFiniteForcingTopology

/-! Full upfront: high-degree-rotation-author-oct15-v001/
REPAIR-two-angle-weak-literal-covariance-topology-partition-v065.md. Exact selected-claim partition. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

local instance : NormedAddCommGroup (StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (BallH1 →L[ℝ] StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (BallH1 →L[ℝ] StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedSpace

set_option diagnostics true in
lemma contDiff_referenceTwoAngleFullWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleFullWeakEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l) := by
  unfold referenceTwoAngleFullWeakEnergyFamily nativeSmoothCoefficientFullEnergyL
  exact contDiff_nativeFullFiniteForcingEnergy
    (fun d e => referenceTwoAnglePrincipalMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 i j k l d e)
    (fun d => referenceTwoAngleDriftMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 i j k l d)
    (fun d e => contDiff_referenceTwoAnglePrincipalMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 i j k l d e)
    (fun d => contDiff_referenceTwoAngleDriftMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 i j k l d)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleFullWeakEnergyFamily
