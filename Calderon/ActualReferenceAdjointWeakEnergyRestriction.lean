import Calderon.ActualReferenceAdjointWeakEnergyConstruction
import Calderon.NativeH1DualTestPostcompositionTopology
import Calderon.ActualReferenceAdjointWeakEnergyIdentification

set_option autoImplicit false
set_option maxSynthPendingDepth 10
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

#eval (do
  let out ← IO.getStdout
  out.putStrLn "ADJOINT R INFINITY DECL BEGIN"
  out.flush : IO Unit)

attribute [local irreducible] referenceAdjointFullWeakEnergyFamily
  referenceAdjointWeakEnergyFamily nativeH1ZeroDualRestrictionL

lemma contDiff_referenceAdjointWeakEnergyFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ADJOINT R CONGRUENCE PROOF ENTER"
    out.flush
  have hE : ContDiff ℝ ∞
      (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) :=
    contDiff_referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc
  have hPost : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      nativeH1ZeroDualRestrictionL.comp
        (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)) :=
    contDiff_nativeH1_dual_test_postcomposition nativeH1ZeroDualRestrictionL
      (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) hE
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ADJOINT R CHECKED POSTCOMPOSITION COMPLETE"
    out.flush
  have hEq : referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc =
      (fun p : ℝ × (R3 × ℝ) => nativeH1ZeroDualRestrictionL.comp
        (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)) :=
    funext (fun p => referenceAdjointWeakEnergyFamily_eq_nativeRestriction
      g L y0 Φ B ε C ρ H a w hData hcalc p)
  have hPredicate := congrArg
    (fun F : (ℝ × (R3 × ℝ)) → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero => ContDiff ℝ ∞ F) hEq.symm
  exact Eq.mp hPredicate hPost
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ADJOINT R INFINITY BODY COMPLETE"
    out.flush

#eval (do
  let out ← IO.getStdout
  out.putStrLn "ADJOINT R INFINITY DECL END"
  out.flush : IO Unit)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointWeakEnergyFamily
