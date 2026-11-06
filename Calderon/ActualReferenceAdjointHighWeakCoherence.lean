import Calderon.ActualReferenceAdjointH2LiftFamily
import Calderon.ActualReferenceAdjointWeakHalfLiftFamily
import Calderon.NativeCoefficientWeakHalfLiftUniqueness

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceAdjointH2LiftFamily
  referenceAdjointWeakHalfLiftFamily referenceAdjointWeakEnergyFamily
  referenceAdjointWeakZeroEnergyFamily referenceWeakDirichletEnergyFamily

#eval (do
  let out ← IO.getStdout
  out.putStrLn "HIGH WEAK COHERENCE DECL BEGIN"
  out.flush : IO Unit)

lemma referenceAdjointH2LiftFamily_highWeakCoherence
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (referenceAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) =
      referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HIGH WEAK COHERENCE PROOF ENTER"
    out.flush
  let A := referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let R := referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let z := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let P : BallH1 := harmonicFirstOrderLiftCompletion hF z
  let U : BallH1 := TauCeti.Wkp.firstOrder 1
    (referenceAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
  let V : BallH1 := referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p z
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "COHERENCE VALUES MADE"
    out.flush
  have hi := referenceAdjointWeakZeroEnergyFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc p hOriginal
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "COHERENCE ADJOINT INVERSE MADE"
    out.flush
  have hRestriction := referenceAdjointWeakEnergyFamily_restriction g L y0 Φ B ε C ρ H a w hData τ0 hcalc p
  have hRestrict (u v : BallH1Zero) : R (u : BallH1) v = A u v :=
    congrArg (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => T u v) hRestriction
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "COHERENCE RESTRICTION MADE"
    out.flush
  have hZeroU : P-U ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
    referenceAdjointH2LiftFamily_zero_boundary_difference g L y0 Φ B ε C ρ H a w hData hcalc hF hO p f
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "COHERENCE HIGH BOUNDARY MADE"
    out.flush
  have hZeroV : P-V ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
    referenceAdjointWeakHalfLiftFamily_affine_difference g L y0 Φ B ε C ρ H a w hData hcalc hF p z
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "COHERENCE LOW BOUNDARY MADE"
    out.flush
  have hDiff : U-V ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
    nativeH1_affine_difference_mem_zero P U V hZeroU hZeroV
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "COHERENCE ZERO DIFFERENCE MADE"
    out.flush
  have hU (v : BallH1Zero) : R U v=0 :=
    (referenceAdjointWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p U v).trans
      (referenceAdjointH2LiftFamily_homogeneous_weak_energy g L y0 Φ B ε C ρ H a w hData
        τ0 hcalc hreg hF p hOriginal f v)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "COHERENCE HIGH ENERGY MADE"
    out.flush
  have hV (v : BallH1Zero) : R V v=0 :=
    (referenceAdjointWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p V v).trans
      (referenceAdjointWeakHalfLiftFamily_weak_solution g L y0 Φ B ε C ρ H a w hData
        τ0 hcalc hF p hOriginal z v)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "COHERENCE LOW ENERGY MADE"
    out.flush
  exact eq_of_nativeEnergy_kernel_zero_difference A hi R hRestrict U V hDiff hU hV

  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HIGH WEAK COHERENCE BODY COMPLETE"
    out.flush

#eval (do
  let out ← IO.getStdout
  out.putStrLn "HIGH WEAK COHERENCE DECL END"
  out.flush : IO Unit)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointH2LiftFamily_highWeakCoherence
