import Calderon.ActualReferenceRotationAdjointH2LiftFamily
import Calderon.ActualReferenceRotationAdjointWeakHalfLiftFamily
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

attribute [local irreducible] referenceRotationAdjointH2LiftFamily
  referenceRotationAdjointWeakHalfLiftFamily referenceRotationAdjointWeakEnergyFamily
  referenceRotationAdjointWeakZeroEnergyFamily referenceWeakDirichletEnergyFamily


lemma referenceRotationAdjointH2LiftFamily_highWeakCoherence
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) =
      referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR HIGH WEAK COHERENCE PROOF ENTER"
    out.flush
  let A := referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
  let R := referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
  let z := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let P : BallH1 := harmonicFirstOrderLiftCompletion hF z
  let U : BallH1 := TauCeti.Wkp.firstOrder 1
    (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f)
  let V : BallH1 := referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t z
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR COHERENCE VALUES MADE"
    out.flush
  have hi := referenceRotationAdjointWeakZeroEnergyFamily_isInvertible_of_original g L y0 Φ B ε C ρ H a w hData hcalc i j t.1 t.2 hOriginal
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR COHERENCE ADJOINT INVERSE MADE"
    out.flush
  have hRestriction := referenceRotationAdjointWeakEnergyFamily_restriction g L y0 Φ B ε C ρ H a w hData τ0 hcalc i j t
  have hRestrict (u v : BallH1Zero) : R (u : BallH1) v = A u v :=
    congrArg (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => T u v) hRestriction
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR COHERENCE RESTRICTION MADE"
    out.flush
  have hZeroU : P-U ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
    referenceRotationAdjointH2LiftFamily_zero_boundary_difference g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j t f
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR COHERENCE HIGH BOUNDARY MADE"
    out.flush
  have hZeroV : P-V ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
    referenceRotationAdjointWeakHalfLiftFamily_affine_difference g L y0 Φ B ε C ρ H a w hData hcalc hF i j t z
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR COHERENCE LOW BOUNDARY MADE"
    out.flush
  have hDiff : U-V ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
    nativeH1_affine_difference_mem_zero P U V hZeroU hZeroV
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR COHERENCE ZERO DIFFERENCE MADE"
    out.flush
  have hU (v : BallH1Zero) : R U v=0 :=
    (referenceRotationAdjointWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc i j t U v).trans
      (referenceRotationAdjointH2LiftFamily_homogeneous_weak_energy g L y0 Φ B ε C ρ H a w hData
        τ0 hcalc hreg hF i j t hOriginal f v)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR COHERENCE HIGH ENERGY MADE"
    out.flush
  have hV (v : BallH1Zero) : R V v=0 :=
    (referenceRotationAdjointWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc i j t V v).trans
      (referenceRotationAdjointWeakHalfLiftFamily_weak_solution g L y0 Φ B ε C ρ H a w hData
        τ0 hcalc hF i j t hOriginal z v)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR COHERENCE LOW ENERGY MADE"
    out.flush
  exact eq_of_nativeEnergy_kernel_zero_difference A hi R hRestrict U V hDiff hU hV

  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ANGULAR HIGH WEAK COHERENCE BODY COMPLETE"
    out.flush


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointH2LiftFamily_highWeakCoherence
