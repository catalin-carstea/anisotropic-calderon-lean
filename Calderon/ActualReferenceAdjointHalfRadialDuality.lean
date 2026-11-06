import Calderon.ActualReferenceAdjointRadialEndpointFamilies
import Calderon.ActualReferenceAdjointConormalGreenPairing
import Calderon.ActualReferenceTangentialHalfDualAdjunction
import Calderon.ActualReferenceNormalHalfInverseDualAdjunction
import Calderon.ActualReferenceNormalDriftHalfPairing
import Calderon.ActualReferenceLowerRadialEndpoint
import Calderon.SphereSobolevHalfDualLinearCombination
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
attribute [local irreducible] referenceLowerRadialEndpointFamily referenceAdjointHalfRadialFamily
  referenceWeakConormalEndpointFamily referenceAdjointWeakConormalEndpointFamily
  referenceNormalHalfMultiplierFamily referenceNormalBoundaryMultiplierFamily
  referenceNormalDriftHalfMultiplierFamily referenceTangentialAdjointHalfFamily

#eval (do
  let out ← IO.getStdout
  out.putStrLn "ACTUAL RADIAL DUALITY DECL BEGIN"
  out.flush : IO Unit)
lemma sphereSobolevDualPairing_referenceLowerRadial_adjoint
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) v
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) =
    sphereSobolevDualPairing (1/2:ℝ) f
      (referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL RADIAL DUALITY PROOF ENTER"
    out.flush
  let A := referenceNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let BN := referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let N := referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
  let NA := referenceAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF p
  let T := ∑ i : Fin 3, (referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i p).comp
    (sphereTangentialDerivativeL hF hO hD i)
  let TS := referenceTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let MB := referenceNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let I := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let z : SphereSobolev (1/2:ℝ) := A.inverse v
  have hEval : referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f =
      BN.inverse (N f-T f) := by
    unfold referenceLowerRadialEndpointFamily
    rfl
  have hAlpha : sphereSobolevDualPairing (1/2:ℝ) v (BN.inverse (N f-T f)) =
      sphereSobolevDualPairing (1/2:ℝ) z (N f-T f) :=
    sphereSobolevDualPairing_referenceNormalBoundaryMultiplier_inverse g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p v (N f-T f)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL RADIAL DUALITY ALPHA COMPLETE"
    out.flush
  have hN := sphereSobolevDualPairing_referenceOriginal_eq_adjoint_add_normal
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF p hOriginal f z
  have hT := sphereSobolevDualPairing_referenceTangentialLower_adjoint
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f z
  have hB := sphereSobolevDualPairing_referenceNormalDriftHalfMultiplier
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f z
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL RADIAL DUALITY THREE PAIRINGS COMPLETE"
    out.flush
  have hNBase : sphereSobolevDualPairing (1/2:ℝ) z (N f) =
      sphereSobolevDualPairing (1/2:ℝ) f (NA z) + sphereSobolevDualPairing (1/2:ℝ) f (I (MB z)) :=
    hN.trans (congrArg (fun b : ℝ => sphereSobolevDualPairing (1/2:ℝ) f (NA z)+b) hB.symm)
  have hTBase : sphereSobolevDualPairing (1/2:ℝ) z (T f) =
      sphereSobolevDualPairing (1/2:ℝ) f (TS z) := hT
  have hSub : sphereSobolevDualPairing (1/2:ℝ) z (N f-T f) =
      sphereSobolevDualPairing (1/2:ℝ) z (N f)-sphereSobolevDualPairing (1/2:ℝ) z (T f) :=
    inner_sub_right _ _ _
  have hComb : sphereSobolevDualPairing (1/2:ℝ) f (NA z+I (MB z)-TS z) =
      sphereSobolevDualPairing (1/2:ℝ) f (NA z)+sphereSobolevDualPairing (1/2:ℝ) f (I (MB z))-
        sphereSobolevDualPairing (1/2:ℝ) f (TS z) :=
    sphereSobolevDualPairing_half_add_sub f (NA z) (I (MB z)) (TS z)
  have hAdjEval : referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v =
      NA z+I (MB z)-TS z := by
    unfold referenceAdjointHalfRadialFamily
    rfl
  exact (congrArg (fun y : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) v y) hEval).trans
    (hAlpha.trans (hSub.trans ((congrArg₂ (fun x y : ℝ => x-y) hNBase hTBase).trans
      (hComb.symm.trans (congrArg
        (fun y : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) f y) hAdjEval.symm)))))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL RADIAL DUALITY BODY COMPLETE"
    out.flush

#eval (do
  let out ← IO.getStdout
  out.putStrLn "ACTUAL RADIAL DUALITY DECL END"
  out.flush : IO Unit)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceLowerRadial_adjoint
