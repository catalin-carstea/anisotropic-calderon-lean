import Calderon.ActualReferenceRotationAdjointRadialEndpointFamilies
import Calderon.ActualReferenceRotationAdjointConormalGreenPairing
import Calderon.ActualReferenceRotationTangentialHalfDualAdjunction
import Calderon.ActualReferenceRotationNormalHalfInverseDualAdjunction
import Calderon.ActualReferenceRotationNormalDriftHalfPairing
import Calderon.ActualReferenceRotationLowerRadialEndpoint
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
attribute [local irreducible] referenceRotationLowerRadialEndpointFamily referenceRotationAdjointHalfRadialFamily
  referenceRotationWeakConormalEndpointFamily referenceRotationAdjointWeakConormalEndpointFamily
  referenceRotationNormalHalfMultiplierFamily referenceRotationNormalBoundaryMultiplierFamily
  referenceRotationNormalDriftHalfMultiplierFamily referenceRotationTangentialAdjointHalfFamily

lemma sphereSobolevDualPairing_referenceRotationLowerRadial_adjoint
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) v
      (referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t f) =
    sphereSobolevDualPairing (1/2:ℝ) f
      (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t v) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL ANGULAR RADIAL DUALITY PROOF ENTER"
    out.flush
  let A := referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t
  let BN := referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t
  let N := referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF iA jA t
  let NA := referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF iA jA t
  let T := ∑ i : Fin 3, (referenceRotationTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA i t).comp
    (sphereTangentialDerivativeL hF hO hD i)
  let TS := referenceRotationTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t
  let MB := referenceRotationNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t
  let I := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let z : SphereSobolev (1/2:ℝ) := A.inverse v
  have hEval : referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t f =
      BN.inverse (N f-T f) := by
    unfold referenceRotationLowerRadialEndpointFamily
    rfl
  have hAlpha : sphereSobolevDualPairing (1/2:ℝ) v (BN.inverse (N f-T f)) =
      sphereSobolevDualPairing (1/2:ℝ) z (N f-T f) :=
    sphereSobolevDualPairing_referenceRotationNormalBoundaryMultiplier_inverse g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 iA jA t v (N f-T f)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL ANGULAR RADIAL DUALITY ALPHA COMPLETE"
    out.flush
  have hN := sphereSobolevDualPairing_referenceRotationOriginal_eq_adjoint_add_normal
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF iA jA t hOriginal f z
  have hT := sphereSobolevDualPairing_referenceRotationTangentialLower_adjoint
    g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t f z
  have hB := sphereSobolevDualPairing_referenceRotationNormalDriftHalfMultiplier
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t f z
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL ANGULAR RADIAL DUALITY THREE PAIRINGS COMPLETE"
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
  have hAdjEval : referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t v =
      NA z+I (MB z)-TS z := by
    unfold referenceRotationAdjointHalfRadialFamily
    rfl
  exact (congrArg (fun y : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) v y) hEval).trans
    (hAlpha.trans (hSub.trans ((congrArg₂ (fun x y : ℝ => x-y) hNBase hTBase).trans
      (hComb.symm.trans (congrArg
        (fun y : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) f y) hAdjEval.symm)))))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL ANGULAR RADIAL DUALITY BODY COMPLETE"
    out.flush

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceRotationLowerRadial_adjoint
