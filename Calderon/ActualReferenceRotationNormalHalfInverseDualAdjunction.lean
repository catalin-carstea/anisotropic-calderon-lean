import Calderon.ActualReferenceRotationNormalEndpointInverseFamilies
import Calderon.ActualReferenceNormalHalfInverseDualAdjunction
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3)

lemma referenceRotationNormalBoundaryMultiplierFamily_isInvertible_of_referenceData (t : ℝ × (ℝ × (R3 × ℝ))) :
    (referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t).IsInvertible := by
  exact referenceRotationNormalBoundaryMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t.1 t.2
      (referenceNormalBoundaryMultiplierFamily_isInvertible_of_referenceData
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t.2)

lemma sphereSobolevDualPairing_referenceRotationNormalBoundaryMultiplier_inverse
    (t : ℝ × (ℝ × (R3 × ℝ))) (v : SphereSobolev (1/2:ℝ)) (y : SphereSobolev (-(1/2:ℝ))) :
    sphereSobolevDualPairing (1/2:ℝ) v
      ((referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t).inverse y) =
    sphereSobolevDualPairing (1/2:ℝ)
      ((referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t).inverse v) y := by
  let A := referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t
  let BN := referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t
  have hA : A.IsInvertible := referenceRotationNormalHalfMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t
  have hB : BN.IsInvertible := referenceRotationNormalBoundaryMultiplierFamily_isInvertible_of_referenceData
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t
  have hPair : ⟪A.inverse v,BN (BN.inverse y)⟫_ℝ = ⟪A (A.inverse v),BN.inverse y⟫_ℝ :=
    ContinuousLinearMap.adjoint_inner_right A (A.inverse v) (BN.inverse y)
  have hLeft : ⟪A.inverse v,BN (BN.inverse y)⟫_ℝ = ⟪A.inverse v,y⟫_ℝ :=
    congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => ⟪A.inverse v,z⟫_ℝ) (hB.self_apply_inverse y)
  have hRight : ⟪A (A.inverse v),BN.inverse y⟫_ℝ = ⟪v,BN.inverse y⟫_ℝ :=
    congrArg (fun z : SphereSobolev (1/2:ℝ) => ⟪z,BN.inverse y⟫_ℝ) (hA.self_apply_inverse v)
  exact (hLeft.symm.trans (hPair.trans hRight)).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalBoundaryMultiplierFamily_isInvertible_of_referenceData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceRotationNormalBoundaryMultiplier_inverse
