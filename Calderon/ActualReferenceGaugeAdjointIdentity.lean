import Calderon.ActualReferenceGaugeRadialDecomposition
import Calderon.ActualReferenceGaugeNormalMultiplierCompatibility
import Calderon.NativeGaugeAdjointIdentity

/-! Full upfront: actual-gradient-drift-author-oct15-v001/
EXPANSION-actual-gauge-adjoint-identity-v011.md. Actual SAME lower DN and true pivot transpose. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceLowerRadialEndpointFamily
  referenceGaugeNormalHalfMultiplierFamily referenceGaugeNormalNegativeHalfMultiplierFamily
  referenceGaugeWeakConormalEndpointFamily referenceGaugeTangentEndpointFamily sphereLowerDistributionalTranspose

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ))
  (hNormal : (referenceNormalBoundaryMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
  (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
  (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)

include hNormal hStrong hWeak

theorem referenceLowerRadialEndpoint_distributionalTranspose_mul_gaugeNormal :
    (sphereLowerDistributionalTranspose (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)).comp (referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) =
    (referenceGaugeNormalNegativeHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)+(referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)-sphereLowerDistributionalTranspose (referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) := by
  let A := (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
  let M := (referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  let Mn := (referenceGaugeNormalNegativeHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  let T := (referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  let N := (referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p)
  have hM : ∀ u : SphereSobolev (1/2 : ℝ), ∀ v : SphereSobolev (-(1/2 : ℝ)),
      sphereSobolevDualPairing (1/2 : ℝ) (M u) v = sphereSobolevDualPairing (1/2 : ℝ) u (Mn v) := by
    intro u v
    have hPair := sphereSobolevDualPairing_referenceGaugeNormalMultiplier g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p v u
    simp only [sphereSobolevDualPairing] at hPair ⊢
    exact (real_inner_comm _ _).trans (hPair.symm.trans (real_inner_comm _ _))
  have hN : N=Mn.comp A+T := by
    dsimp only [N,Mn,A,T]
    unfold referenceGaugeNormalNegativeHalfMultiplierFamily
    exact referenceGaugeWeakConormalEndpointFamily_eq_normal_add_tangent
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p hNormal hStrong hWeak
  have hSym : ∀ f z : SphereSobolev (1/2 : ℝ),
      sphereSobolevDualPairing (1/2 : ℝ) z (N f) = sphereSobolevDualPairing (1/2 : ℝ) f (N z) :=
    sphereSobolevDualPairing_referenceGaugeWeakConormalEndpoint_comm
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF p hWeak
  exact lower_distributionalTranspose_mul_eq_of_symmetric_weighted_operator A T N M Mn hM hN hSym

theorem referenceLowerRadialEndpoint_distributionalTranspose_sub_gaugeNormal_inverse :
    sphereLowerDistributionalTranspose (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)-(referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    ((referenceGaugeNormalNegativeHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)-(referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp (referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)+(referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)-sphereLowerDistributionalTranspose (referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)).comp (referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse := by
  let A := (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
  let M := (referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  let Mn := (referenceGaugeNormalNegativeHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  let T := (referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  let N := (referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p)
  have hM : ∀ u : SphereSobolev (1/2 : ℝ), ∀ v : SphereSobolev (-(1/2 : ℝ)),
      sphereSobolevDualPairing (1/2 : ℝ) (M u) v = sphereSobolevDualPairing (1/2 : ℝ) u (Mn v) := by
    intro u v
    have hPair := sphereSobolevDualPairing_referenceGaugeNormalMultiplier g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p v u
    simp only [sphereSobolevDualPairing] at hPair ⊢
    exact (real_inner_comm _ _).trans (hPair.symm.trans (real_inner_comm _ _))
  have hN : N=Mn.comp A+T := by
    dsimp only [N,Mn,A,T]
    unfold referenceGaugeNormalNegativeHalfMultiplierFamily
    exact referenceGaugeWeakConormalEndpointFamily_eq_normal_add_tangent
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p hNormal hStrong hWeak
  have hSym : ∀ f z : SphereSobolev (1/2 : ℝ),
      sphereSobolevDualPairing (1/2 : ℝ) z (N f) = sphereSobolevDualPairing (1/2 : ℝ) f (N z) :=
    sphereSobolevDualPairing_referenceGaugeWeakConormalEndpoint_comm
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF p hWeak
  have hi : M.IsInvertible := (referenceGaugeNormalMultiplierFamilies_isInvertible g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).1
  have hInv : M.comp M.inverse = ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) := by
    apply ContinuousLinearMap.ext
    intro f
    exact hi.self_apply_inverse f
  exact lower_distributionalTranspose_sub_eq_of_right_inverse A T N M Mn hM hN hSym M.inverse hInv

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialEndpoint_distributionalTranspose_mul_gaugeNormal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialEndpoint_distributionalTranspose_sub_gaugeNormal_inverse
