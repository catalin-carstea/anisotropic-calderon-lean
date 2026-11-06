import Calderon.NativeCoefficientRotationAdjointEndpointCompatibility
import Calderon.SphereSobolevHalfDualRotationPairing
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap NativeCoefficientBoundaryMultiplier

lemma sphereSobolevDualPairing_nativeHalfCoefficientRotation_adjoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (i j : Fin 3) (u v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) v
      ((nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
        (sphereSobolevRotationL (1/2:ℝ) i j) u) =
    sphereSobolevDualPairing (1/2:ℝ) u
      (nativeCoefficientRotationAdjointEndpointL (1/2:ℝ)
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F) i j v) := by
  let M := nativeHalfCoefficientMulL hcalc hF hO hD τ0 F
  let R := sphereSobolevRotationL (1/2:ℝ) i j
  change ⟪v,nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F (R u)⟫_ℝ = ⟪u,-(R (M v))⟫_ℝ
  rw [inner_neg_right]
  have hM : ⟪v,nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F (R u)⟫_ℝ = ⟪M v,R u⟫_ℝ :=
    ContinuousLinearMap.adjoint_inner_right M v (R u)
  have hSwap : ⟪M v,R u⟫_ℝ = ⟪R u,M v⟫_ℝ := real_inner_comm _ _
  exact hM.trans (hSwap.trans (sphereSobolevDualPairing_half_rotation_skew i j u (M v)))

end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_nativeHalfCoefficientRotation_adjoint
