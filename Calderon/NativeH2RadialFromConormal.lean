import Calderon.NativeH2ConormalRadialConversion
import Calderon.NativeBoundaryNormalMultiplierInverse

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeFullSharpHalfTrace NativeNegativeHalfSmoothMultiplier
  NativeBoundaryNormalMultiplierInverse

/-! Expansion: EXPANSION-native-H2-conormal-radial-conversion-v001.md, step 3.
The normal inverse is derived from actual open-ball ellipticity by the imported module. -/

theorem nativeH2_radial_eq_inverse_conormal_sub_tangent
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(boundaryNormalCoefficientData F).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryNormalCoefficientData F).1 x‖ ≤ M)
    {N : Fin 3 → ℝ} (hN : ∀ j, 0 ≤ N j)
    (ht : ∀ j, ∀ x ∈ (ballOpens : Set R3), |(boundaryTangentCoefficientData F j).1 x| ≤ N j)
    (hgt : ∀ j, ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryTangentCoefficientData F j).1 x‖ ≤ N j)
    (U : BallSobolev 2) :
    (nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hg).inverse
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
          (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U)) -
        ∑ j : Fin 3,
          nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryTangentCoefficientData F j)
            (hN j) (ht j) (hgt j)
            (sphereTangentialDerivativeL hF hO hD j
              (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)))) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U)) := by
  rw [nativeH2_conormal_negativeHalf_eq_normal_add_tangent
    hcalc hF hO hD τ0 F hM hm hg hN ht hgt U,add_sub_cancel_right]
  exact inverse_nativeNegativeHalfNormalCoefficientMulL_apply
    hF hO hD τ0 F lam Lam hUE hM hm hg _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
