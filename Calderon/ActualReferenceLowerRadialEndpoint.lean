import Calderon.ActualReferenceBoundaryCoefficientFamilies
import Calderon.ActualReferenceWeakConormalEndpointTopology
import Calderon.SphereSobolevTangentialDerivative

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeBoundaryCoefficientFamilies NativeNormalCoefficientInverseFamily
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! The same retained coefficient a; no parameter-dependent bound choices in the maps. -/
def referenceLowerRadialEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse.comp
    (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p -
      ∑ j : Fin 3, (referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j p).comp (sphereTangentialDerivativeL hF hO hD j))

lemma norm_referenceLowerRadialEndpointFamily_le
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) :
    ‖referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖ ≤
      ‖(referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse‖ *
        (‖referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p‖ +
          ∑ j : Fin 3, ‖referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j p‖ * ‖sphereTangentialDerivativeL hF hO hD j‖) := by
  unfold referenceLowerRadialEndpointFamily
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sub_le _ _).trans
  apply add_le_add_right
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  exact ContinuousLinearMap.opNorm_comp_le _ _

lemma contDiffAt_referenceLowerRadialEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a (p,x)) lam Lam)
    (hs : UnitBallSmallDriftData (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) lam) :
    ContDiffAt ℝ ∞ (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p := by
  have hNormal := contDiff_referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hInv := referenceNormalBoundaryMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p lam Lam hUE
  have hInvDiff : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
      (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t).inverse) p :=
    hInv.contDiffAt_map_inverse.comp p hNormal.contDiffAt
  have hWeak := contDiffAt_referenceWeakConormalEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF p lam hs
  have hTan : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
      ∑ j : Fin 3, (referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j t).comp (sphereTangentialDerivativeL hF hO hD j)) p := by
    apply ContDiffAt.sum
    intro j hj
    exact (contDiff_referenceTangentBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j).contDiffAt.clm_comp contDiffAt_const
  exact hInvDiff.clm_comp (hWeak.sub hTan)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceLowerRadialEndpointFamily_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceLowerRadialEndpointFamily
