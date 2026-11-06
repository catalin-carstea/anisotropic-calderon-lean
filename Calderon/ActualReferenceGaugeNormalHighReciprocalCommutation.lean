import Calderon.ActualReferenceGaugeNormalThreeHalfMultiplier
import Calderon.NativeThreeHalfCoefficientCommutation

/-! Same actual high right reciprocal. -/
set_option autoImplicit false
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (y0 : R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceGaugeNormalThreeHalfMultiplierFamily nativeThreeHalfCoefficientMulL

lemma referenceGaugeNormalThreeHalfMultiplierFamily_inverse_commutes_coefficientMulL
    (p : ℝ × (R3 × ℝ)) (Q : SmoothCoefficientJets 3) :
    (referenceGaugeNormalThreeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse.comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q) =
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q).comp
      (referenceGaugeNormalThreeHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse := by
  let P := referenceGaugeNormalThreeHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let M := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  have hi : P.IsInvertible := referenceGaugeNormalThreeHalfMultiplierFamily_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  apply ContinuousLinearMap.ext
  intro u
  have hP (z : SphereSobolev (3/2 : ℝ)) : P z =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p) z := by
    dsimp only [P]
    unfold referenceGaugeNormalThreeHalfMultiplierFamily
    rfl
  have hNative := nativeThreeHalfCoefficientMulL_comm_apply hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p)
    Q (P.inverse u)
  have hComm : P (M (P.inverse u)) = M (P (P.inverse u)) :=
    (hP (M (P.inverse u))).trans (hNative.trans (congrArg M (hP (P.inverse u)).symm))
  have hRight : P (M (P.inverse u)) = M u :=
    hComm.trans (congrArg M (hi.self_apply_inverse u))
  have hInverse := congrArg P.inverse hRight
  exact hInverse.symm.trans (hi.inverse_apply_self (M (P.inverse u)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalThreeHalfMultiplierFamily_inverse_commutes_coefficientMulL
