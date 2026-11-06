import Calderon.NativeFullHalfRadialTrace
import Calderon.NativeHarmonicLiftExtension
import Calderon.ActualJointNativeTraceOperatorFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeFullHalfRadialTrace
  NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceSharpRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (nativeHalfOutwardTraceL hF hO hD hcalc τ0).comp
    ((referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).comp
      (harmonicLiftCompletion hF))

lemma referenceSharpRadialTraceFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2 : ℝ)) :
    referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f =
      nativeHalfOutwardTraceL hF hO hD hcalc τ0
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
          (harmonicLiftCompletion hF f)) := rfl

lemma sphereSobolevInclusionL_referenceSharpRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) =
      sphereSobolevZeroEquiv hO hD
        (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 p.1 p.2
          (harmonicLiftCompletion hF f)) := by
  exact sphereSobolevInclusionL_nativeHalfOutwardTraceL hF hO hD hcalc τ0
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
      (harmonicLiftCompletion hF f))

lemma norm_referenceSharpRadialTraceFamily_le
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) :
    ‖referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖ ≤
      ‖nativeHalfOutwardTraceL hF hO hD hcalc τ0‖ *
        (‖referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2‖ *
          ‖harmonicLiftCompletion hF‖) := by
  let T := nativeHalfOutwardTraceL hF hO hD hcalc τ0
  let V := referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
  let P := harmonicLiftCompletion hF
  change ‖T.comp (V.comp P)‖ ≤ ‖T‖ * (‖V‖ * ‖P‖)
  exact (ContinuousLinearMap.opNorm_comp_le T (V.comp P)).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le V P) (norm_nonneg T))

lemma contDiffAt_referenceSharpRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p := by
  exact contDiffAt_const.clm_comp
    ((contDiffAt_joint_referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p hi).clm_comp
      contDiffAt_const)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
