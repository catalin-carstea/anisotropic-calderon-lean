import Calderon.NativeH2OutwardTraceOrthogonalCovariance
import Calderon.ActualReferenceSharpBoundaryIdentity
import Calderon.ActualReferenceSharpUpperTrace

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeFullSharpHalfTrace NativeFullHalfRadialTrace

lemma sphereSobolevOrthogonalPullback_inclusion_inverse
    (s t : ℝ) (hts : t ≤ s) (e : R3 ≃ₗᵢ[ℝ] R3) (f : SphereSobolev s) :
    sphereSobolevOrthogonalPullbackL t e
      (sphereSobolevInclusionL s t hts (sphereSobolevOrthogonalPullbackL s e.symm f)) =
    sphereSobolevInclusionL s t hts f := by
  have hc := congrArg (fun T : SphereSobolev s →L[ℝ] SphereSobolev t => T f)
    (sphereSobolevInclusionL_orthogonalPullback s t hts e.symm)
  simp only [ContinuousLinearMap.comp_apply] at hc
  rw [hc]
  simpa only [LinearIsometryEquiv.symm_symm] using
    sphereSobolevOrthogonalPullbackL_symm_apply t e.symm (sphereSobolevInclusionL s t hts f)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceOrthogonalStrongHarmonicLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2:ℝ)) : BallSobolev 2 :=
  nativeH2OrthogonalPullback hcalc e
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
      (harmonicLiftCompletion hF (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e.symm f)))

lemma firstOrder_referenceOrthogonalStrongHarmonicLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (referenceOrthogonalStrongHarmonicLift
      g L y0 Φ B ε C ρ H a w hData hcalc hF e p f) =
    nativeH1OrthogonalPullback e (TauCeti.Wkp.firstOrder 1
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
        (harmonicLiftCompletion hF (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e.symm f)))) :=
  firstOrder_nativeH2OrthogonalPullback hcalc e _

lemma nativeHalfTraceL_referenceOrthogonalStrongHarmonicLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1
      (referenceOrthogonalStrongHarmonicLift g L y0 Φ B ε C ρ H a w hData hcalc hF e p f)) =
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f := by
  rw [firstOrder_referenceOrthogonalStrongHarmonicLift,nativeHalfTraceL_nativeH1OrthogonalPullback]
  have ht := nativeHalfTraceL_firstOrder_referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2 hi
      (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e.symm f)
  rw [TauCeti.Wkp.firstOrderL_apply] at ht
  rw [ht]
  exact sphereSobolevOrthogonalPullback_inclusion_inverse (3/2:ℝ) (1/2:ℝ) (by norm_num) e f

lemma nativeHalfOutwardTraceL_referenceOrthogonalStrongHarmonicLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2:ℝ)) :
    nativeHalfOutwardTraceL hF hO hD hcalc τ0
      (referenceOrthogonalStrongHarmonicLift g L y0 Φ B ε C ρ H a w hData hcalc hF e p f) =
    sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevOrthogonalPullbackL (3/2:ℝ) e.symm f)) :=
  nativeHalfOutwardTraceL_nativeH2OrthogonalPullback hF hO hD hcalc τ0 e _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevOrthogonalPullback_inclusion_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrthogonalStrongHarmonicLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_referenceOrthogonalStrongHarmonicLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfTraceL_referenceOrthogonalStrongHarmonicLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfOutwardTraceL_referenceOrthogonalStrongHarmonicLift
