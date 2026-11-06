import Calderon.ActualReferenceSmoothMultiplierStrongDefect
import Calderon.ActualReferenceInvertibleStrongWeakCoherence
import Calderon.NativeH2SmoothMultiplierDerivative
import Calderon.NativeOrderOneCoefficientMultiplier

/-! Strong identity for the smooth multiplier: the actual harmonic lift identity, with an
explicit trace-kernel parameter as the only additional parameter. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHalfSmoothMultiplier NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier

theorem nativeHalfCoefficientMulL_smoothMultiplierLower_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothMultiplierDatum Q).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothMultiplierDatum Q).1 x‖ ≤ M) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) =
      nativeHalfSmoothMulL hF hO hD τ0 (smoothMultiplierDatum Q) hM hm hg := by
  have hd : coefficientSmoothData (smoothMultiplierLowerJets Q) = smoothMultiplierDatum Q := by
    apply Subtype.ext
    exact coefficientValue_smoothMultiplierLowerJets Q
  have hm' : ∀ x ∈ (ballOpens : Set R3),
      |(coefficientSmoothData (smoothMultiplierLowerJets Q)).1 x| ≤ M := by
    simpa only [hd] using hm
  have hg' : ∀ x ∈ (ballOpens : Set R3),
      ‖gradient (coefficientSmoothData (smoothMultiplierLowerJets Q)).1 x‖ ≤ M := by
    simpa only [hd] using hg
  have h := nativeHalfCoefficientMulL_eq_smoothMulL
    hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) hM hm' hg'
  simpa only [hd] using h

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceHarmonicLift_smooth_multiplier_difference_eq_strongDefect
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0) (Q : SmoothCoefficientJets 3)
    (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
      (harmonicLiftCompletion hF (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q f)) -
    coefficientMultiplier hcalc 2 Q
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
        (harmonicLiftCompletion hF f)) =
    referenceSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (smoothMultiplierDatum Q)
  let U : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2 :=
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).comp
      (harmonicLiftCompletion hF)
  let W : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
  let V : SphereSobolev (1/2 : ℝ) →L[ℝ] BallSobolev 2 :=
    referenceSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : BallSobolev 2 →L[ℝ] BallH1 := TauCeti.Wkp.firstOrderL 1
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (smoothMultiplierDatum Q).1 (smoothMultiplierDatum Q).2 hM hm hg
  let M3 := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let M1 := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  have hU (v : SphereSobolev (3/2 : ℝ)) : J (U v) = W (I v) :=
    firstOrder_referenceHarmonicLiftFamily_eq_weakHalfLift_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 p.1 p.2 hStrong hWeak v
  have hV : J (V (I f)) = W (M1 (I f))-S (W (I f)) := by
    have hv := firstOrder_referenceSmoothMultiplierStrongDefectFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q hM hm hg p hStrong hWeak (I f)
    have hm1 := nativeHalfCoefficientMulL_smoothMultiplierLower_eq hcalc hF hO hD τ0 Q hM hm hg
    change J (V (I f)) = W (nativeHalfSmoothMulL hF hO hD τ0
      (smoothMultiplierDatum Q) hM hm hg (I f))-S (W (I f)) at hv
    exact hv.trans (congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      W (A (I f))-S (W (I f))) hm1.symm)
  have hX : J (coefficientMultiplier hcalc 2 Q (U f)) = S (J (U f)) :=
    firstOrder_H2CoefficientMultiplier_eq_contDiffSMulL hcalc Q (U f) hM hm hg
  have hI : I (M3 f) = M1 (I f) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A f)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q
        (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have h1 : J (U (M3 f)) = W (M1 (I f)) := (hU (M3 f)).trans (congrArg W hI)
  have h2 : J (coefficientMultiplier hcalc 2 Q (U f)) = S (W (I f)) :=
    hX.trans (congrArg S (hU f))
  apply nativeH2_firstOrder_injective
  change J (U (M3 f)-coefficientMultiplier hcalc 2 Q (U f)) = J (V (I f))
  exact (J.map_sub _ _).trans
    ((congrArg₂ (fun x y : BallH1 => x-y) h1 h2).trans hV.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfCoefficientMulL_smoothMultiplierLower_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHarmonicLift_smooth_multiplier_difference_eq_strongDefect
