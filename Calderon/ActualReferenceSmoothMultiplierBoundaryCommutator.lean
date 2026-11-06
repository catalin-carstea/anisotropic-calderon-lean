import Calderon.ActualReferenceSmoothMultiplierStrongIdentity
import Calderon.NativeH2SmoothMultiplierOutwardTrace
import Calderon.ActualReferenceSharpUpperTrace

/-! Smooth boundary commutator. The genuine plus normal multiplier is part of the bounded
extension; no gain premise is assumed. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeFullSharpHalfTrace NativeFullHalfRadialTrace
  NativeHarmonicLiftCompletion NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceSmoothMultiplierBoundaryCommutatorFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (nativeHalfOutwardTraceL hF hO hD hcalc τ0).comp
    (referenceSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p) +
  nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q

lemma referenceSmoothMultiplierBoundaryCommutatorFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (u : SphereSobolev (1/2 : ℝ)) :
    referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q p u =
      nativeHalfOutwardTraceL hF hO hD hcalc τ0
        (referenceSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p u) +
      nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q u := rfl

lemma norm_referenceSmoothMultiplierBoundaryCommutatorFamily_le
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    ‖referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q p‖ ≤
    ‖nativeHalfOutwardTraceL hF hO hD hcalc τ0‖ *
      ‖referenceSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p‖ +
    ‖nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q‖ := by
  let O := nativeHalfOutwardTraceL hF hO hD hcalc τ0
  let V := referenceSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
  let Nq := nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q
  exact (norm_add_le (O.comp V) Nq).trans
    (add_le_add (ContinuousLinearMap.opNorm_comp_le O V) le_rfl)

attribute [local irreducible] nativeHalfOutwardTraceL referenceHarmonicLiftFamily harmonicLiftCompletion

lemma referenceSmoothMultiplierBoundaryCommutatorFamily_inclusion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0) (Q : SmoothCoefficientJets 3)
    (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q p
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) =
    referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q f) -
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) := by
  let U : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2 :=
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).comp
      (harmonicLiftCompletion hF)
  let V := referenceSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
  let O := nativeHalfOutwardTraceL hF hO hD hcalc τ0
  let T := nativeHalfTraceL hF hO hD τ0
  let J : BallSobolev 2 →L[ℝ] BallH1 := TauCeti.Wkp.firstOrderL 1
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let M3 := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let M1 := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let Nq := nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q
  have hb : U (M3 f)-coefficientMultiplier hcalc 2 Q (U f) = V (I f) :=
    referenceHarmonicLift_smooth_multiplier_difference_eq_strongDefect
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q p hStrong hWeak f
  have ht : T (J (U f)) = I f :=
    nativeHalfTraceL_firstOrder_referenceHarmonicLiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2 hStrong f
  have hx : O (coefficientMultiplier hcalc 2 Q (U f)) = M1 (O (U f))+Nq (I f) := by
    have hp := nativeHalfOutwardTraceL_smooth_multiplier hcalc hF hO hD τ0 Q (U f)
    change O (coefficientMultiplier hcalc 2 Q (U f)) = M1 (O (U f))+Nq (T (J (U f))) at hp
    exact hp.trans (congrArg (fun v => M1 (O (U f))+Nq v) ht)
  have hd : O (U (M3 f))-O (coefficientMultiplier hcalc 2 Q (U f)) = O (V (I f)) :=
    (O.map_sub _ _).symm.trans (congrArg O hb)
  have hd' : O (U (M3 f))-(M1 (O (U f))+Nq (I f)) = O (V (I f)) :=
    (congrArg (fun v => O (U (M3 f))-v) hx).symm.trans hd
  have hB : referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q p (I f) = O (V (I f))+Nq (I f) :=
    referenceSmoothMultiplierBoundaryCommutatorFamily_apply
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p (I f)
  have hDNop : referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p = O.comp U := by
    unfold referenceSharpRadialTraceFamily
    rfl
  have hDN (v : SphereSobolev (3/2 : ℝ)) :
      referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 p v = O (U v) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v) hDNop
  have hc : O (V (I f))+Nq (I f) = O (U (M3 f))-M1 (O (U f)) := by
    rw [← hd']
    abel
  exact hB.trans (hc.trans
    (congrArg₂ (fun x y : SphereSobolev (1/2 : ℝ) => x-M1 y)
      (hDN (M3 f)).symm (hDN f).symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierBoundaryCommutatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierBoundaryCommutatorFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceSmoothMultiplierBoundaryCommutatorFamily_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierBoundaryCommutatorFamily_inclusion
