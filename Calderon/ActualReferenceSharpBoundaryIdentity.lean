import Calderon.ActualReferenceStrongWeakHalfCoherence
import Calderon.NativeHalfTraceRightInverse

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence NativeFullSharpHalfTrace
  NativeHalfTraceRightInverse SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


theorem nativeHalfTraceL_referenceWeakHalfLiftFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2 : ℝ)) :
    nativeHalfTraceL hF hO hD τ0
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) = f := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  rw [sphereSobolevCoefficientL_nativeHalfTraceL]
  exact sphereHarmonicCoordinate_valueTraceL_referenceWeakHalfLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f k

theorem nativeHalfTraceL_comp_referenceWeakHalfLiftFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    (nativeHalfTraceL hF hO hD τ0).comp
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p) =
    ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) := by
  apply ContinuousLinearMap.ext
  intro f
  exact nativeHalfTraceL_referenceWeakHalfLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f

theorem nativeHalfTraceL_firstOrder_referenceHarmonicLiftFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrderL 1
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
        (harmonicLiftCompletion hF f))) =
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f := by
  let E : BallSobolev 2 := harmonicLiftCompletion hF f
  let U : BallSobolev 2 :=
    referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E
  let Q : BallSobolev 2 →L[ℝ] BallH1 := TauCeti.Wkp.firstOrderL 1
  let T : BallH1 →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfTraceL hF hO hD τ0
  have hz : Q (U-E) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceHarmonicLiftFamily_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc 0 q p hi E
  let c : BallH1Zero := ⟨Q (U-E),hz⟩
  have ht : T (Q (U-E)) = 0 := nativeHalfTraceL_zeroDirichlet hF hO hD τ0 c
  have hsub : T (Q U)-T (Q E) = 0 := by
    simpa only [map_sub] using ht
  have hsame : T (Q U) = T (Q E) := sub_eq_zero.mp hsub
  have hharm : T (Q E) =
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f := by
    change nativeHalfTraceL hF hO hD τ0
      (TauCeti.Wkp.firstOrderL 1 (harmonicLiftCompletion hF f)) = _
    rw [firstOrder_harmonicLiftCompletion hF hO]
    exact nativeHalfTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0 _
  exact hsame.trans hharm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
