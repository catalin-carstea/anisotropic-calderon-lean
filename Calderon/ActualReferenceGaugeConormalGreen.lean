import Calderon.ActualReferenceGaugeWeakConormalEndpoint
import Calderon.ActualReferenceInvertibleConormalCompatibility
import Calderon.SphereContinuousScalarMultiplierSymmetry

/-! Full upfront: actual-gradient-drift-author-oct15-v001/
EXPANSION-actual-gauge-conormal-green-v008.md. Original conormal of SAME U. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion SphereHarmonic NativePolynomialBulkMoments NativeHalfSmoothMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem sphereSobolevDualPairing_referenceGaugeWeakConormal_high_Green
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (τ0 : UnitBallValueTrace) (q : ℝ) (p : R3 × ℝ)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,p)).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) (z : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) z
      (referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF (q,p)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) =
    ⟪referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p (harmonicLiftCompletion hF f)),
      sphereContinuousScalarMulL
        (smoothSphereValue (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg (q,p)))
        (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z))⟫_ℝ := by
  let m := referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg (q,p)
  obtain ⟨M,hM,hm,hgrad⟩ := exists_smooth_ball_multiplier_bound m
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hgrad
  let W : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p)
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let T : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 := harmonicFirstOrderLiftCompletion hF
  let U : BallSobolev 2 := referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 q p (harmonicLiftCompletion hF f)
  let Q : BallH1 → ℝ := fun u => sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => a ((q,p),x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),x)) 0
    u (S (T z))
  have hE := sphereSobolevDualPairing_referenceGaugeWeakConormalEndpoint_energy
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF (q,p) (I f) z
  have hGauge := referenceEnergy_exponentialGauge
    g L y0 Φ B ε C ρ H a w hData hg (q,p) hM hm hgrad (W (I f)) (T z)
  have hProduct := congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) hGauge.symm
  have hCo := firstOrder_referenceHarmonicLiftFamily_eq_weakHalfLift_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 q p hStrong hWeak f
  have hCoEnergy : Q (W (I f)) = Q (TauCeti.Wkp.firstOrder 1 U) := congrArg Q hCo.symm
  have hGreen := referenceHarmonicLiftFamily_normalized_full_test_energy_Green
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p hStrong (harmonicLiftCompletion hF f) (S (T z))
  have hTrace := valueTraceL_contDiffSMulL τ0 m hM hm hgrad (T z)
  have hTracePair := congrArg (fun v : SphereL2 =>
    inner ℝ (referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p U) v) hTrace
  exact hE.trans (hProduct.trans (hCoEnergy.trans (hGreen.trans hTracePair)))

theorem sphereSobolevDualPairing_referenceGaugeWeakConormal_high_flux
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (τ0 : UnitBallValueTrace) (q : ℝ) (p : R3 × ℝ)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,p)).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) (z : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) z
      (referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF (q,p)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) =
    ⟪sphereContinuousScalarMulL
        (smoothSphereValue (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg (q,p)))
        (referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p
          (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p (harmonicLiftCompletion hF f))),
      τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)⟫_ℝ :=
  (sphereSobolevDualPairing_referenceGaugeWeakConormal_high_Green
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO τ0 q p hStrong hWeak f z).trans
      (inner_sphereContinuousScalarMulL_left _ _ _).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceGaugeWeakConormal_high_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceGaugeWeakConormal_high_flux
