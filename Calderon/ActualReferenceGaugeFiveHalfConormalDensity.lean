import Calderon.NativePrincipalFiveHalfConormalDensity
import Calderon.ActualReferenceGaugePrincipalFamily

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH4FiveHalfCoefficientConormalTrace

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- Higher angular density of the same physical gauge conormal construction. -/
def referencePhysicalGaugeConormalDensityFiveHalf
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (E : (ℝ × (R3 × ℝ)) → BallSobolev 4) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (5/2 : ℝ) :=
  nativePrincipalFiveHalfConormalDensity hcalc hF hO hD τ0 p.2.2
    (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 4 p) (E p)

include hg hData in
/-- Exact inclusion identifies the high density with the old physical gauge
density on the lowered version of the same datum. -/
theorem sphereSobolevInclusionL_referencePhysicalGaugeConormalDensityFiveHalf
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (E : (ℝ × (R3 × ℝ)) → BallSobolev 4) (p : ℝ × (R3 × ℝ)) :
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (referencePhysicalGaugeConormalDensityFiveHalf g hg L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 E p) =
    referencePhysicalGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 (fun q => TauCeti.Wkp.lowerOrder 3 (E q)) p := by
  let F4 := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 4 p
  let F3 := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p
  have hFG (i j : Fin 3) : coefficientValue 4 (F4 i j) = coefficientValue 3 (F3 i j) :=
    (coefficientValue_referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 4 p i j).trans
      (coefficientValue_referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p i j).symm
  have hi4 := referencePhysicalGauge_fullPrincipal_restriction_isInvertible
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 2 p
  have hi3 := referencePhysicalGauge_fullPrincipal_restriction_isInvertible
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 1 p
  have hCore : sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (nativePrincipalFiveHalfConormalDensity hcalc hF hO hD τ0 p.2.2 F4 (E p)) =
      nativePrincipalHarmonicConormalDensity hcalc hF hO hD τ0 p.2.2 F3
        (TauCeti.Wkp.lowerOrder 3 (E p)) :=
    sphereSobolevInclusionL_nativePrincipalFiveHalfConormalDensity
      hcalc hF hO hD τ0 p.2.2 F4 F3 hFG hi4 hi3 (E p)
  simpa only [referencePhysicalGaugeConormalDensityFiveHalf,
    referencePhysicalGaugeConormalDensity,F4,F3] using hCore

include hg hData in
theorem contDiff_referencePhysicalGauge_nativeFiveHalfConormal
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (fun p => nativeFiveHalfCoefficientConormalTraceL
      hcalc hF hO hD τ0
        (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 4 p)) := by
  unfold nativeFiveHalfCoefficientConormalTraceL
  refine ContDiff.sum fun i _ => ?_
  refine ContDiff.sum fun j _ => ?_
  have hm : ContDiff ℝ ∞ (fun p => coefficientMultiplier hcalc 3
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 4 p i j)) := by
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc 3
      (fun v => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H v i j)
      (contDiff_pi.mp (contDiff_pi.mp
        (contDiff_referencePhysicalGaugeCompactPrincipalCoefficient g hg L y0 Φ B ε C ρ H a w hData) i) j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun p z hz => by
        rw [referencePhysicalGaugeCompactPrincipalCoefficient_eq_zero_outside g L Φ H p z hz]
        rfl)
  exact contDiff_const.clm_comp (contDiff_const.clm_comp (hm.clm_comp contDiff_const))

include hg hData in
theorem contDiffOn_referencePhysicalGaugeConormalDensityFiveHalf
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (E : (ℝ × (R3 × ℝ)) → BallSobolev 4) (Q : Set (ℝ × (R3 × ℝ)))
    (hE : ContDiffOn ℝ ∞ E Q) :
    ContDiffOn ℝ ∞ (referencePhysicalGaugeConormalDensityFiveHalf
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 E) Q := by
  let F := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 4
  let A := fun p => ordinaryPrincipalL hcalc 2 (F p)
  have hA : ContDiff ℝ ∞ A :=
    contDiff_referencePhysicalGauge_fullPrincipal g hg L y0 Φ B ε C ρ H a w hData hcalc 2
  have hi : ∀ p ∈ Q, ((A p).comp (strongDirichletSubmodule 2).toSubmodule.subtypeL).IsInvertible :=
    fun p _ => referencePhysicalGauge_fullPrincipal_restriction_isInvertible
      g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 2 p
  have hP := contDiffOn_strongHarmonicProjectionL 2 A Q hA.contDiffOn hi
  have hC := (contDiff_referencePhysicalGauge_nativeFiveHalfConormal
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn (s := Q)
  have hr : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => p.2.2) := contDiff_snd.snd
  exact (hr.contDiffOn.mul contDiffOn_const).smul
    (hC.clm_apply ((hP.clm_apply hE).sub hE))

end OAI.AnisotropicCalderon.ConnectionError
