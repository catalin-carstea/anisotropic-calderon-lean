import Calderon.NativePrincipalCutoffCommutator
import Calderon.NativeConormalCutoffInvariance
import Calderon.ActualHalfGaugeConormalFamily
import Calderon.ActualHalfGaugeCollarForcingSupport
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap NativePolynomialBulkMoments SphereHarmonic

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0)
    (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η)


include hg hData hcalc in
theorem referencePhysicalHalfGaugeCollarHighCorrection_lowerOrder
    (hreg : FixedDirichletRegularity) (a0 : ℝ)
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) a0, ζ z = 1)
    (hηZero : ∀ z ∈ closedBall (0 : R3) a0, η z = 0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    TauCeti.Wkp.lowerOrder 2
      (referencePhysicalHalfGaugeCollarHighCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη (q,(y,r)) : BallSobolev 3) =
      coefficientMultiplier hcalc 2 (nativeUnitBallCutoffJets 3 η hη)
        (referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r)) : BallSobolev 2) := by
  have hFields : coefficientMatrixField 2 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) = coefficientMatrixField 3 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 (q,(y,r))) := by
    rw [coefficientMatrixField_referencePhysicalGaugeCoefficientJets,
      coefficientMatrixField_referencePhysicalGaugeCoefficientJets]
  have hZeroAE : ∀ᵐ z ∂(volume : Measure R3).restrict ballOpens,
      η z * (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z = 0 := by
    simpa only [TauCeti.Wkp.value_zero] using
      (referencePhysicalHalfGaugeCollarForcing_cutoff_ae_zero g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero
        a0 η hθOne hζOne hηZero q hq y hy r hr)
  have hCut : coefficientMultiplier hcalc 0
      (coefficientRepackedJets 3 1 (nativeUnitBallCutoffJets 3 η hη)) (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) = 0 :=
    nativeUnitBallCutoff_forcing_eq_zero_of_ae hcalc η hη _ hZeroAE
  have h := nativePrincipal_inverse_cutoff_gain_coherence hcalc (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 (q,(y,r))) hFields
    (nativeUnitBallCutoffJets 3 η hη)
    (referencePhysicalGaugePrincipal_isInvertible g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 0 (q,(y,r)))
    (referencePhysicalGaugePrincipal_isInvertible g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 1 (q,(y,r)))
    (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) hCut
  exact h

include hg hData hcalc in
theorem sphereSobolevInclusionL_zero_referencePhysicalHalfGaugeConormalDensity
    (hreg : FixedDirichletRegularity) (a0 : ℝ)
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) a0, ζ z = 1)
    (hηZero : ∀ z ∈ closedBall (0 : R3) a0, η z = 0)
    (hηSphere : ∀ x : UnitSphere, η x.val = 1)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
      (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 (q,(y,r))) =
      sphereSurfaceMass • sphereSobolevZeroEquiv hO hD
        (ordinaryConormalTraceL hcalc τ0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r)))
          (referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r)) : BallSobolev 2)) := by
  have hEntries : ∀ i j, coefficientValue 3 ((referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 (q,(y,r))) i j) = coefficientValue 2 ((referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) i j) := by
    intro i j
    rw [coefficientValue_referencePhysicalGaugeCoefficientJets,
      coefficientValue_referencePhysicalGaugeCoefficientJets]
  have hOne : ∀ x : UnitSphere, coefficientValue 3 (nativeUnitBallCutoffJets 3 η hη) x.val = 1 := by
    intro x
    have hx : x.val ∈ closedBall (0 : R3) 1 := by
      have hn : ‖x.val‖ = 1 := by simpa only [UnitSphere, mem_sphere,dist_zero_right] using x.property
      simpa only [mem_closedBall,dist_zero_right,hn] using (le_refl (1 : ℝ))
    rw [coefficientValue_nativeUnitBallCutoffJets]
    change unitBallSmoothCutoff x.val * η x.val = 1
    rw [(unitBallSmoothCutoff_eventuallyEq_one hx).eq_of_nhds,hηSphere x,one_mul]
  have hLower := referencePhysicalHalfGaugeCollarHighCorrection_lowerOrder g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη
    hreg a0 hθOne hζOne hηZero q hq y hy r hr
  have hTrace := sphereSobolevInclusionL_zero_highConormal_eq_uncut_low
    hcalc hF hO hD τ0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 (q,(y,r))) (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) hEntries (nativeUnitBallCutoffJets 3 η hη) hOne
    (referencePhysicalHalfGaugeCollarHighCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη (q,(y,r)) : BallSobolev 3) (referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) hLower
  change sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
    (sphereSurfaceMass • NativeH3CoefficientConormalTrace.nativeThreeHalfCoefficientConormalTraceL
      hcalc hF hO hD τ0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 (q,(y,r))) (referencePhysicalHalfGaugeCollarHighCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη (q,(y,r)) : BallSobolev 3)) = _
  rw [map_smul,hTrace]

end OAI.AnisotropicCalderon.ConnectionError
