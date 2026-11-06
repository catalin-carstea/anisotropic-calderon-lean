import Calderon.ActualHalfGaugeCollarForcing
import Calderon.ActualReferenceGaugeCutoffFamily
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap NativePolynomialBulkMoments

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hcalc : FixedSobolevCalculus)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0)

open SphereHarmonic

variable (η : R3 → ℝ) (hη : ContDiff ℝ ∞ η)

def referencePhysicalHalfGaugeCollarHighCorrection (p : ℝ × (R3 × ℝ)) : StrongDirichletSpace 1 :=
  (strongDirichletOperator hcalc 1 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p)).inverse
    (referencePhysicalGaugeCutoffCommutatorL g hg L y0 Φ B ε C ρ H a w hData hcalc η hη p (referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero p : BallSobolev 2))

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referencePhysicalHalfGaugeConormalDensity (p : ℝ × (R3 × ℝ)) : SphereSobolev (3/2 : ℝ) :=
  sphereSurfaceMass • NativeH3CoefficientConormalTrace.nativeThreeHalfCoefficientConormalTraceL
    hcalc hF hO hD τ0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p) (referencePhysicalHalfGaugeCollarHighCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη p : BallSobolev 3)

include hg hData hcalc in
theorem contDiff_referencePhysicalGauge_strongInverse (hreg : FixedDirichletRegularity) (s : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => (strongDirichletOperator hcalc s
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData (s+2) p)).inverse) := by
  have hOp : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => strongDirichletOperator hcalc s
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData (s+2) p)) := by
    have hEq : (fun p : ℝ × (R3 × ℝ) => strongDirichletOperator hcalc s
        (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData (s+2) p)) =
        (fun p => (ordinaryPrincipalL hcalc s (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData (s+2) p)).comp
          (strongDirichletSubmodule s).toSubmodule.subtypeL) :=
      funext (fun p => (ordinaryPrincipalL_restriction hcalc s
        (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData (s+2) p)).symm)
    rw [hEq]
    exact (contDiff_referencePhysicalGauge_fullPrincipal g hg L y0 Φ B ε C ρ H a w hData hcalc s).clm_comp contDiff_const
  exact contDiffOn_univ.mp (contDiffOn_banachInverseFamily _ Set.univ hOp.contDiffOn
    (fun p _ => referencePhysicalGaugePrincipal_isInvertible g hg L y0 Φ B ε C ρ H a w hData hcalc hreg s p))
include hg hData hcalc in
theorem contDiff_referencePhysicalHalfGaugeCollarHighCorrection (hreg : FixedDirichletRegularity) :
    ContDiff ℝ ∞ (referencePhysicalHalfGaugeCollarHighCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη) := by
  have hU : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => (referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero p : BallSobolev 2)) :=
    (strongDirichletSubmodule 0).toSubmodule.subtypeL.contDiff.comp
      (contDiff_referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero hreg)
  exact (contDiff_referencePhysicalGauge_strongInverse g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 1).clm_apply
    ((contDiff_referencePhysicalGaugeCutoffCommutatorL g hg L y0 Φ B ε C ρ H a w hData hcalc η hη).clm_apply hU)
include hg hData hcalc in
theorem referencePhysicalHalfGaugeCollarHighCorrection_equation (hreg : FixedDirichletRegularity)
    (p : ℝ × (R3 × ℝ)) :
    ordinaryPrincipalL hcalc 1 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p) (referencePhysicalHalfGaugeCollarHighCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη p : BallSobolev 3) =
      referencePhysicalGaugeCutoffCommutatorL g hg L y0 Φ B ε C ρ H a w hData hcalc η hη p (referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero p : BallSobolev 2) := by
  change ((ordinaryPrincipalL hcalc 1 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p)).comp
    (strongDirichletSubmodule 1).toSubmodule.subtypeL)
      ((strongDirichletOperator hcalc 1 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 3 p)).inverse
        (referencePhysicalGaugeCutoffCommutatorL g hg L y0 Φ B ε C ρ H a w hData hcalc η hη p
          (referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero p : BallSobolev 2))) = _
  rw [ordinaryPrincipalL_restriction]
  exact (referencePhysicalGaugePrincipal_isInvertible g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 1 p).self_apply_inverse _
include hg hData hcalc in
theorem contDiff_referencePhysicalHalfGaugeConormalDensity (hreg : FixedDirichletRegularity) :
    ContDiff ℝ ∞ (referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0) := by
  have hZ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => (referencePhysicalHalfGaugeCollarHighCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη p : BallSobolev 3)) :=
    (strongDirichletSubmodule 1).toSubmodule.subtypeL.contDiff.comp
      (contDiff_referencePhysicalHalfGaugeCollarHighCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hreg)
  have hMass : ContDiff ℝ ∞ (fun _ : ℝ × (R3 × ℝ) => sphereSurfaceMass) := contDiff_const
  exact hMass.smul ((contDiff_referencePhysicalGauge_nativeThreeHalfConormal
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).clm_apply hZ)
include hg hData hcalc in
theorem exists_compact_uniform_referencePhysicalHalfGaugeConormalDensity_bound
    (hreg : FixedDirichletRegularity) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ p ∈ K, ‖referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 p‖ ≤ C0 := by
  obtain ⟨C0,hC0⟩ := hK.exists_bound_of_continuousOn
    (contDiff_referencePhysicalHalfGaugeConormalDensity g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero η hη hF hO hD τ0 hreg).continuous.continuousOn
  exact ⟨max C0 1,le_max_right _ _,fun p hp => (hC0 p hp).trans (le_max_left _ _)⟩
end OAI.AnisotropicCalderon.ConnectionError
