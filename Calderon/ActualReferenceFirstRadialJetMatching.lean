import Calderon.ActualNativeFirstVariationOperatorRadialFactor
import Calderon.ActualReferenceSharpMidpointRadialCoefficientCore
import Calderon.SharpRadialCoefficientOperators
import Calderon.ActualFirstCorrectionSobolevFamilies

/-! Upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-chosen-midpoint-firstjet-matching-v025.md. Chosen actual midpoint
radial firstjet equals the existing bounded finite-band native F0. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma radialFirstDerivative_referenceSharpMidpointRadialTrace_single_radialFactor
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (u : harmonicSphereSubspace k) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0)
      (sphereSobolevSingleL 1 k u) = sphereSobolevZeroEquiv hO hD
        (radialDriftTraceL hF hO hD (referenceCenterDrift g L q y) (u : SphereL2)) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have he := radialFirstDerivative_referenceSharpMidpointRadialTrace_on_high_data
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y hp
      (sphereSobolevSingleL (3/2 : ℝ) k u)
  rw [sphereSobolevInclusionL_single,harmonicLiftCompletion_sphereSobolevSingle hF hO] at he
  let p : harmonicHomogeneous k :=
    ⟨harmonicPolynomialRepresentativeL hF k u,harmonicPolynomialRepresentative_mem hF k u⟩
  have hz := radialFirstDerivative_referenceNativeRadialTrace_harmonic_polynomial_radialFactor
    g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0 hF hO hD q hq y hy k p
  have hu : polynomialSphereL2 p = (u : SphereL2) :=
    polynomialSphereL2_harmonicPolynomialRepresentative hF k u
  have hz' := hz.trans (congrArg
    (radialDriftTraceL hF hO hD (referenceCenterDrift g L q y)) hu)
  exact he.trans (congrArg (sphereSobolevZeroEquiv hO hD) hz')

lemma radialFirstDerivative_referenceSharpMidpointRadialTrace_eq_firstDrift_radialFactor
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0) =
      sphereSobolevFirstRadialDriftL hF hO hD (referenceCenterDrift g L q y) := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k u
  exact (radialFirstDerivative_referenceSharpMidpointRadialTrace_single_radialFactor
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy k u).trans
    (sphereSobolevFirstRadialDriftL_single hF hO hD (referenceCenterDrift g L q y) k u).symm

lemma sphereSobolevFirstRadialDriftL_eq_radialDrift_inclusion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (d : R3) :
    sphereSobolevFirstRadialDriftL hF hO hD d =
      (sphereSobolevInclusionL 1 0 (by norm_num)).comp
        (sphereSobolevRadialDriftL hF hO hD 1 d) := by
  apply ContinuousLinearMap.ext
  intro u
  let I := sphereSobolevInclusionL 1 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let v := Z.symm (I u)
  have hv : Z v = I u := Z.apply_symm_apply (I u)
  have hR := sphereSobolevRadialDriftL_zeroEquiv hF hO hD d v
  have hI := sphereSobolevInclusionL_radialDrift hF hO hD 1 0 (by norm_num) d u
  change Z (radialDriftTraceL hF hO hD d v) = I (sphereSobolevRadialDriftL hF hO hD 1 d u)
  exact hR.symm.trans ((congrArg (sphereSobolevRadialDriftL hF hO hD 0 d) hv).trans hI.symm)

lemma radialFirstDerivative_referenceSharpMidpointRadialTrace_eq_nativeFirstCorrection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0) =
      (sphereSobolevInclusionL 1 0 (by norm_num)).comp
        (sphereSobolevRadialDriftL hF hO hD 1 (referenceCenterDrift g L q y)) :=
  (radialFirstDerivative_referenceSharpMidpointRadialTrace_eq_firstDrift_radialFactor
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy).trans
    (sphereSobolevFirstRadialDriftL_eq_radialDrift_inclusion hF hO hD (referenceCenterDrift g L q y))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceSharpMidpointRadialTrace_single_radialFactor
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceSharpMidpointRadialTrace_eq_firstDrift_radialFactor
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevFirstRadialDriftL_eq_radialDrift_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceSharpMidpointRadialTrace_eq_nativeFirstCorrection
