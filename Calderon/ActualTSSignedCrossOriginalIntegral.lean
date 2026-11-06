import Calderon.ActualTSSignedCrossAssembly
import Calderon.ActualTSZeroFirstOriginalEnergy

/-! Original signed T/S cross integral. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSignedCrossOriginalIntegral
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  PrincipalCommutator ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (ε C ρ : ℝ) (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)




open ActualTSSignedCrossAssembly ActualTSFullLowerAssembly ActualTSLowerZeroZeroBinding
local notation "TSD" => originalSignedTSPhysicalDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "PB" => OriginalProfileIntegralBound
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "Lower" => lowerPhysicalCross
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs

/-- Original lower T/S integral bound, using the D01 estimate. -/
theorem exists_original_lower_TS_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    PB (fun q dr Ar p hdr hAr F x => 4*Lower g2 dr Ar p hdr hAr q F x) :=
  original_lower_TS_integral_bound_of_D01
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
    (exists_original_zero_first_integral_bound
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2)

/-- Full literal original signed T/S genuine integrability and original energy. -/
theorem exists_original_signed_TS_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cts etaTS : ℝ, 0 < Cts ∧ 0 < etaTS ∧ etaTS ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaTS →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*TSD g2 dr Ar p hdr hAr q F x) ∧
        |∫ x, referenceDensityFamily g L (q,x)*TSD g2 dr Ar p hdr hAr q F x| ≤
          Cts*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
            hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x :=
  original_signed_TS_integral_bound_of_D01
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
    (exists_original_zero_first_integral_bound
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSignedCrossOriginalIntegral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSignedCrossOriginalIntegral.exists_original_lower_TS_integral_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSSignedCrossOriginalIntegral.exists_original_signed_TS_integral_bound
