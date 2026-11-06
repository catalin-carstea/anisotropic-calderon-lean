import Calderon.ActualTSFullLowerAssembly
import Calderon.ActualTSZeroLiteralIntegral

/-! Exact binding of the zero/zero row to the original full lower T/S cross.
D10 and D01 are not estimated here; grouped integrals only. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSLowerZeroZeroBinding
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualHigherSFormation ActualTFirstPhysicalDictionary ActualSFirstPhysicalDictionary
  ActualHigherSZeroPhysicalGraph ActualTSFullLowerAssembly ActualTSZeroLiteralPointwise
  ActualTSZeroLiteralIntegral ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth
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

local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "UF" => higherSInput hO hD
local notation "S0" => nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs
local notation "Sd0" => nativeAdjointZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs
local notation "S1" => referenceSFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Sd1" => referenceSAdjointFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Lower" => lowerPhysicalCross g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs
local notation "D00" => originalZeroZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

/-- Original first/zero row, including its exact factor four and raw adjoint. -/
def originalFirstZeroCrossDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*(⟪KL (referenceFirstHalf hO hD hF g L q (UF F) x),
          KL (S0 g2 dr Ar p hdr hAr q F x)⟫_ℝ-
      ⟪KL (referenceAdjointFirstHalf hO hD hF g L q (UF F) x),
          KL (Sd0 g2 dr Ar p hdr hAr q F x)⟫_ℝ)

/-- Original zero/first row; no room or cap premise is added. -/
def originalZeroFirstCrossDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*(⟪(nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x,
          KL (S1 g2 dr Ar p q (UF F) x)⟫_ℝ-
      ⟪(nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x,
          KL (Sd1 g2 dr Ar p q (UF F) x)⟫_ℝ)

local notation "D10" => originalFirstZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "D01" => originalZeroFirstCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Global literal decomposition, without integrating either row. -/
theorem original_lower_cross_eq_three_signed_rows (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    4*Lower g2 dr Ar p hdr hAr q F x =
      D10 g2 dr Ar p hdr hAr q F x+D01 g2 dr Ar p hdr hAr q F x+
      D00 g2 dr Ar p hdr hAr q F x := by
  unfold lowerPhysicalCross originalFirstZeroCrossDensity
    originalZeroFirstCrossDensity originalZeroZeroCrossDensity
  ring

/-- The grouped residual is the original lower cross less its exact first two rows. -/
def originalLowerZeroZeroResidual (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*Lower g2 dr Ar p hdr hAr q F x-
    D10 g2 dr Ar p hdr hAr q F x-D01 g2 dr Ar p hdr hAr q F x
local notation "R00" => originalLowerZeroZeroResidual
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

theorem original_lower_residual_eq_zero_zero (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    R00 g2 dr Ar p hdr hAr q F x=D00 g2 dr Ar p hdr hAr q F x := by
  unfold originalLowerZeroZeroResidual
  rw [original_lower_cross_eq_three_signed_rows]
  ring

attribute [local irreducible] originalZeroZeroCrossDensity finiteCoreReferenceProfileEnergy
/-- The original full-lower residual has the same genuine integral estimate as literal L00. -/
theorem exists_original_lower_zero_zero_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Czero etaZero : ℝ, 0 < Czero ∧ 0 < etaZero ∧ etaZero ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaZero →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*R00 g2 dr Ar p hdr hAr q F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*R00 g2 dr Ar p hdr hAr q F x| ≤
        Czero*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨Czero,etaZero,hCzero,hetaZero,hetaZero0,hBound⟩ :=
    exists_original_zero_zero_integral_bound hF hO hD g L y0 Φ B ε C ρ H a w hData
      hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  refine ⟨Czero,etaZero,hCzero,hetaZero,hetaZero0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have h := hBound q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  simpa only [original_lower_residual_eq_zero_zero] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSLowerZeroZeroBinding
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSLowerZeroZeroBinding.original_lower_cross_eq_three_signed_rows
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSLowerZeroZeroBinding.original_lower_residual_eq_zero_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSLowerZeroZeroBinding.exists_original_lower_zero_zero_integral_bound
