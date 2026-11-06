import Calderon.ActualHigherSCoefficientExtraction

/-! Forward-only exact native source constructor transport. No reverse or zero split. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSForwardZeroConstructor
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
attribute [local irreducible] ActualHigherSCoefficientExtraction.zeroCoefficient
  ActualHigherSCoefficientExtraction.secondZeroRow

theorem native_zero_profile_congr
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (x : R3)
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half)
    (Eh Eh' : Fin 3 → R3 → Hi →L[ℝ] Half)
    (El El' : Fin 3 → Half →L[ℝ] Neg) (hEh : Eh=Eh') (hEl : El=El') :
    ActualHigherSCoefficientExtraction.zeroCoefficient r Q b
      (ActualHigherSCoefficientExtraction.secondZeroRow g L q R Eh El x)
      (fun j => Eh j x) El Alo Ahi =
    ActualHigherSCoefficientExtraction.zeroCoefficient r Q b
      (ActualHigherSCoefficientExtraction.secondZeroRow g L q R Eh' El' x)
      (fun j => Eh' j x) El' Alo Ahi := by
  cases hEh
  cases hEl
  rfl

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PH" => ActualHigherSCoefficientExtraction.profileHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PL" => ActualHigherSCoefficientExtraction.profileLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

theorem actual_zero_source_raw (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    CZ g2 dr Ar p q x =
    ActualHigherSCoefficientExtraction.zeroCoefficient (referenceRadius dr Ar p L x)
      (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
      (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x))
      (ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius dr Ar p L)
        (PH dr Ar p q) (PL dr Ar p q x) x)
      (fun j => PH dr Ar p q j x) (PL dr Ar p q x)
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ))
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)) := by
  unfold ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  rfl

theorem actual_whole_profileHigh_eq_pullback (dr Ar : ℝ) (p : ℕ) (q : ℝ) :
    PH dr Ar p q = fun j y => EH j ((Tq dr Ar p q) y) := by
  rfl

attribute [local irreducible] ActualHigherSCoefficientExtraction.profileHigh
  ActualHigherSCoefficientExtraction.profileLow canonicalHigh
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint

theorem actual_zero_source_constructor
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (Low : Fin 3 → Half →L[ℝ] Neg)
    (hLow : ActualHigherSCoefficientExtraction.profileLow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 dr Ar p q x=Low) :
    CZ g2 dr Ar p q x = ActualHigherSCoefficientExtraction.zeroCoefficient
      (referenceRadius dr Ar p L x) (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x))
      (ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius dr Ar p L)
        (fun j y => EH j ((Tq dr Ar p q) y)) Low x)
      (fun j => EH j ((Tq dr Ar p q) x)) Low
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ))
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)) := by
  have hRaw := actual_zero_source_raw
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x
  have hHigh := actual_whole_profileHigh_eq_pullback
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 dr Ar p q
  have hProfiles := native_zero_profile_congr g L q (referenceRadius dr Ar p L) x
    (referenceRadius dr Ar p L x)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
    (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x))
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ))
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ))
    (PH dr Ar p q) (fun j y => EH j ((Tq dr Ar p q) y))
    (PL dr Ar p q x) Low hHigh hLow
  exact hRaw.trans hProfiles
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSForwardZeroConstructor
