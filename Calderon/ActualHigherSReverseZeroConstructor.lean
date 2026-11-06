import Calderon.ActualHigherSLinearZero
import Calderon.ActualHigherSAdjointLeadingCoordinate

/-! Reverse-only exact native constructor/profile/density transport.
Author source, conditional until focused/native/closure checks. No zero split. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSReverseZeroConstructor
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth ActualHigherSLinearZero
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
attribute [local irreducible] ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient
  ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow

theorem native_adjoint_profile_density_congr
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (x : R3)
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half)
    (Eh Eh' : Fin 3 → R3 → Hi →L[ℝ] Half)
    (El El' : Fin 3 → Half →L[ℝ] Neg)
    (d1 d1' d2 d2' : Fin 3 → Fin 3 → ℝ)
    (hEh : Eh=Eh') (hEl : El=El') (hd1 : d1=d1') (hd2 : d2=d2') :
    ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient r Q b d1 d2
      (ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q R Eh El x)
      (fun i => Eh i x) El Alo Ahi =
    ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient r Q b d1' d2'
      (ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q R Eh' El' x)
      (fun i => Eh' i x) El' Alo Ahi := by
  cases hEh
  cases hEl
  cases hd1
  cases hd2
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
local notation "BH" => ActualFullEGainedAssembly.orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => ActualFullEGainedAssembly.orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => ActualHigherSAdjointCoefficientExtraction.reverseProfileHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => ActualHigherSAdjointCoefficientExtraction.reverseProfileLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CT" => ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

theorem actual_adjoint_source_raw (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    CT g2 dr Ar p q x =
    ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient (referenceRadius dr Ar p L x)
      (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (fun i => ActualNormalizedSecondMetricDrift.normalizedSecondDriftFrameJoint g g2 L i (q,x))
      (fun i j => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
        (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x /
          referenceDensityFamily g L (q,x))
      (fun i j => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q j
        (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x /
          referenceDensityFamily g L (q,x))
      (ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q (referenceRadius dr Ar p L)
        (RH dr Ar p q) (RL dr Ar p q x) x)
      (fun i => RH dr Ar p q i x) (RL dr Ar p q x)
      (loweringLow hF hO hD) (loweringHigh hF hO hD) := by
  unfold ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient
  rfl

theorem actual_whole_reverseProfileHigh_eq_ordered (dr Ar : ℝ) (p : ℕ) (q : ℝ) :
    RH dr Ar p q = fun i y => BH i ((Tq dr Ar p q) y) := by
  funext i y
  exact ActualHigherSAdjointLeadingCoordinate.reverseEHigh_eq_ordered
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i ((Tq dr Ar p q) y)

theorem actual_whole_reverseProfileLow_eq_ordered (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    RL dr Ar p q x = fun j => BL j ((Tq dr Ar p q) x) := by
  funext j
  exact ActualHigherSAdjointLeadingCoordinate.reverseELow_eq_ordered
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j ((Tq dr Ar p q) x)

theorem actual_first_density_array_eq (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    (fun i j : Fin 3 => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
      (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x /
        referenceDensityFamily g L (q,x)) =
    (fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j i x) := by
  rfl

theorem actual_second_density_array_eq (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    (fun i j : Fin 3 => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q j
      (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x /
        referenceDensityFamily g L (q,x)) =
    (fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j j x) := by
  rfl

attribute [local irreducible] ActualHigherSAdjointCoefficientExtraction.reverseProfileHigh
  ActualHigherSAdjointCoefficientExtraction.reverseProfileLow ActualFullEGainedAssembly.orderedReverseHigh ActualFullEGainedAssembly.orderedReverseLow
  referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint
  normalizedSecondCoefficientDerivative

theorem actual_adjoint_source_constructor
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) :
    CT g2 dr Ar p q x = ActualHigherSAdjointCoefficientExtraction.adjointZeroCoefficient
      (referenceRadius dr Ar p L x) (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x))
      (fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j i x)
      (fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j j x)
      (ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow g L q (referenceRadius dr Ar p L)
        (fun i y => BH i ((Tq dr Ar p q) y)) (fun j => BL j ((Tq dr Ar p q) x)) x)
      (fun i => BH i ((Tq dr Ar p q) x)) (fun j => BL j ((Tq dr Ar p q) x))
      (loweringLow hF hO hD) (loweringHigh hF hO hD) := by
  have hRaw := actual_adjoint_source_raw
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x
  have hHigh := actual_whole_reverseProfileHigh_eq_ordered
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 dr Ar p q
  have hLow := actual_whole_reverseProfileLow_eq_ordered
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 dr Ar p q x
  have hDensity1 := actual_first_density_array_eq g L g2 dr Ar p q x
  have hDensity2 := actual_second_density_array_eq g L g2 dr Ar p q x
  have hProfiles := native_adjoint_profile_density_congr g L q (referenceRadius dr Ar p L) x
    (referenceRadius dr Ar p L x) (referenceDensityPrincipalFrameCoefficient g g2 L q x)
    (fun i => ActualNormalizedSecondMetricDrift.normalizedSecondDriftFrameJoint g g2 L i (q,x))
    (loweringLow hF hO hD) (loweringHigh hF hO hD)
    (RH dr Ar p q) (fun i y => BH i ((Tq dr Ar p q) y))
    (RL dr Ar p q x) (fun j => BL j ((Tq dr Ar p q) x))
    (fun i j => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
      (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x /
        referenceDensityFamily g L (q,x))
    (fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j i x)
    (fun i j => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q j
      (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x /
        referenceDensityFamily g L (q,x))
    (fun i j => normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j j x)
    hHigh hLow hDensity1 hDensity2
  exact hRaw.trans hProfiles
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSReverseZeroConstructor
