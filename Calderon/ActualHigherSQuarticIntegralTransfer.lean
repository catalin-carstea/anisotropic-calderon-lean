import Calderon.ActualHigherSOriginalDataCommonFirstWordRoom
import Calderon.ActualHigherSQuadraticZeroQuartic
import Calderon.ActualHigherSQuarticBound
import Calderon.ActualHigherSLinearZeroScalarCaps
import Calderon.ActualLowerSSelfFormation
import Calderon.ActualHigherSIntegratedPairing
import Calderon.FixedParameterProfilePullback
import Calderon.ActualHigherSZeroWordCoefficientBound
import Calderon.ActualHigherSQuadraticZeroQuarticRegularity
import Calderon.ActualHigherSQuadraticZeroQuarticRowBound
import Calderon.ActualHigherSPairingNormDiagnostic

/-! Complete actual density-weighted integral transfer, boundary E. The final
original theorem must prove its internal square/energy integrabilities, actual
support facts and pointwise estimate from native data and complete C/D producers.
No new final premise, norm or analytic callback is licensed. Uncompiled; original
source/body/API/owner/norm/energy/germ/literature37/model holds remain. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuarticFactorization
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
  ActualHigherSQuadraticZeroQuartic ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds ReferenceWeightedApproximation FixedParameterProfilePullback
  ActualScalarPrincipalAdjoint SpectralWeightedGraph SectionFiveErrorForms SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GG" => fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  Room hreg data.Gcoord data.GN data.δ0 data.germs
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "RD" => ActualCommonFirstWordQuadraticAdjoint.revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "WC" => actualWordCoefficient g L

local notation "VA" => actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "QR" => quarticWordRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- Complete integral transfer for the actual original fields and energy. -/
lemma integral_defect_le_reference_energy (hL : 0 < L) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (hp : 1 ≤ p) (q : ℝ)
    (Cquart eta : ℝ) (hCquart : 0 < Cquart) (heta : 0 ≤ eta)
    (K : Set R3) (F : smoothCompactFiniteSphereCore hO hD)
    (hsupp : tsupport F.val ⊆ K)
    (hZS : tsupport (Z2 g2 dr Ar p q F) ⊆ tsupport F.val)
    (hTS : tsupport (T2 g2 dr Ar p q F) ⊆ tsupport F.val)
    (hIZ : Integrable (fun x => referenceDensityFamily g L (q,x)*‖KL (Z2 g2 dr Ar p q F x)‖^2))
    (hIT : Integrable (fun x => referenceDensityFamily g L (q,x)*‖KL (T2 g2 dr Ar p q F x)‖^2))
    (hPoint : ∀ x ∈ K,
      |‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2| ≤
        Cquart*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
          (actualReferenceBeta g L q dr Ar p x) F x)
    (hIE : Integrable (fun x => referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
      hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)) :
    |(∫ x, referenceDensityFamily g L (q,x)*‖KL (Z2 g2 dr Ar p q F x)‖^2) -
      (∫ x, referenceDensityFamily g L (q,x)*‖KL (T2 g2 dr Ar p q F x)‖^2)| ≤
      Cquart*eta*(∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) := by
  have hID : Integrable (fun x => referenceDensityFamily g L (q,x)*
      (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)) := by
    exact (hIZ.sub hIT).congr (Filter.Eventually.of_forall (fun x => by
      simp only [Pi.sub_apply, mul_sub]))
  have hWeighted (x : R3) :
      |referenceDensityFamily g L (q,x)*
        (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)| ≤
      (Cquart*eta)*(referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) := by
    have hmuPos := referenceDensityFamily_pos g hg L (q,x)
    by_cases hx : x ∈ K
    · rw [abs_mul, abs_of_pos hmuPos]
      calc
        _ ≤ referenceDensityFamily g L (q,x)*(Cquart*eta*finiteCoreReferenceProfileEnergy
            hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) :=
          mul_le_mul_of_nonneg_left (hPoint x hx) hmuPos.le
        _ = _ := by ring
    · have hZ0 : Z2 g2 dr Ar p q F x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp (hZS h)))
      have hT0 : T2 g2 dr Ar p q F x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp (hTS h)))
      have hDefect0 : ‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2 = 0 :=
        ActualHigherSZeroAtomTransport.sub_values_eq_sum_of_both_eq_zero
          (fun Z : Half => ‖KL Z‖^2) hZ0 hT0 (rfl : (0 : ℝ) = 0)
      have hWeighted0 : |referenceDensityFamily g L (q,x)*
          (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)| = 0 :=
        (congrArg (fun r : ℝ => |referenceDensityFamily g L (q,x)*r|) hDefect0).trans
          (by simp only [mul_zero, abs_zero])
      have hE := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q
        (actualReferenceBeta g L q dr Ar p x)
        (actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x).le F x
      exact hWeighted0.le.trans
        (mul_nonneg (mul_nonneg hCquart.le heta) (mul_nonneg hmuPos.le hE))
  have hIntegral :
      |∫ x, referenceDensityFamily g L (q,x)*
        (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)| ≤
      (Cquart*eta)*(∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) := by
    calc
      _ ≤ ∫ x, |referenceDensityFamily g L (q,x)*
          (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun x => referenceDensityFamily g L (q,x)*
            (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2))
      _ ≤ ∫ x, (Cquart*eta)*(referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) :=
        integral_mono hID.abs (hIE.const_mul _) hWeighted
      _ = _ := integral_const_mul _ _
  have hIntegralEq :
      (∫ x, referenceDensityFamily g L (q,x)*
        (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)) =
      (∫ x, referenceDensityFamily g L (q,x)*‖KL (Z2 g2 dr Ar p q F x)‖^2) -
        (∫ x, referenceDensityFamily g L (q,x)*‖KL (T2 g2 dr Ar p q F x)‖^2) := by
    simpa only [mul_sub] using integral_sub hIZ hIT
  rw [hIntegralEq] at hIntegral
  exact hIntegral

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuarticFactorization
