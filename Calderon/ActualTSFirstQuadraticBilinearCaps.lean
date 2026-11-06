import Calderon.ActualTSActualTriplePhysicalCaps
import Calderon.ActualTSFirstQuadraticScalarJets
import Calderon.ActualHigherSScalarCommutatorCoefficients
import Calderon.ActualHigherSZeroWordCoefficientProfileRegularity

/-! Original first-T/quadratic-S bilinear caps.
Uses the directional product budget and the actual physical room pullback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticBilinearCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation
  ActualTSTripleBilinearCoefficient

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
local notation "Coeff" => ActualTSActualTripleRoomCaps.TripleCoefficientSpace
attribute [local instance] ActualTSActualTripleRoomCaps.tripleCoefficientNormedGroup
  ActualTSActualTripleRoomCaps.tripleCoefficientNormedSpace
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
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d

local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0



open ActualTSActualTripleRoomCaps ActualTSActualTriplePhysicalCaps
  ActualTSFirstQuadraticScalarJets ActualHigherSMixedWordScalarJets
  ActualHigherSQuadraticZeroWords ActualHigherSQuadraticZeroQuarticBounds
  ActualHigherSScalarCommutatorCoefficients PrincipalCommutator
  SmoothMetricFrame MovingFrameConnection FixedParameterProfilePullback FixedParameterProfileBudgets
  ActualTSPrincipalCoefficients ActualTSPrincipalGreen ActualHigherSCoordinateWeightBounds
  ActualHigherSLeadingBracketGain ActualTSPrincipalPhysicalGreen ActualTSPrincipalAngularCaps
  ActualScalarPrincipalAdjoint ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ActualHigherSScalarCommutatorNativeForm ActualMixedAngularPairedGains
  ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
local notation "QC" => actualTripleCoefficient
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "Tq" => ActualHigherSFormation.higherSParam L

/-- Exactly the original weighted smoothness, value and coordinate derivative conclusions. -/
def WeightedTripleFirstCaps (A : R3 → Coeff) (x : R3) (C eta beta : ℝ) : Prop :=
  ContDiffAt ℝ ∞ A x ∧ ‖A x‖ ≤ C*eta ∧
    ∀ m : Fin 3, ‖directionalFDeriv (coordinateDirection m) A x‖ ≤ C*eta*beta

theorem weightedTripleFirstCaps_iff (A : R3 → Coeff) (x : R3) (C eta beta : ℝ) :
    WeightedTripleFirstCaps A x C eta beta ↔
      ContDiffAt ℝ ∞ A x ∧ ‖A x‖ ≤ C*eta ∧
        ∀ m : Fin 3, ‖directionalFDeriv (coordinateDirection m) A x‖ ≤ C*eta*beta := Iff.rfl

/-- The original frame/word weight multiplies the exact bounded triple, in its
original order. Its actual D10 instantiation sets a to raisingAtom i and b,c
to the two word atoms; no change to either scalar coefficient is made. -/
def weightedTripleCoefficient (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (i l : Fin 3) (z : ZeroWord) (a b c : AngularAtom) (x : R3) :
    Coeff :=
  firstQuadraticWordWeight g L g2 q dr Ar p i l z x • QC ((Tq dr Ar p q) x) a b c
local notation "WCoeff" => weightedTripleCoefficient
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

private lemma coordinate_cap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : R3 → V) (x : R3) (m : Fin 3) (B : ℝ) (h : ‖fderiv ℝ f x‖ ≤ B) :
    ‖directionalFDeriv (coordinateDirection m) f x‖ ≤ B := by
  calc
    _ ≤ ‖fderiv ℝ f x‖*‖coordinateDirection m‖ := (fderiv ℝ f x).le_opNorm _
    _ = ‖fderiv ℝ f x‖ := by rw [norm_coordinateDirection,mul_one]
    _ ≤ B := h

/-- Actual coefficient caps for the symmetric Green estimate. -/
theorem exists_actual_uniform_weighted_triple_first_caps
    (hL : 0 < L) {d : ℝ} (hd : 0 < d) (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cweight : ℝ, 0 < Cweight ∧ ∃ etaRoom : ℝ, 0 < etaRoom ∧ etaRoom ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaRoom →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ i l : Fin 3, ∀ z : ZeroWord, ∀ a b c : AngularAtom,
      WeightedTripleFirstCaps (WCoeff g2 q dr Ar p i l z a b c) x Cweight eta
        (actualReferenceBeta g L q dr Ar p x) := by
  obtain ⟨Cphys,hCphys,etaRoom,hEta,hEta1,hPhysical⟩ :=
    exists_actual_uniform_triple_physical_first_caps
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hd P
  obtain ⟨Cs,hCs,hScalar⟩ := exists_actual_first_quadratic_word_scalar_first_caps
    g hg L hL y0 ρ g2 hg2
  let frameWitness := exists_metricFrame_uniform_first_caps g hg L y0 ρ
  have hFrame := (Classical.choose_spec frameWitness).2
  let Cweight : ℝ := 2*Cs*Cphys+1
  have hCweight : 0 < Cweight := by dsimp only [Cweight]; positivity
  have hSC : 0 ≤ Cs*Cphys := mul_nonneg hCs.le hCphys.le
  have hC0 : Cs*Cphys ≤ Cweight := by dsimp only [Cweight]; nlinarith only [hSC]
  have hC1 : 2*Cs*Cphys ≤ Cweight := by dsimp only [Cweight]; linarith
  refine ⟨Cweight,hCweight,etaRoom,hEta,hEta1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom x hx hxBall hb hs i l z a b c
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  let s : R3 → ℝ := firstQuadraticWordWeight g L g2 q dr Ar p i l z
  let A : R3 → Coeff := fun y => QC ((Tq dr Ar p q) y) a b c
  have hJet := hScalar q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaRoom.trans hEta1)
    x hx hb hs i l z
  have hA := hPhysical q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom x hx hxBall hb hs a b c
  have hsSmooth : ContDiffAt ℝ ∞ s x := by
    unfold s firstQuadraticWordWeight
    exact ((hFrame q hq x hx i l).1.mul
      (contDiff_actualWordCoefficient_scalar g g2 hg hg2 L dr Ar p hdr hAr q z)).contDiffAt
  have hS0 : |s x| ≤ Cs*eta := hJet.value
  have hS1 (m : Fin 3) : |directionalFDeriv (coordinateDirection m) s x| ≤ Cs*eta*beta := by
    simpa only [Real.norm_eq_abs] using coordinate_cap s x m (Cs*eta*beta) hJet.derivative
  have hA1 (m : Fin 3) : ‖directionalFDeriv (coordinateDirection m) A x‖ ≤ Cphys :=
    coordinate_cap A x m Cphys hA.2.2
  have hBeta0 : 0 ≤ beta := zero_le_one.trans hb
  have hLift : (Cs*Cphys)*eta ≤ (Cs*Cphys)*eta*beta := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hb (mul_nonneg hSC heta)
  have hValue : ‖s x • A x‖ ≤ Cweight*eta := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (Cs*eta)*Cphys := mul_le_mul hS0 hA.2.1 (norm_nonneg _) (mul_nonneg hCs.le heta)
      _ = (Cs*Cphys)*eta := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC0 heta
  refine ⟨hsSmooth.smul hA.1,hValue,?_⟩
  intro m
  have hProd := product_first_jet_budget s A x (coordinateDirection m) hsSmooth hA.1
    (Cs*eta) (Cs*eta*beta) Cphys Cphys
    (by positivity) (by positivity) hCphys.le hCphys.le hS0 (hS1 m) hA.2.1 (hA1 m)
  calc
    _ ≤ (Cs*eta*beta)*Cphys+(Cs*eta)*Cphys := hProd.2
    _ = (Cs*Cphys)*eta*beta+(Cs*Cphys)*eta := by ring
    _ ≤ (2*Cs*Cphys)*eta*beta := by nlinarith only [hLift]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 heta) hBeta0

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticBilinearCaps
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticBilinearCaps.exists_actual_uniform_weighted_triple_first_caps

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticBilinearCaps.weightedTripleFirstCaps_iff
