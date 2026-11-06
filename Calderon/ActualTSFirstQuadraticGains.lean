import Calderon.ActualTSFirstQuadraticTriple
import Calderon.ActualTSFirstQuadraticScalarJets
import Calderon.ActualHigherSZeroScalarCommutatorForm

/-! Exact actual weighted gained remainder, before its grouped integral. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticGains
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation


local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
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
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d


open PrincipalCommutator ActualTSFirstQuadraticTriple ActualTSFirstQuadraticScalarJets
  ActualHigherSQuadraticZeroWords ActualHigherSScalarCommutatorForm
  ActualHigherSZeroScalarCommutatorForm
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- Both original gained terms, with original index order and coefficient.
The later physical decomposition SUBTRACTS this quantity. -/
def weightedOriginalTripleGain {d : ℝ} (P : ARoom d)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (U : R3 → Hi)
    (i l : Fin 3) (z : ZeroWord) (x : R3) : ℝ :=
  firstQuadraticWordWeight g L g2 q dr Ar p i l z x*
    (PL (AH ((Tq dr Ar p q) x) (wordAtoms z).2
        (directionalFDeriv (coordinateDirection l) U x))
      (JL (P.gainHigh (wordAtoms z).1 (raisingAtom i) ((Tq dr Ar p q) x) (U x)))+
     PL (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (U x))
      (JL (P.gainHigh (raisingAtom i) (wordAtoms z).2 ((Tq dr Ar p q) x)
        (directionalFDeriv (coordinateDirection l) U x))))
local notation "WG" => weightedOriginalTripleGain
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] angularAtomHigh angularAtomReverseHigh
  sphereSobolevInclusionL ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
  ActualHigherSFormation.higherSParam

/-- One constant bounds both original gains for all profiles and every word.
Only the included base derivative, already in the original energy, is used. -/
theorem exists_actual_uniform_weighted_triple_gain_bound
    (hL : 0 < L) {d : ℝ} (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cgain : ℝ, 0 < Cgain ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      ∀ x ∈ closedBall y0 ρ,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      (Tq dr Ar p q) x ∈ ParamRoom d →
      ∀ U : R3 → Hi, ∀ i l : Fin 3, ∀ z : ZeroWord,
        |WG P g2 q dr Ar p U i l z x| ≤
          Cgain*eta*inclusionEnergyDensity IH (actualReferenceBeta g L q dr Ar p x) U x := by
  obtain ⟨Cg,hCg,hGain⟩ := exists_actual_uniform_three_word_symmetrization
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data P
  obtain ⟨Cs,hCs,hScalar⟩ := exists_actual_first_quadratic_word_scalar_first_caps
    g hg L hL y0 ρ g2 hg2
  refine ⟨Cs*Cg,mul_pos hCs hCg,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he1 x hx hb hs hRoom U i l z
  have hS := hScalar q hq dr hdr hdr1 Ar hAr p hp eta heta he1 x hx hb hs i l z
  have hG := (hGain ((Tq dr Ar p q) x) hRoom (U x)
    (directionalFDeriv (coordinateDirection l) U x) (raisingAtom i) (wordAtoms z).1 (wordAtoms z).2).2
  have hbpos : 0 < actualReferenceBeta g L q dr Ar p x := zero_lt_one.trans_le hb
  have hMix := inclusion_energy_mixed_le IH (actualReferenceBeta g L q dr Ar p x) U x hbpos l
  unfold weightedOriginalTripleGain
  rw [abs_mul]
  calc
    _ ≤ (Cs*eta)*(Cg*‖U x‖*‖IH (directionalFDeriv (coordinateDirection l) U x)‖) :=
      mul_le_mul hS.value hG (abs_nonneg _) (mul_nonneg hCs.le heta)
    _ = (Cs*Cg*eta)*(‖IH (directionalFDeriv (coordinateDirection l) U x)‖*‖U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMix (by positivity)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticGains
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticGains.exists_actual_uniform_weighted_triple_gain_bound
