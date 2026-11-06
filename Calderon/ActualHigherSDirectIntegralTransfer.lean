import Calderon.ActualHigherSDirectLowerDefinitions
import Calderon.ActualHigherSDirectUniformData
import Calderon.ActualHigherSDirectPointwiseBound
import Calderon.ActualHigherSDirectRegularityFacts
import Calderon.ActualPPCoefficientCaps
import Calderon.ActualHigherSDirectAlgebra
import Calderon.ActualHigherSLinearZeroCaps
import Calderon.ActualHigherSQuadraticZeroQuarticBounds
import Calderon.ActualLowerSSelfFormation
import Calderon.ActualHigherSPairingNormDiagnostic
import Calderon.ActualHigherSZeroAtomDictionary
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualHigherSLeadingBracketGain ConformalDepth PrincipalCommutator
  ActualHigherSLinearZero ActualHigherSQuadraticZeroWords ActualHigherSQuadraticZeroQuartic
  ActualHigherSQuadraticZeroQuarticBounds ActualHigherSLinearZeroScalarCaps
  ActualHigherSLeadingWeightedJetBounds ActualPPCoefficientCaps
  ActualScalarPrincipalSelfFormBound SectionFiveErrorForms FixedParameterProfilePullback
  ActualHigherSDirectAlgebra
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
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
  (g2 : MatrixField)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "PH" => ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "PL" => ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DL" => ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "HU" => ActualHigherSScalarCommutatorNativeForm.halfInput hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "PF" => ActualPPLowerRemainder.actualPPFirstOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "PR" => ActualPPLowerRemainder.actualPPReverseFirstOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "ZH" => linearZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "TH" => linearAdjointZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "QPP" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
local notation "DH" => ActualPPLowerRemainder.actualPPReverseFirstHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WC" => actualWordCoefficient g L g2
local notation "VA" => actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d

local notation "ZO" => actualZ1Out g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "TO" => actualT1Out g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2

local notation "DF" => directFirstLinear g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DQ" => directQuadraticLinear g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "DS" => directLinearSquares g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DR" => actualDirectLower g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh sphereSobolevInclusionL sphereSobolevHalfToSphereL2L
  ActualHigherSFormation.higherSInput ActualHigherSScalarCommutatorNativeForm.halfInput
  atomHigh atomLow atomReverseHigh atomReverseLow

local notation "DData" => DirectUniformData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "CD" D:max => directBoundConstant g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
local notation "etaD" D:max => directProfileThreshold g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D

/-- Complete original full-K and weighted all-space tail.
Every regularity, support, L1 and pointwise premise is PRODUCED internally. -/
lemma actual_direct_full_tail (hL : 0 < L) (hg2 : IsAdmissibleMetric g2)
    (D : DData) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1) (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaD : eta ≤ etaD D)
    (K : Set R3) (hK : IsCompact K) (hKball : K ⊆ ball y0 ρ)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport F.val ⊆ K)
    (hb : ∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    let mu := fun x : R3 => referenceDensityFamily g L (q,x)
  let energy := fun x : R3 => mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q dr Ar p x) F x
  DirectPhysicalRegularity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F ∧
  Integrable (fun x => mu x*DF dr Ar p q F x) ∧ Integrable (fun x => mu x*DQ dr Ar p q F x) ∧
  Integrable (fun x => mu x*DS dr Ar p q F x) ∧ Integrable (fun x => mu x*DR dr Ar p q F x) ∧
  Integrable (fun x => mu x*|DR dr Ar p q F x|) ∧ Integrable energy ∧
  (∀ x ∈ K,|DR dr Ar p q F x| ≤ CD D*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q dr Ar p x) F x) ∧
  (∫ x,mu x*|DR dr Ar p q F x|) ≤ CD D*eta*(∫ x,energy x) ∧
  |∫ x,mu x*DR dr Ar p q F x| ≤ CD D*eta*(∫ x,energy x) := by
  dsimp only
  let mu := fun x : R3 => referenceDensityFamily g L (q,x)
  let energy := fun x : R3 => mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q dr Ar p x) F x
  have R := actual_direct_regularity_facts g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hL hg2 D q hq dr hdr hdr1 Ar hAr p hp eta heta hetaD K hK hKball F hsupp hb hs
  have hInputPoint := actual_direct_pointwise_on_input_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D q hq dr hdr hdr1 Ar hAr p hp eta heta hetaD K hK hKball F hsupp hb hs
  have hCD := directBoundConstant_pos g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
  have hPoint (x : R3) (hx : x ∈ K) : |DR dr Ar p q F x| ≤
      CD D*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q dr Ar p x) F x := by
    by_cases hxi : x ∈ tsupport F.val
    · exact hInputPoint x hxi
    · rw [R.direct_off_input x hxi,abs_zero]
      exact mul_nonneg (mul_nonneg hCD.le heta)
        (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q _
          (zero_le_one.trans (hb x hx)) F x)
  have hGlobal (x : R3) : mu x*|DR dr Ar p q F x| ≤ (CD D*eta)*energy x := by
    by_cases hxi : x ∈ tsupport F.val
    · have hh := mul_le_mul_of_nonneg_left (hInputPoint x hxi)
        (referenceDensityFamily_pos g hg L (q,x)).le
      convert hh using 1 <;> dsimp only [mu,energy] <;> ring
    · rw [R.direct_off_input x hxi,abs_zero,mul_zero]
      exact mul_nonneg (mul_nonneg hCD.le heta) (R.energy_nonneg x)
  have hAbs : (∫ x,mu x*|DR dr Ar p q F x|) ≤ CD D*eta*(∫ x,energy x) := by
    calc
      _ ≤ ∫ x,(CD D*eta)*energy x :=
        integral_mono R.absolute_integrable (R.energy_integrable.const_mul _) hGlobal
      _ = _ := integral_const_mul _ _
  have hSigned : |∫ x,mu x*DR dr Ar p q F x| ≤ CD D*eta*(∫ x,energy x) := by
    calc
      _ = ‖∫ x,mu x*DR dr Ar p q F x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x,(CD D*eta)*energy x := norm_integral_le_of_norm_le
        (R.energy_integrable.const_mul _) (Filter.Eventually.of_forall (fun x => by
          have hm : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (q,x)).le
          simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hm] using hGlobal x))
      _ = _ := integral_const_mul _ _
  exact ⟨R.regularity,R.first_integrable,R.quadratic_integrable,R.squares_integrable,
    R.direct_integrable,R.absolute_integrable,R.energy_integrable,hPoint,hAbs,hSigned⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
