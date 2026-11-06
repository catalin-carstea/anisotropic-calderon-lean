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

def actualZ1Out (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  KL (ZH dr Ar p q x (UF F x))
def actualT1Out (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  KL (TH dr Ar p q x (UF F x))
local notation "ZO" => actualZ1Out g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "TO" => actualT1Out g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2

def directFirstLinear (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  2*(⟪PF dr Ar p q F x,ZO dr Ar p q F x⟫_ℝ-⟪PR dr Ar p q F x,TO dr Ar p q F x⟫_ℝ)
def directQuadraticLinear (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  2*(⟪KL (Z2 dr Ar p q F x),ZO dr Ar p q F x⟫_ℝ-
    ⟪KL (T2 dr Ar p q F x),TO dr Ar p q F x⟫_ℝ)
def directLinearSquares (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ‖ZO dr Ar p q F x‖^2-‖TO dr Ar p q F x‖^2
def actualDirectLower (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  directFirstLinear g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x+
  directQuadraticLinear g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x+
  directLinearSquares g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x
local notation "DF" => directFirstLinear g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DQ" => directQuadraticLinear g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "DS" => directLinearSquares g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DR" => actualDirectLower g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2

def DirectPhysicalRegularity (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  (ContDiff ℝ ∞ (PF dr Ar p q F) ∧ HasCompactSupport (PF dr Ar p q F)) ∧
  (ContDiff ℝ ∞ (PR dr Ar p q F) ∧ HasCompactSupport (PR dr Ar p q F)) ∧
  (ContDiff ℝ ∞ (fun x => KL (Z2 dr Ar p q F x)) ∧ HasCompactSupport (fun x => KL (Z2 dr Ar p q F x))) ∧
  (ContDiff ℝ ∞ (fun x => KL (T2 dr Ar p q F x)) ∧ HasCompactSupport (fun x => KL (T2 dr Ar p q F x))) ∧
  (ContDiff ℝ ∞ (ZO dr Ar p q F) ∧ HasCompactSupport (ZO dr Ar p q F)) ∧
  (ContDiff ℝ ∞ (TO dr Ar p q F) ∧ HasCompactSupport (TO dr Ar p q F))

def DirectLowerContract : Prop :=
  ∃ CD etaD : ℝ,0 < CD ∧ 0 < etaD ∧ etaD ≤ data.eta0 ∧ ∀ q ∈ Icc (0 : ℝ) 1,
  ∀ dr : ℝ,∀ hdr : 0 < dr,dr ≤ 1 → ∀ Ar : ℝ,∀ hAr : 0 < Ar,∀ p : ℕ,1 ≤ p →
  ∀ eta : ℝ,0 ≤ eta → eta ≤ etaD → ∀ K : Set R3,IsCompact K → K ⊆ ball y0 ρ →
  ∀ F : smoothCompactFiniteSphereCore hO hD,tsupport F.val ⊆ K →
  (∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x) →
  (∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
  let mu := fun x : R3 => referenceDensityFamily g L (q,x)
  let energy := fun x : R3 => mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q dr Ar p x) F x
  DirectPhysicalRegularity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F ∧
  Integrable (fun x => mu x*DF dr Ar p q F x) ∧ Integrable (fun x => mu x*DQ dr Ar p q F x) ∧
  Integrable (fun x => mu x*DS dr Ar p q F x) ∧ Integrable (fun x => mu x*DR dr Ar p q F x) ∧
  Integrable (fun x => mu x*|DR dr Ar p q F x|) ∧ Integrable energy ∧
  (∀ x ∈ K,|DR dr Ar p q F x| ≤ CD*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q dr Ar p x) F x) ∧
  (∫ x,mu x*|DR dr Ar p q F x|) ≤ CD*eta*(∫ x,energy x) ∧
  |∫ x,mu x*DR dr Ar p q F x| ≤ CD*eta*(∫ x,energy x)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
