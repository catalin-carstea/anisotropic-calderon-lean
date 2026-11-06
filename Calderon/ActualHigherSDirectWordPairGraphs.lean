import Calderon.ActualHigherSDirectAtomGraphs
import Calderon.ActualHigherSDirectLowerDefinitions
import Calderon.ActualHigherSDirectUniformData
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

lemma actual_forward_word_pair_graph {dA : ℝ} (P : ARoom dA)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (htA : (Tq dr Ar p q) x ∈ ParamRoom dA)
    (hLifts : ∀ b : ZeroAtom, IH (VA dr Ar p q F x b)=
      AH ((Tq dr Ar p q) x) b (UF F x)) :
    ⟪KL (Z2 dr Ar p q F x),ZO dr Ar p q F x⟫_ℝ =
      ∑ z : ZeroWord, WC dr Ar p q x z *
        QPP (ZH dr Ar p q x (UF F x))
          (AL ((Tq dr Ar p q) x) (wordAtoms z).1
            (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x))) := by
  let U := UF F x
  let z := ZH dr Ar p q x U
  let t := (Tq dr Ar p q) x
  have hPair (v w : Half) : QPP v (JL w)=⟪KL v,KL w⟫_ℝ := by
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using
      ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD v w
  have hA (b : ZeroAtom) (v : Hi) : JL (AH t b v)=AL t b (IH v) :=
    actual_forward_atom_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t htA b v
  exact word_physical_inner_eq_low_sum IH JL KL QPP hPair
    (AH t) (AL t) (fun w : ZeroWord => (wordAtoms w).1)
    (fun w : ZeroWord => (wordAtoms w).2) (WC dr Ar p q x) U
    (VA dr Ar p q F x) hA hLifts z

lemma actual_reverse_word_pair_graph {dA : ℝ} (P : ARoom dA)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (htA : (Tq dr Ar p q) x ∈ ParamRoom dA)
    (hLifts : ∀ b : ZeroAtom, IH (VB dr Ar p q F x b)=
      RH ((Tq dr Ar p q) x) b (UF F x)) :
    ⟪KL (T2 dr Ar p q F x),TO dr Ar p q F x⟫_ℝ =
      ∑ z : ZeroWord, WC dr Ar p q x z *
        QPP (TH dr Ar p q x (UF F x))
          (RL ((Tq dr Ar p q) x) (wordAtoms z).2
            (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x))) := by
  let U := UF F x
  let zR := TH dr Ar p q x U
  let t := (Tq dr Ar p q) x
  have hPair (v w : Half) : QPP v (JL w)=⟪KL v,KL w⟫_ℝ := by
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using
      ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD v w
  have hB (b : ZeroAtom) (v : Hi) : JL (RH t b v)=RL t b (IH v) :=
    actual_reverse_atom_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t htA b v
  exact word_physical_inner_eq_low_sum IH JL KL QPP hPair
    (RH t) (RL t) (fun w : ZeroWord => (wordAtoms w).2)
    (fun w : ZeroWord => (wordAtoms w).1) (WC dr Ar p q x) U
    (VB dr Ar p q F x) hB hLifts zR

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
