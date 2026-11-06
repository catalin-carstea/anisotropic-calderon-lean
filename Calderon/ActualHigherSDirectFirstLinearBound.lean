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

/-- Exact native instance of the original generic low-input bound. -/
private lemma native_abs_pair_low_input_le (Low : Half →L[ℝ] Neg)
    (z v : Half) (Z B : ℝ) (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hz : ‖z‖ ≤ Z) (hLow : ‖Low‖ ≤ B) :
    |QPP z (Low v)| ≤ ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP*Z*B*‖v‖ := by
  rw [ActualHigherSPairingNormDiagnostic.standardPairingNorm_eq_generic]
  exact abs_pair_low_input_le QPP Low z v Z B hZ hB hz hLow

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh sphereSobolevInclusionL sphereSobolevHalfToSphereL2L
  ActualHigherSFormation.higherSInput ActualHigherSScalarCommutatorNativeForm.halfInput
  atomHigh atomLow atomReverseHigh atomReverseLow

lemma actual_direct_first_linear_of_caps
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (htD : (Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (Mf Cz Cr eta : ℝ) (hMf : 0 ≤ Mf) (hCz : 0 ≤ Cz) (hCr : 0 ≤ Cr)
    (heta : 0 ≤ eta) (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hLow : ∀ k : Fin 3,‖PL dr Ar p q x k‖ ≤ Mf*(referenceRadius dr Ar p L x)^2 ∧
      ‖DL dr Ar p q x k‖ ≤ Mf*(referenceRadius dr Ar p L x)^2)
    (hLin : ‖ZH dr Ar p q x‖ ≤ Cz*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x ∧
      ‖TH dr Ar p q x‖ ≤ Cz*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x)
    (hYoung : ∀ k : Fin 3,‖directionalFDeriv (coordinateDirection k) (HU F) x‖*‖UF F x‖ ≤
      (1+Cr)*finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q dr Ar p x) F x)
    (hr : 0 ≤ referenceRadius dr Ar p L x)
    (h4 : (referenceRadius dr Ar p L x)^4*actualReferenceBeta g L q dr Ar p x ≤ eta) :
    |DF dr Ar p q F x| ≤
      (12*ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP*Mf*Cz*(1+Cr))*eta*
      finiteCoreReferenceProfileEnergy hO hD g hg L q
      (actualReferenceBeta g L q dr Ar p x) F x := by
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let U := UF F x
  let E := finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x
  let z := ZH dr Ar p q x U
  let zR := TH dr Ar p q x U
  let du := fun k => directionalFDeriv (coordinateDirection k) (HU F) x
  let dU := fun k => directionalFDeriv (coordinateDirection k) (UF F) x
  let t := (Tq dr Ar p q) x
  let N := ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP
  have hN : 0 ≤ N := ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hE : 0 ≤ E := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q beta hb0 F x
  have hz : ‖z‖ ≤ Cz*r^2*beta*‖U‖ := (ZH dr Ar p q x).le_opNorm U |>.trans
    (mul_le_mul_of_nonneg_right hLin.1 (norm_nonneg _))
  have hzR : ‖zR‖ ≤ Cz*r^2*beta*‖U‖ := (TH dr Ar p q x).le_opNorm U |>.trans
    (mul_le_mul_of_nonneg_right hLin.2 (norm_nonneg _))
  have hPair (v w : Half) : QPP v (JL w)=⟪KL v,KL w⟫_ℝ := by
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using
      ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD v w
  have hi (k : Fin 3) : IH (dU k)=du k :=
    (ActualHigherSScalarCommutatorNativeForm.directional_halfInput hO hD F (coordinateDirection k) x).symm
  have hGraph (k : Fin 3) := ActualPPLowerRemainder.actual_first_high_low_graphs
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q x htD k (dU k)
  have hPF : ⟪PF dr Ar p q F x,ZO dr Ar p q F x⟫_ℝ=
      ∑ k : Fin 3,QPP z (PL dr Ar p q x k (du k)) :=
    first_physical_inner_eq_low_sum IH JL KL QPP hPair
      (PH dr Ar p q x) (PL dr Ar p q x) dU du (fun k => (hGraph k).1) hi z
  have hPR : ⟪PR dr Ar p q F x,TO dr Ar p q F x⟫_ℝ=
      ∑ k : Fin 3,QPP zR (DL dr Ar p q x k (du k)) :=
    first_physical_inner_eq_low_sum IH JL KL QPP hPair
      (DH dr Ar p q x) (DL dr Ar p q x) dU du (fun k => (hGraph k).2) hi zR
  have hFirstRow (Low : Half →L[ℝ] Neg) (zz : Half) (k : Fin 3)
      (hL : ‖Low‖ ≤ Mf*r^2) (hZ : ‖zz‖ ≤ Cz*r^2*beta*‖U‖) :
      |QPP zz (Low (du k))| ≤ (N*Mf*Cz*(1+Cr))*eta*E := by
    have hy := hYoung k
    calc
      _ ≤ N*(Cz*r^2*beta*‖U‖)*(Mf*r^2)*‖du k‖ :=
        native_abs_pair_low_input_le Low zz (du k) _ _ (by positivity) (by positivity) hZ hL
      _ = (N*Mf*Cz)*(r^4*beta)*(‖du k‖*‖U‖) := by ring
      _ ≤ (N*Mf*Cz)*eta*((1+Cr)*E) := by gcongr
      _ = _ := by ring
  have hPbound : |⟪PF dr Ar p q F x,ZO dr Ar p q F x⟫_ℝ| ≤
      3*(N*Mf*Cz*(1+Cr))*eta*E := by
    rw [hPF]
    calc
      _ ≤ ∑ k : Fin 3,|QPP z (PL dr Ar p q x k (du k))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 3,(N*Mf*Cz*(1+Cr))*eta*E :=
        Finset.sum_le_sum (fun k _ => hFirstRow _ z k (hLow k).1 hz)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hRbound : |⟪PR dr Ar p q F x,TO dr Ar p q F x⟫_ℝ| ≤
      3*(N*Mf*Cz*(1+Cr))*eta*E := by
    rw [hPR]
    calc
      _ ≤ ∑ k : Fin 3,|QPP zR (DL dr Ar p q x k (du k))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 3,(N*Mf*Cz*(1+Cr))*eta*E :=
        Finset.sum_le_sum (fun k _ => hFirstRow _ zR k (hLow k).2 hzR)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hFirst : |DF dr Ar p q F x| ≤ (12*N*Mf*Cz*(1+Cr))*eta*E := by
    unfold directFirstLinear
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    exact (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hPbound hRbound))
      (by norm_num : (0 : ℝ)≤2)).trans (le_of_eq (by ring))
  exact hFirst

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
