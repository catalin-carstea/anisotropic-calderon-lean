import Calderon.ActualTSPrincipalFirstReference
import Calderon.ActualTSPrincipalPairingGraph

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalCrossReference
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly PrincipalCommutator ReferenceDensityBounds
  ActualScalarPrincipalAdjoint ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ActualHigherSScalarCommutatorNativeForm ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ConformalDepth ReferenceWeightedApproximation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def mixedNegDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def mixedNegDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def mixedLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def mixedLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] mixedNegDualNormed mixedNegDualSpace mixedLowNormed mixedLowSpace

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
local notation "CoeffRoom" => ActualFullEGainedEndpoints.CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

open ActualMixedAngularPairedGains ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Omega" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "CH" => loweringEHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "HH" => raisingReverseHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

open ActualTSPrincipalCoefficients ActualTSPrincipalGreen FixedParameterProfilePullback FixedParameterProfileBudgets
  ActualHigherSCoordinateWeightBounds ActualHigherSLeadingBracketGain SmoothMetricFrame MovingFrameConnection

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL loweringHigh loweringLow raisingHigh raisingLow loweringEHigh raisingReverseHigh


open ActualTSPrincipalPhysicalGreen
local notation "PK" => angularPrincipalHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "PT" => angularPrincipalTransposeHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

open ActualTSPrincipalAngularCaps

local notation "PC" => principalCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "PCt" => principalTransposeCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

open ActualTSPrincipalWeightedCaps ActualTSPrincipalGreen ActualHigherSZeroScalarCommutatorForm


def literalPrincipalFirstCross (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (l k : Fin 3) (U : R3 → Hi) (x : R3) : ℝ :=
  (referenceRadius dr Ar p L x)^2*
    ∑ i : Fin 3, ∑ j : Fin 3,
      (referenceMetricGramFrame g L (q,x) i l*firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x))*
      (PP (AH i (directionalFDeriv (coordinateDirection l) U x))
          (JL (EH j ((Tq dr Ar p q) x) (directionalFDeriv (coordinateDirection k) U x)))-
        PP (aH i (directionalFDeriv (coordinateDirection l) U x))
          (JL (eH j ((Tq dr Ar p q) x) (directionalFDeriv (coordinateDirection k) U x))))

local notation "LC" => literalPrincipalFirstCross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

theorem firstForm_eq_literal_principal_cross
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3)
    (mu : R3 → ℝ) (U : R3 → Hi) :
    firstForm highDualPairingL mu U (PC g2 dr Ar p q l k) (coordinateDirection l) (coordinateDirection k) =
      ∫ x, mu x*LC g2 dr Ar p q l k U x := by
  unfold firstForm literalPrincipalFirstCross
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact congrArg (fun z : ℝ => mu x*z)
    (ActualTSPrincipalPairingGraph.coordinate_first_pairing_eq_principal
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg g2 dr Ar p q l k x
      (directionalFDeriv (coordinateDirection l) U x)
      (directionalFDeriv (coordinateDirection k) U x))

theorem exists_literal_principal_first_reference_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ data.eta0 ∧
      ∀ g2 : MatrixField, ∀ hg2 : IsAdmissibleMetric g2, ∃ Bc : ℝ, 0 < Bc ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
      ∀ F0 : smoothCompactFiniteSphereCore hO hD, tsupport F0.val ⊆ ball y0 ρ →
      (∀ x ∈ tsupport F0.val, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ tsupport F0.val, referenceRadius dr Ar p L x*
        (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ l k : Fin 3,
      |∫ x, referenceDensityFamily g L (q,x)*
        LC g2 dr Ar p q l k (ActualHigherSFormation.higherSInput hO hD F0) x| ≤
      Bc*eta*∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F0 x  := by
  obtain ⟨eta0,h0,hle,hRows⟩ :=
    ActualTSPrincipalFirstReference.exists_principal_first_reference_form_bound
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hL hreg δ0 W data
  refine ⟨eta0,h0,hle,?_⟩
  intro g2 hg2
  obtain ⟨Bc,hBc,hBound⟩ := hRows g2 hg2
  refine ⟨Bc,hBc,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 F0 hsupp hb hs l k
  rw [← firstForm_eq_literal_principal_cross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    g2 dr Ar p q l k (fun x => referenceDensityFamily g L (q,x))
    (ActualHigherSFormation.higherSInput hO hD F0)]
  exact hBound q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 F0 hsupp hb hs l k

private lemma nine_terms_bound (v : Fin 3 → Fin 3 → ℝ) (Bc eta J : ℝ)
    (h : ∀ l k, |v l k| ≤ Bc*eta*J) :
    |∑ l : Fin 3, ∑ k : Fin 3, v l k| ≤ (9*Bc)*eta*J := by
  have hrow (l : Fin 3) : |∑ k : Fin 3, v l k| ≤ 3*(Bc*eta*J) :=
    ActualScalarPrincipalAdjoint.abs_sum_three_le _ _ (h l)
  calc
    _ ≤ 3*(3*(Bc*eta*J)) := ActualScalarPrincipalAdjoint.abs_sum_three_le _ _ hrow
    _ = (9*Bc)*eta*J := by ring

theorem exists_literal_principal_coordinate_sum_reference_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ data.eta0 ∧
      ∀ g2 : MatrixField, ∀ hg2 : IsAdmissibleMetric g2, ∃ Bc : ℝ, 0 < Bc ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
      ∀ F0 : smoothCompactFiniteSphereCore hO hD, tsupport F0.val ⊆ ball y0 ρ →
      (∀ x ∈ tsupport F0.val, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ tsupport F0.val, referenceRadius dr Ar p L x*
        (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      |∑ l : Fin 3, ∑ k : Fin 3, (∫ x, referenceDensityFamily g L (q,x)*
        LC g2 dr Ar p q l k (ActualHigherSFormation.higherSInput hO hD F0) x)| ≤
      Bc*eta*∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F0 x  := by
  obtain ⟨eta0,h0,hle,hRows⟩ := exists_literal_principal_first_reference_bound
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hL hreg δ0 W data
  refine ⟨eta0,h0,hle,?_⟩
  intro g2 hg2
  obtain ⟨Bc,hBc,hBound⟩ := hRows g2 hg2
  refine ⟨9*Bc,mul_pos (by norm_num) hBc,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 F0 hsupp hb hs
  exact nine_terms_bound
    (fun l k => ∫ x, referenceDensityFamily g L (q,x)*
      LC g2 dr Ar p q l k (ActualHigherSFormation.higherSInput hO hD F0) x)
    Bc eta (∫ x, referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F0 x)
    (hBound q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 F0 hsupp hb hs)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalCrossReference
