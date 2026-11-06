import Calderon.ActualTSPrincipalWeightedCaps
import Calderon.ActualTSPairedLowerGreenBound
import Calderon.ActualHigherSZeroScalarNativeForm
import Calderon.ActualTSPrincipalWeightedCoefficients
import Calderon.ActualMixedAngularFullOutputForm
import Calderon.ActualHigherSScalarCommutatorNativeForm
import Calderon.ActualHigherSIntegratedPairing

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalPairingGraph
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


private lemma real_smul_mul (a b : ℝ) : a • b=a*b := by
  exact smul_eq_mul a b

/-- The actual raising/lowering–E/e first pairing is the native principal angular product. -/
theorem angular_first_pairing_eq_principal (i j : Fin 3) (t : Tpar) (u v : Hi) :
    highDualPairingL u (PK i j t v) =
      PP (AH i u) (JL (EH j t v))-PP (aH i u) (JL (eH j t v)) := by
  have h1 : PP (IH u) (aL i (EH j t v))=PP (AH i u) (JL (EH j t v)) :=
    (v017_aA1 hF hO hD i u (EH j t v)).trans
      (v016_pairing_inclusion_symm (EH j t v) (AH i u))
  have h2 : PP (IH u) (AL i (eH j t v))=PP (aH i u) (JL (eH j t v)) :=
    (v017_aA2 hF hO hD i u (eH j t v)).symm
  simpa only [highDualPairingL_apply,angularPrincipalHigh,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply,v016_pairing_sub_right] using
    congrArg₂ (fun x y : ℝ => x-y) h1 h2

/-- Every original coordinate/frame factor and the complete R² weight are retained in the actual first pairing. -/
theorem coordinate_first_pairing_eq_principal
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3) (u v : Hi) :
    highDualPairingL u (PC g2 dr Ar p q l k x v) =
      (referenceRadius dr Ar p L x)^2*
        ∑ i : Fin 3, ∑ j : Fin 3,
          (referenceMetricGramFrame g L (q,x) i l*firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x))*
          (PP (AH i u) (JL (EH j ((Tq dr Ar p q) x) v))-
            PP (aH i u) (JL (eH j ((Tq dr Ar p q) x) v))) := by
  simp only [principalCoordinateCoefficient,weightedMixedSecondCoefficient,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum,real_smul_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [angular_first_pairing_eq_principal hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg i j
    ((Tq dr Ar p q) x) u v]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalPairingGraph
