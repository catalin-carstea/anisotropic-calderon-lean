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
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalLowerReferenceOrders
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

private lemma coordinate_derivative_cap {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : R3 → V)
    (x : R3) (i : Fin 3) (M : ℝ) (hcap : ‖fderiv ℝ f x‖ ≤ M) :
    ‖directionalFDeriv (coordinateDirection i) f x‖ ≤ M := by
  calc
    _ ≤ ‖fderiv ℝ f x‖*‖coordinateDirection i‖ := (fderiv ℝ f x).le_opNorm _
    _ = ‖fderiv ℝ f x‖ := by rw [norm_coordinateDirection,mul_one]
    _ ≤ M := hcap

/-- Actual principal lower Green rows in the original reference energy; fixed-g2 constant only. -/
theorem exists_principal_lower_reference_all_orders_bound (hL : 0 < L)
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
      ∀ l k i j : Fin 3,
      |lowerForm highDualPairingL (fun x => referenceDensityFamily g L (q,x))
        (ActualHigherSFormation.higherSInput hO hD F0) (PC g2 dr Ar p q l k)
        (coordinateDirection i) (coordinateDirection j)| ≤
      Bc*eta*∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F0 x := by
  classical
  let angular := Classical.choice (exists_principalAngularPhysicalRoom hF hO hD hcalc τ0
    g L y0 Φ B ε C ρ H a w hData hg hL hreg)
  let pairWitness := exists_principalCoordinate_pairing_profile_room hF hO hD hcalc τ0
    g L y0 Φ B ε C ρ H a w hData hg hL hreg δ0 W data
  let etaP : ℝ := Classical.choose pairWitness
  have pairFacts := Classical.choose_spec pairWitness
  obtain ⟨M,hM,hmuCap⟩ := exists_density_coordinate_relative_bound g hg L
    (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨Cr,hCr,hRef⟩ :=
    ActualHigherSZeroScalarNativeForm.exists_highInput_inclusion_reference_integral_bound
      hO hD g hg L hL (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  refine ⟨min angular.eta0 etaP,lt_min angular.eta0_pos pairFacts.1,
    (min_le_right _ _).trans pairFacts.2.1,?_⟩
  intro g2 hg2
  obtain ⟨Q,hQ,hCaps⟩ := exists_principalCoordinate_uniform_first_caps hF hO hD hcalc τ0
    g L y0 Φ B ε C ρ H a w hData hg hL angular g2 hg2
  let aB : ℝ := ‖PL‖*Q*(M+1)
  have haB : 0 ≤ aB := by dsimp [aB]; positivity
  refine ⟨1+aB*Cr,by positivity,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 F0 hsupp hb hs l k i j
  let K : Set R3 := tsupport F0.val
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := actualReferenceBeta g L q dr Ar p
  let U := ActualHigherSFormation.higherSInput hO hD F0
  have hK : IsCompact K := F0.property.2.1
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmu : ∀ x, 0 ≤ mu x := fun x => (referenceDensityFamily_pos g hg L (q,x)).le
  have hbcont := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hbpos := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp
  have hu : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hz : ∀ x ∉ K, U x=0 :=
    ActualHigherSZeroScalarNativeForm.highInput_eq_zero_off hO hD F0
  have hAtPoint (x : R3) (hx : x ∈ K) := hCaps q hq dr hdr hdr1 Ar hAr p hp eta heta
    (heta0.trans (min_le_left _ _)) x (ball_subset_closedBall (hsupp hx)) (hsupp hx)
    (hb x hx) (hs x hx) l k
  have hPair (x : R3) (hx : x ∈ K) :
      ∀ᶠ y in 𝓝 x, ∀ u1 u2 : Hi, PL (IH u1) (PC g2 dr Ar p q l k y u2)=
        PL (IH u2) (PCt g2 dr Ar p q l k y u1) := by
    have hgerm := pairFacts.2.2 g2 q hq dr hdr hdr1 Ar hAr p hp eta heta
      (heta0.trans (min_le_right _ _)) x (ball_subset_closedBall (hsupp hx)) (hsupp hx)
      (hb x hx) (hs x hx) l k
    exact hgerm.mono (fun y hy u1 u2 => by
      simpa only [highDualPairingL_apply,halfDualPairingL_apply] using hy u2 u1)
  have hLower := ActualTSPairedLowerGreenBound.paired_lowerForm_bound PL IH mu beta U
    (PC g2 dr Ar p q l k) (PCt g2 dr Ar p q l k) K hK hm hbcont hbpos hu hz
    (fun x hx => (hAtPoint x hx).1.1) (fun x hx => (hAtPoint x hx).2.1) hPair
    Q M eta hQ (zero_le_one.trans hM) heta hmu i j
    (fun x hx => ((hAtPoint x hx).2.2.1).trans (div_le_self (mul_nonneg hQ heta) (hb x hx)))
    (fun x hx => coordinate_derivative_cap _ x i (Q*eta) (hAtPoint x hx).2.2.2)
    (fun x hx => hmuCap q hq x (ball_subset_closedBall (hsupp hx)) i)
  have hRefBound := hRef q hq dr Ar p hdr hAr hp F0
    (fun x hx => ball_subset_closedBall (hsupp hx)) hb
  have hNonneg : 0 ≤ ∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x :=
    integral_nonneg (fun x => mul_nonneg (hmu x)
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbpos x).le F0 x))
  change |lowerForm ((PL).comp IH) mu U (PC g2 dr Ar p q l k)
    (coordinateDirection i) (coordinateDirection j)| ≤ _
  calc
    _ ≤ (aB*eta)*inclusionEnergy IH mu beta U := hLower.2
    _ ≤ (aB*eta)*(Cr*∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x) :=
      mul_le_mul_of_nonneg_left hRefBound (mul_nonneg haB heta)
    _ ≤ (1+aB*Cr)*eta*∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x := by
      have hn := mul_nonneg heta hNonneg
      nlinarith only [hn]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalLowerReferenceOrders
