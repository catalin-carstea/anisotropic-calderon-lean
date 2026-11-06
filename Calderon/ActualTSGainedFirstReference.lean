import Calderon.ActualTSPrincipalWeightedCaps
import Calderon.ActualTSPrincipalSymmetricFirstForm
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
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSGainedFirstReference
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


local notation "GC" => gainedCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "LowC" => mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

/-- The actual gained first form uses only the original included gradient and a native value gain. -/
theorem exists_gained_first_reference_form_bound (hL : 0 < L)
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
      |firstForm highDualPairingL (fun x => referenceDensityFamily g L (q,x))
        (ActualHigherSFormation.higherSInput hO hD F0) (GC hreg δ0 W data g2 dr Ar p q l k)
        (coordinateDirection i) (coordinateDirection j)| ≤
      Bc*eta*∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F0 x := by
  classical
  let guardWitness := exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ data.δ data.δ_pos
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaRoom : ℝ := Classical.choose guardWitness
  have guardFacts := Classical.choose_spec guardWitness
  obtain ⟨Cr,hCr,hRef⟩ :=
    ActualHigherSZeroScalarNativeForm.exists_highInput_inclusion_reference_integral_bound
      hO hD g hg L hL (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  refine ⟨min data.eta0 etaRoom,lt_min data.eta0_pos guardFacts.1,min_le_left _ _,?_⟩
  intro g2 hg2
  obtain ⟨Q,hQ,hCaps⟩ := exists_mixedAngularSecondCoefficient_uniform_first_caps hF hO hD hcalc τ0
    g L y0 Φ B ε C ρ H a w hData hg hL hreg δ0 W data g2 hg2
  let aB : ℝ := ‖PL‖*Q
  have haB : 0 ≤ aB := mul_nonneg (norm_nonneg PL) hQ
  refine ⟨1+aB*Cr,by positivity,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 F0 hsupp hb hs l k i j
  let K : Set R3 := tsupport F0.val
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := actualReferenceBeta g L q dr Ar p
  let U := ActualHigherSFormation.higherSInput hO hD F0
  let Clow := LowC hreg δ0 W data g2 dr Ar p q l k
  have hK : IsCompact K := F0.property.2.1
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmu : ∀ x, 0 ≤ mu x := fun x => (referenceDensityFamily_pos g hg L (q,x)).le
  have hbcont := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hbpos := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp
  have hu : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hz : ∀ x ∉ K, U x=0 := ActualHigherSZeroScalarNativeForm.highInput_eq_zero_off hO hD F0
  have hmem (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom data.δ := by
    have hg := guardFacts.2.2 q hq dr hdr hdr1 Ar hAr p hp eta heta
      (heta0.trans (min_le_right _ _)) x (ball_subset_closedBall (hsupp hx)) (hsupp hx) (hb x hx) (hs x hx)
    exact (higherSParam_eventually_mem y0 ρ data.δ L dr Ar q p hdr hAr x hg).self_of_nhds
  have hGraph (x : R3) (hx : x ∈ K) :
      GC hreg δ0 W data g2 dr Ar p q l k x=(Clow x).comp IH :=
    gainedCoordinate_eq_checked_coefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W data g2 dr Ar p q l k x (hmem x hx)
  have hC (x : R3) (hx : x ∈ K) := hCaps q hq dr hdr hdr1 Ar hAr p hp eta heta
    (heta0.trans (min_le_left _ _)) x (ball_subset_closedBall (hsupp hx)) (hsupp hx) (hb x hx) (hs x hx) l k
  have hBound := ActualTSPrincipalSymmetricFirstForm.gained_firstForm_bound PL IH mu beta U Clow K hK
    hm.continuous hbcont hbpos hu hz (fun x hx => (hC x hx).1) Q eta hQ heta hmu
    (fun x hx => (hC x hx).2.1) i j
  have hEq := ActualTSPrincipalSymmetricFirstForm.included_firstForm_eq PL IH mu U
    (GC hreg δ0 W data g2 dr Ar p q l k) Clow K hK.isClosed hu hz hGraph
    (coordinateDirection i) (coordinateDirection j)
  have hRefBound := hRef q hq dr Ar p hdr hAr hp F0
    (fun x hx => ball_subset_closedBall (hsupp hx)) hb
  have hNonneg : 0 ≤ ∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x :=
    integral_nonneg (fun x => mul_nonneg (hmu x)
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbpos x).le F0 x))
  change |firstForm ((PL).comp IH) mu U (GC hreg δ0 W data g2 dr Ar p q l k)
    (coordinateDirection i) (coordinateDirection j)| ≤ _
  rw [hEq]
  calc
    _ ≤ (aB*eta)*inclusionEnergy IH mu beta U := hBound
    _ ≤ (aB*eta)*(Cr*∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x) :=
      mul_le_mul_of_nonneg_left hRefBound (mul_nonneg haB heta)
    _ ≤ (1+aB*Cr)*eta*∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F0 x := by
      have hn := mul_nonneg heta hNonneg
      nlinarith only [hn]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSGainedFirstReference
