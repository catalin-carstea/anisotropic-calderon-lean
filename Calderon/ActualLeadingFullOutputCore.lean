import Calderon.ActualLeadingPhysicalSignedSecondForm
import Calderon.ActualHigherSPhysicalPairing
import Calderon.ActualHigherSFirstPhysicalCommutatorGraph

set_option autoImplicit false
set_option Elab.async false
set_option stderrAsMessages false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
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
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rh" => originalRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rl" => originalRadialLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sh" => originalRadialReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sl" => originalRadialReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hh" => jacobiAngularOperatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hl" => jacobiAngularOperatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hh" => jacobiAngularReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hl" => jacobiAngularReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RR" => retainedAdjacentHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "RH" => radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HR" => angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HH" => jacobiAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  originalRadialHigh originalRadialLow originalRadialReverseHigh originalRadialReverseLow
  jacobiAngularOperatorHigh jacobiAngularOperatorLow jacobiAngularReverseHigh jacobiAngularReverseLow
  zeroCorrectionHigh zeroCorrectionHalf zeroReverseHigh zeroReverseHalf sphereSobolevInclusionL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  fullGainedHigh retainedAdjacentHigh radialAngularHigh angularRadialHigh jacobiAngularHigh
  commonRoom referenceRadialEndpointInvertibleLocus

open FixedParameterProfilePullback FixedParameterProfileBudgets ConformalDepth
  ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

open ActualHigherSLeadingGainedSecondForm ActualHigherSCoordinateWeightBounds
  ActualHigherSLeadingBracketGain


open MeasureTheory PrincipalCommutator ReferenceDensityBounds ActualFiniteHarmonicModel ActualFiniteHarmonicCore
  ActualHigherSScalarCommutatorNativeForm ActualHigherSScalarCommutatorForm
  ActualHigherSFirstPhysicalCommutatorGraph

/-- The actual input inclusion commutes with both base derivatives, before any geometric coefficient. -/
theorem leading_second_halfInput (F : smoothCompactFiniteSphereCore hO hD)
    (l k : Fin 3) (x : R3) :
    directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) (halfInput hO hD F)) x =
      IH (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k)
        (ActualHigherSFormation.higherSInput hO hD F)) x) := by
  let U : R3 → Hi := ActualHigherSFormation.higherSInput hO hD F
  have hu : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hInput : (fun y => IH (U y)) = halfInput hO hD F := rfl
  have firstGraph : directionalFDeriv (coordinateDirection l)
      (directionalFDeriv (coordinateDirection k) (fun y => IH (U y))) x =
      IH (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) U) x) :=
    directional_second_linear_input IH U hu (coordinateDirection l) (coordinateDirection k) x
  have renameInput := congrArg (fun z : R3 → Half => directionalFDeriv (coordinateDirection l)
    (directionalFDeriv (coordinateDirection k) z) x) hInput
  exact renameInput.symm.trans firstGraph

/-- Fixed-space supported action, using the concrete inherited Sobolev structures. -/
theorem contDiff_supported_leading_operator (u : R3 → Hi) (A : R3 → Hi →L[ℝ] Half)
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) :
    ContDiff ℝ ∞ (fun x => A x (u x)) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x ∈ K
  · exact (hA x hx).clm_apply hu.contDiffAt
  · have he : (fun y => A y (u y)) =ᶠ[𝓝 x] (fun _ => (0 : Half)) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      simp only [h0 y hy,map_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- Exact concrete three-row sum; its addition is the original Half addition. -/
theorem contDiff_leading_half_sum3 (f : Fin 3 → R3 → Half)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) : ContDiff ℝ ∞ (fun x => ∑ i : Fin 3, f i x) := by
  have hexpand : (fun x => ∑ i : Fin 3, f i x) = (fun x => f 0 x+f 1 x+f 2 x) := by
    funext x
    rw [Fin.sum_univ_three]
  have hthree : ContDiff ℝ ∞ (fun x => f 0 x+f 1 x+f 2 x) := ((hf 0).add (hf 1)).add (hf 2)
  have hprop : ContDiff ℝ ∞ (fun x => ∑ i : Fin 3, f i x) =
      ContDiff ℝ ∞ (fun x => f 0 x+f 1 x+f 2 x) :=
    congrArg (fun z : R3 → Half => ContDiff ℝ ∞ z) hexpand
  exact Eq.mpr hprop hthree

/-- The original bounded embedding gives the full L2 output, without angular finiteness. -/
theorem contDiff_leading_physical_embedding (u : R3 → Half) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun x => sphereSobolevHalfToSphereL2L hO hD (u x)) :=
  (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hu

/-- Complete fixed-space smoothness of the supported second sum, before endpoint parameters. -/
theorem contDiff_supported_leading_second_sum
    (A : Fin 3 → Fin 3 → R3 → Hi →L[ℝ] Half) (u : R3 → Hi)
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (hzero : ∀ x ∉ K, u x = 0)
    (hA : ∀ l k x, x ∈ K → ContDiffAt ℝ ∞ (A l k) x) :
    ContDiff ℝ ∞ (fun x => ∑ l : Fin 3, ∑ k : Fin 3,
      A l k x (directionalFDeriv (coordinateDirection l)
        (directionalFDeriv (coordinateDirection k) u) x)) := by
  have hd0 (k : Fin 3) : ∀ y ∉ K, directionalFDeriv (coordinateDirection k) u y = 0 :=
    fun y hy => directional_eq_zero_off u _ hK hzero _ y hy
  have hdd0 (l k : Fin 3) : ∀ y ∉ K,
      directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) y = 0 :=
    fun y hy => directional_eq_zero_off _ _ hK (hd0 k) _ y hy
  have hrow (l k : Fin 3) : ContDiff ℝ ∞ (fun x => A l k x
      (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x)) :=
    contDiff_supported_leading_operator
      (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u))
      (A l k) K hK
      (contDiff_directionalFDeriv _ _ (contDiff_directionalFDeriv _ u hu)) (hdd0 l k) (hA l k)
  exact contDiff_leading_half_sum3 _ (fun l => contDiff_leading_half_sum3 _ (hrow l))

section LeadingCoefficientSmooth
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Smoothness in the exact generic instance context of the existing weighted coefficient. -/
theorem contDiffAt_leadingWeightedCoefficient (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G : Fin 3 → Fin 3 → R3 → E →L[ℝ] F) (x : R3)
    (hR : ContDiffAt ℝ ∞ R x) (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x)
    (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x) (hG : ∀ i j, ContDiffAt ℝ ∞ (G i j) x) :
    ContDiffAt ℝ ∞ (weightedGainedCoefficient R a b G) x := by
  have hW : ContDiffAt ℝ ∞ (fun y => ∑ i : Fin 3, ∑ j : Fin 3, (a i y*b j y) • G i j y) x := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact ((ha i).mul (hb j)).smul (hG i j)
  unfold weightedGainedCoefficient
  exact ((hR.pow 4).neg).smul hW
end LeadingCoefficientSmooth

/-- The genuine high realization of the ordered actual leading coefficient. -/
def physicalLeadingHighCoefficient (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) : R3 → Hi →L[ℝ] Half :=
  weightedGainedCoefficient (referenceRadius dr Ar p L)
    (fun i y => firstCoordinateWeight g g2 L l i ((Tq dr Ar p q) y))
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data.Gcoord data.GN data.δ0 data.germs i j ((Tq dr Ar p q) y))

/-- Both actual Sobolev inclusions, without any inverse or angular-output truncation. -/
theorem physicalLeadingHighCoefficient_negative_graph (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom data.δ) (v : Hi) :
    JL (physicalLeadingHighCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q l k x v) =
    physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q l k x (IH v) := by
  simp only [physicalLeadingHighCoefficient,physicalLeadingCoefficient,weightedGainedCoefficient,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hCompat := congrArg (fun A : Hi →L[ℝ] Neg => A v) (data.low_graph i j _ ht).1
  simpa only [ContinuousLinearMap.comp_apply] using hCompat.symm

attribute [local irreducible] physicalLeadingHighCoefficient physicalLeadingCoefficient

/-- All nine high leading rows applied to the original finite input. -/
def actualLeadingSignedSecondHalf (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  ∑ l : Fin 3, ∑ k : Fin 3,
    physicalLeadingHighCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q l k x
      (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k)
        (ActualHigherSFormation.higherSInput hO hD F)) x)

/-- Full SphereL2 output, with no finite angular-output restriction. -/
def actualLeadingSignedSecondOut (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  sphereSobolevHalfToSphereL2L hO hD (actualLeadingSignedSecondHalf
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x)

local notation "CH" => physicalLeadingHighCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "NH" => actualLeadingSignedSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "NN" => actualLeadingSignedSecondNeg g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "NO" => actualLeadingSignedSecondOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

/-- The exact global negative graph; support locality closes points outside the room. -/
theorem actualLeadingSignedSecondHalf_negative_graph (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom data.δ) (x : R3) :
    JL (NH hreg data g2 dr Ar p q F x) = NN hreg data g2 dr Ar p q F x := by
  let U : R3 → Hi := ActualHigherSFormation.higherSInput hO hD F
  have hu : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hz : ∀ y ∉ tsupport F.val, U y = 0 := higherSInput_eq_zero_off hO hD F
  have hSecondInput (l k : Fin 3) : directionalFDeriv (coordinateDirection l)
      (directionalFDeriv (coordinateDirection k) (halfInput hO hD F)) x =
      IH (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) U) x) :=
    leading_second_halfInput hO hD F l k x
  unfold actualLeadingSignedSecondHalf actualLeadingSignedSecondNeg
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _

  let v : Hi := directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) U) x
  let dv : Half := directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) (halfInput hO hD F)) x
  let CL : Half →L[ℝ] Neg := physicalLeadingCoefficient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x
  have hRight : CL dv = CL (IH v) := congrArg (fun z : Half => CL z) (hSecondInput l k)

  by_cases hx : x ∈ tsupport F.val
  · have hLeft : JL (CH hreg data g2 dr Ar p q l k x v) = CL (IH v) :=
      physicalLeadingHighCoefficient_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 dr Ar p q l k x (hTF x hx) v
    have rowResult : JL (CH hreg data g2 dr Ar p q l k x v) = CL dv := hLeft.trans hRight.symm

    endpoint_literal_transport rowResult
  · have hd0 : ∀ y ∉ tsupport F.val, directionalFDeriv (coordinateDirection k) U y = 0 :=
      fun y hy => directional_eq_zero_off U _ (isClosed_tsupport F.val) hz _ y hy
    have hdd : v = 0 := directional_eq_zero_off _ _ (isClosed_tsupport F.val) hd0 (coordinateDirection l) x hx
    have hLeft : JL (CH hreg data g2 dr Ar p q l k x v) = CL (IH v) := by
      simp only [hdd,map_zero]
    have rowResult : JL (CH hreg data g2 dr Ar p q l k x v) = CL dv := hLeft.trans hRight.symm

    endpoint_literal_transport rowResult

/-- Smoothness of the genuine high coefficient from the actual endpoint cap record. -/
theorem physicalLeadingHighCoefficient_contDiffAt (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (hdr : 0 < dr) (hdr1 : dr ≤ 1) (hAr : 0 < Ar) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0)
    (x : R3) (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (l k : Fin 3) : ContDiffAt ℝ ∞ (CH hreg data g2 dr Ar p q l k) x := by
  have ha := exists_physical_firstCoordinateWeight_uniform_first_caps g g2 hg hg2 L y0 ρ
  have hweights := (Classical.choose_spec ha).2
  have hG (i j : Fin 3) := (data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0
    x hx hxBall hb hs i j).1.1
  unfold physicalLeadingHighCoefficient
  exact contDiffAt_leadingWeightedCoefficient (referenceRadius dr Ar p L)
    (fun i y => firstCoordinateWeight g g2 L l i ((Tq dr Ar p q) y))
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data.Gcoord data.GN data.δ0 data.germs i j ((Tq dr Ar p q) y)) x
    (contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
    (fun i => (hweights q hq x hx dr Ar p l i).1.contDiffAt)
    (fun j => (hweights q hq x hx dr Ar p k j).1.contDiffAt) hG

/-- Global smoothness of the actual nine-row Half output, with the original hypotheses. -/
theorem actualLeadingSignedSecondHalf_contDiff (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (hdr : 0 < dr) (hdr1 : dr ≤ 1) (hAr : 0 < Ar) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hball : tsupport F.val ⊆ ball y0 ρ)
    (hb : ∀ x ∈ tsupport F.val, 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ tsupport F.val,
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    ContDiff ℝ ∞ (NH hreg data g2 dr Ar p q F) := by
  have hCH (l k : Fin 3) (x : R3) (hx : x ∈ tsupport F.val) :
      ContDiffAt ℝ ∞ (CH hreg data g2 dr Ar p q l k) x :=
    physicalLeadingHighCoefficient_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
      hreg data g2 hg2 dr Ar p q hq hdr hdr1 hAr hp eta heta heta0 x
      (ball_subset_closedBall (hball hx)) (hball hx) (hb x hx) (hs x hx) l k
  have built := contDiff_supported_leading_second_sum
    (fun l k => CH hreg data g2 dr Ar p q l k)
    (ActualHigherSFormation.higherSInput hO hD F) (tsupport F.val) (isClosed_tsupport F.val)
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F) (higherSInput_eq_zero_off hO hD F) hCH
  unfold actualLeadingSignedSecondHalf
  endpoint_literal_transport built


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
