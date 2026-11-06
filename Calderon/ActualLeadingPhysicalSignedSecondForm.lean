import Calderon.ActualFullEPhysicalEndpoints
import Calderon.ActualHigherSLeadingGainedSecondForm
import Calderon.ActualHigherSCoordinateWeightBounds
import Calderon.ActualHigherSAdjointLeadingCoordinate
import Calderon.ActualHigherSScalarCommutatorNativeForm

/-! Exact actual full E/E joint endpoints. All actual RR/RH/HR/HH and zero rows, both low
inclusion graphs and six-family all-order within caps are retained. -/
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

@[instance_reducible] private def leadingNegDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] leadingNegDualNormed
@[instance_reducible] private def leadingNegDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] leadingNegDualSpace
@[instance_reducible] private def leadingLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] leadingLowNormed
@[instance_reducible] private def leadingLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] leadingLowSpace
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL

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

/-- The actual leading signed coefficient, with all nine ordered gained rows. -/
def physicalLeadingCoefficient (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) : R3 → Half →L[ℝ] Neg :=
  weightedGainedCoefficient (referenceRadius dr Ar p L)
    (fun i y => firstCoordinateWeight g g2 L l i ((Tq dr Ar p q) y))
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => data.Cl i j ((Tq dr Ar p q) y))

/-- Actual physical endpoint producers discharge all operator-jet premises of the leading cap estimate. -/
theorem exists_actual_leading_coefficient_uniform_first_caps (hL : 0 < L)
    (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ l k : Fin 3,
      ContDiffAt ℝ ∞ (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k) x ∧
      ‖physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x‖ ≤ Q*eta/(actualReferenceBeta g L q dr Ar p x) ∧
      ‖fderiv ℝ (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k) x‖ ≤ Q*eta := by
  classical
  let scalarWitness := exists_physical_firstCoordinateWeight_uniform_first_caps g g2 hg hg2 L y0 ρ
  let Ma : ℝ := Classical.choose scalarWitness
  have scalarFacts := Classical.choose_spec scalarWitness
  have hMa := scalarFacts.1
  have hscalar := scalarFacts.2
  let jetWitness := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _) 1
  let J : ℝ := Classical.choose jetWitness
  have jetFacts := Classical.choose_spec jetWitness
  have hJ := jetFacts.1
  have hjet := jetFacts.2
  have hMa0 : 0 ≤ Ma := zero_le_one.trans hMa
  have hB0 : 0 ≤ data.M := data.M_nonneg
  have hB1 : 0 ≤ data.M*data.KT := mul_nonneg data.M_nonneg data.KT_pos.le
  refine ⟨leadingCoefficientBudget Ma data.M (data.M*data.KT) J,?_,?_⟩
  · unfold leadingCoefficientBudget
    positivity
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs l k
  have hG (i j : Fin 3) := (data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i j).2.1
  have ha (i : Fin 3) := hscalar q hq x hx dr Ar p l i
  have hc (j : Fin 3) := hscalar q hq x hx dr Ar p k j
  have hjet' : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x := by
    simpa only [norm_iteratedFDeriv_one,pow_one,actualReferenceBeta,J,jetWitness]
      using (hjet q hq dr hdr hdr1 Ar hAr p hp x hx).1
  exact weightedGainedCoefficient_form_caps Ma data.M (data.M*data.KT) J
    hMa0 hB0 hB1 hJ.le (referenceRadius dr Ar p L)
    (fun i y => firstCoordinateWeight g g2 L l i ((Tq dr Ar p q) y))
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => data.Cl i j ((Tq dr Ar p q) y)) x
    (contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
    (fun i => (ha i).1.contDiffAt) (fun j => (hc j).1.contDiffAt) (fun i j => (hG i j).1)
    (fun i => by simpa only [Real.norm_eq_abs] using (ha i).2.1)
    (fun i => (ha i).2.2)
    (fun j => by simpa only [Real.norm_eq_abs] using (hc j).2.1)
    (fun j => (hc j).2.2)
    (fun i j => (hG i j).2.1) (fun i j => (hG i j).2.2)
    (actualReferenceBeta g L q dr Ar p x) eta
    (referenceRadius_pos dr Ar p L x hdr hAr).le hb heta (heta0.trans data.eta0_le) hs hjet'

/-- Exact signed leading graph on the actual room; the physical threshold lemma supplies ht. -/
theorem physicalLeadingCoefficient_gain_graph_on_room (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom data.δ) :
    (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x).comp IH =
      ((-(referenceRadius dr Ar p L x)^2) •
        orderedReverseFirstCoordinateFactorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l ((Tq dr Ar p q) x)).comp
        (((referenceRadius dr Ar p L x)^2) •
          ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k ((Tq dr Ar p q) x)) -
      (((referenceRadius dr Ar p L x)^2) •
        ActualHigherSFirstCoefficientJets.firstCoordinateFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k ((Tq dr Ar p q) x)).comp
        ((-(referenceRadius dr Ar p L x)^2) •
          orderedReverseFirstCoordinateFactorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l ((Tq dr Ar p q) x)) := by
  exact actual_first_weighted_gain_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data.δ0 data.germs data.Gcoord data.GN data.Cl ((Tq dr Ar p q) x)
    (fun i j u => data.high_graph i j _ ht u)
    (fun i j => (data.low_graph i j _ ht).1) g2 l k (referenceRadius dr Ar p L x)

/-- The literal full ordered signed leading graph at a physical point. -/
def physicalLeadingGainGraph (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3) : Prop :=
    (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x).comp IH =
      ((-(referenceRadius dr Ar p L x)^2) •
        orderedReverseFirstCoordinateFactorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l ((Tq dr Ar p q) x)).comp
        (((referenceRadius dr Ar p L x)^2) •
          ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k ((Tq dr Ar p q) x)) -
      (((referenceRadius dr Ar p L x)^2) •
        ActualHigherSFirstCoefficientJets.firstCoordinateFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k ((Tq dr Ar p q) x)).comp
        ((-(referenceRadius dr Ar p L x)^2) •
          orderedReverseFirstCoordinateFactorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l ((Tq dr Ar p q) x))

/-- Actual radius smallness supplies the leading graph room, uniformly before all profiles. -/
theorem exists_actual_leading_gain_graph_threshold (hL : 0 < L)
    (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) :
    ∃ etaG : ℝ, 0 < etaG ∧ etaG ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaG →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ l k : Fin 3,
      physicalLeadingGainGraph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x := by
  let gw := exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ data.δ data.δ_pos
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaRoom : ℝ := Classical.choose gw
  have gf := Classical.choose_spec gw
  refine ⟨min data.eta0 etaRoom, lt_min data.eta0_pos gf.1, min_le_left _ _, ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x hx hxBall hb hs l k
  have hguard := gf.2.2 q hq dr hdr hdr1 Ar hAr p hp eta heta
    (hetaG.trans (min_le_right _ _)) x hx hxBall hb hs
  have hmem := higherSParam_eventually_mem y0 ρ data.δ L dr Ar q p hdr hAr x hguard
  exact physicalLeadingCoefficient_gain_graph_on_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 dr Ar p q l k x hmem.self_of_nhds

attribute [local irreducible] physicalLeadingCoefficient

open PrincipalCommutator ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ReferenceDensityBounds MeasureTheory ActualFiniteHarmonicModel

/-- Canonical coordinate conversion in the small concrete operator space. -/
private theorem leading_coordinate_derivative_cap {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : R3 → V)
    (x : R3) (i : Fin 3) (M : ℝ) (hcap : ‖fderiv ℝ f x‖ ≤ M) :
    ‖directionalFDeriv (coordinateDirection i) f x‖ ≤ M := by
  calc
    _ ≤ ‖fderiv ℝ f x‖*‖coordinateDirection i‖ := (fderiv ℝ f x).le_opNorm _
    _ = ‖fderiv ℝ f x‖ := by rw [norm_coordinateDirection,mul_one]
    _ ≤ M := hcap

/-- The actual leading signed second row, with one constant selected before all profiles and supports. -/
theorem exists_actual_leading_signed_second_form_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ CLead : ℝ, 0 ≤ CLead ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ u : R3 → Half, ContDiff ℝ ∞ u → (∀ x ∉ K, u x = 0) →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ l k : Fin 3,
      Integrable (fun x => referenceDensityFamily g L (q,x)*PP (u x)
        (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x
          (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x))) ∧
      |∫ x, referenceDensityFamily g L (q,x)*PP (u x)
        (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x
          (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x))| ≤
        CLead*eta*coordinateEnergy coordinateDirection (fun x => referenceDensityFamily g L (q,x))
          (actualReferenceBeta g L q dr Ar p) u := by
  classical
  let capWitness := exists_actual_leading_coefficient_uniform_first_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg data g2 hg2
  let Q : ℝ := Classical.choose capWitness
  have capFacts := Classical.choose_spec capWitness
  have hQ := capFacts.1
  have hcaps := capFacts.2
  let densityWitness := ActualHigherSScalarCommutatorNativeForm.exists_density_coordinate_relative_bound
    g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Md : ℝ := Classical.choose densityWitness
  have densityFacts := Classical.choose_spec densityWitness
  have hMd := densityFacts.1
  have hdmu := densityFacts.2
  refine ⟨‖PL‖*Q*(Md+3),by positivity,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball u hu h0 hb hs l k
  have hclosed (x : R3) (hx : x ∈ K) : x ∈ closedBall y0 ρ := ball_subset_closedBall (hKball hx)
  have hc (x : R3) (hx : x ∈ K) :=
    hcaps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x (hclosed x hx) (hKball hx) (hb x hx) (hs x hx) l k
  have hm : ContDiff ℝ ∞ (fun x => referenceDensityFamily g L (q,x)) := by
    simpa only [Function.comp_def,id] using
      (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmu (x : R3) : 0 ≤ referenceDensityFamily g L (q,x) := (referenceDensityFamily_pos g hg L (q,x)).le
  have hderiv : ∀ x ∈ K, ‖directionalFDeriv (coordinateDirection l) (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k) x‖ ≤ Q*eta := by
    intro x hx
    exact leading_coordinate_derivative_cap (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k) x l (Q*eta) (hc x hx).2.2
  have result := weighted_second_operator_form_bound PL (fun x => referenceDensityFamily g L (q,x))
    (actualReferenceBeta g L q dr Ar p) u
    (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k)
    K hK hm (continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr)
    (actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp) hu h0
    (fun x hx => (hc x hx).1) Q Md eta hQ (zero_le_one.trans hMd) heta hmu hb l k
    (fun x hx => (hc x hx).2.1) hderiv (fun x hx => hdmu q hq x (hclosed x hx) l)
  simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using result


open ActualHigherSScalarCommutatorNativeForm ActualFiniteHarmonicCore

/-- All nine original ordered leading second rows, acting on the full Sobolev half input. -/
def actualLeadingSignedSecondNeg (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Neg :=
  ∑ l : Fin 3, ∑ k : Fin 3,
    physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x
      (directionalFDeriv (coordinateDirection l)
        (directionalFDeriv (coordinateDirection k) (halfInput hO hD F)) x)

/-- The complete nine-row leading weak form is small in the original reference energy. -/
theorem exists_actual_leading_signed_second_reference_form (hL : 0 < L)
    (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ CRef : ℝ, 0 < CRef ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*PP (halfInput hO hD F x)
        (actualLeadingSignedSecondNeg g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x)) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*PP (halfInput hO hD F x)
        (actualLeadingSignedSecondNeg g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x)| ≤
        CRef*eta*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  let formWitness := exists_actual_leading_signed_second_form_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg data g2 hg2
  let CLead : ℝ := Classical.choose formWitness
  have formFacts := Classical.choose_spec formWitness
  have hCL := formFacts.1
  have hform := formFacts.2
  let energyWitness := exists_halfInput_coordinate_reference_integral_bound hO hD g hg L hL
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let Cr : ℝ := Classical.choose energyWitness
  have energyFacts := Classical.choose_spec energyWitness
  have hCr := energyFacts.1
  have henergy := energyFacts.2
  refine ⟨9*(CLead+1)*Cr, by positivity, ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs
  let u := halfInput hO hD F
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta := actualReferenceBeta g L q dr Ar p
  let row : Fin 3 → Fin 3 → R3 → ℝ := fun l k x => mu x*PP (u x)
    (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x
      (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x))
  have hu : ContDiff ℝ ∞ u := contDiff_halfInput hO hD F
  have hzero : ∀ x ∉ K, u x = 0 := fun x hx =>
    halfInput_eq_zero_off hO hD F x (fun ht => hx (hsupp ht))
  have hrow (l k : Fin 3) := hform q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball u hu hzero hb hs l k
  have hI := ActualHigherSIntegratedPairing.integrable_sum2 row (fun l k => (hrow l k).1)
  have hIEq := ActualHigherSIntegratedPairing.integral_sum2 row (fun l k => (hrow l k).1)
  have hfun : (fun x => mu x*PP (u x)
      (actualLeadingSignedSecondNeg g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x)) =
      (fun x => ∑ l : Fin 3, ∑ k : Fin 3, row l k x) := by
    funext x
    simp only [actualLeadingSignedSecondNeg, halfPairing_sum_right, Finset.mul_sum, row, u]
  have hbcont := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hbpos := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp
  have hsub : tsupport F.val ⊆ closedBall y0 ρ := fun x hx => ball_subset_closedBall (hKball (hsupp hx))
  have hE := henergy q hq dr Ar p hdr hAr hp F hsub (fun x hx => hb x (hsupp hx))
  have hN := integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q beta hbcont hbpos F
  let E := ∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x
  have hE0 : 0 ≤ E := integral_nonneg (fun x =>
    mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbpos x).le F x))
  refine ⟨hfun.symm ▸ hI, hN, ?_⟩
  have hIntegral := congrArg (fun f : R3 → ℝ => ∫ x, f x) hfun
  calc
    _ = |∑ l : Fin 3, ∑ k : Fin 3, ∫ x, row l k x| := congrArg abs (hIntegral.trans hIEq)
    _ = ‖∑ l : Fin 3, ∑ k : Fin 3, ∫ x, row l k x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑ l : Fin 3, ‖∑ k : Fin 3, ∫ x, row l k x‖ := norm_sum_le _ _
    _ ≤ ∑ l : Fin 3, ∑ k : Fin 3, ‖∫ x, row l k x‖ := Finset.sum_le_sum (fun l _ => norm_sum_le _ _)
    _ = ∑ l : Fin 3, ∑ k : Fin 3, |∫ x, row l k x| := by simp only [Real.norm_eq_abs]
    _ ≤ ∑ _l : Fin 3, ∑ _k : Fin 3, CLead*eta*coordinateEnergy coordinateDirection mu beta u :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun k _ => (hrow l k).2))
    _ = 9*CLead*eta*coordinateEnergy coordinateDirection mu beta u := by simp only [Fin.sum_univ_three]; ring
    _ ≤ 9*CLead*eta*(Cr*E) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ (9*(CLead+1)*Cr)*eta*E := by
      have hpos : 0 ≤ 9*Cr*eta*E := by positivity
      nlinarith only [hpos]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
