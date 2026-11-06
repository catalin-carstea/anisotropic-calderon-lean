import Calderon.ActualLowerUSSecondRowCoefficients

/-!
This module concerns only the second-base lower U/S weak row, with full physical
E coefficients.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualPiJacobiRadialGainedRows
  ActualMixedAngularPairedGains ActualHigherSLeadingBracketGain ActualHigherSCoordinateWeightBounds
  SmoothMetricFrame MovingFrameConnection ConformalDepth ReferenceWeightedApproximation
  ReferenceDensityBounds NormalizedPrincipalMetric ActualPhysicalMixedFirst
  FixedParameterProfilePullback

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
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

local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

local notation "FG" => firstGainCombination
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "TC" => lowerUSSecondCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

attribute [local irreducible] lowerUSSecondCoefficient firstGainCombination firstAngularGain
  firstAngularCoefficient nativeBAngularPartMass firstCoordinateWeight referenceRadius

/-- Internally produced fixed-g2 joint norm cap, with no assumed analytic
budget. The original coefficient mass is retained explicitly. -/
theorem exists_lowerUSSecondCoefficient_joint_bound (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr Ar : ℝ, ∀ p : ℕ, ∀ x ∈ closedBall y0 ρ,
      (Tq dr Ar p q) x ∈ ParamRoom δ → (Tq dr Ar p q) x ∈ ParamRoom mixed.δ →
      ∀ i j : Fin 3,
      ‖TC mixed δ gen g2 q dr Ar p i j x‖ ≤
        C2 * (referenceRadius dr Ar p L x)^2 * nativeBAngularPartMass g g2 L q dr Ar p i x := by
  obtain ⟨MG,hMG,hG⟩ := exists_firstAngularGain_joint_cap
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ gen
  obtain ⟨MW,hMW,hW⟩ := exists_coordinateWeightBase_uniform_first_caps g g2 hg hg2 L y0 ρ
  refine ⟨3*MW*MG,by positivity,?_⟩
  intro q hq dr Ar p x hx htG htM i j
  have hFG (b : Fin 3) : ‖FG mixed δ gen g2 q dr Ar p i b x‖ ≤
      MG * nativeBAngularPartMass g g2 L q dr Ar p i x :=
    norm_firstGainCombination_le g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen g2 q dr Ar p i b x MG hMG.le
      (fun v => hG _ htG htM b v)
  have hweight (b : Fin 3) : |firstCoordinateWeight g g2 L j b ((Tq dr Ar p q) x)| ≤ MW := by
    rw [firstCoordinateWeight_eq_base]
    exact (hW q hq x hx j b).1
  have hn := norm_nonneg_smul_three_sum_le ((referenceRadius dr Ar p L x)^2) MW
    (MG*nativeBAngularPartMass g g2 L q dr Ar p i x)
    (sq_nonneg (referenceRadius dr Ar p L x)) (by linarith : 0 ≤ MW)
    (fun b : Fin 3 => firstCoordinateWeight g g2 L j b ((Tq dr Ar p q) x))
    (fun b : Fin 3 => FG mixed δ gen g2 q dr Ar p i b x) hweight hFG
  calc
    _ ≤ (referenceRadius dr Ar p L x)^2 *
        (3*MW*(MG*nativeBAngularPartMass g g2 L q dr Ar p i x)) := by
      unfold lowerUSSecondCoefficient
      exact hn
    _ = _ := by ring

/-- Fixed second metric intermediate, with constants before every actual
profile, base point, compact support and finite/angular input. The parameter
memberships expose the exact domain of the graph above. -/
def SecondRowUniformProfileBound (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) : Prop :=
  ∃ C2 : ℝ, 0 < C2 ∧ ∃ eta2 : ℝ, 0 < eta2 ∧ eta2 ≤ data.eta0 ∧ eta2 ≤ 1 ∧
    ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta2 →
    ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
    1 ≤ actualReferenceBeta g L q dr Ar p x →
    referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
    CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
      eta * referenceRadius dr Ar p L x →
    (Tq dr Ar p q) x ∈ ParamRoom δ ∧
    (Tq dr Ar p q) x ∈ ParamRoom mixed.δ ∧
    (Tq dr Ar p q) x ∈ ParamRoom data.δ ∧
    ∀ i j : Fin 3, ‖TC mixed δ gen g2 q dr Ar p i j x‖ ≤
      C2 * eta / actualReferenceBeta g L q dr Ar p x

/-- Derive the actual profile cap from original H8 coefficients and the
retained low endpoints; no arbitrary operator norm budget is assumed. -/
theorem secondRowUniformProfileBound_of_rooms (mixed : MRoom) (δ : ℝ) (hδ : 0 < δ)
    (gen : GRoom δ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hL : 0 < L) :
    SecondRowUniformProfileBound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen g2 := by
  obtain ⟨C2,hC2,hRow⟩ := exists_lowerUSSecondCoefficient_joint_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ gen g2 hg2
  obtain ⟨CB,hCB,hB⟩ := exists_nativeBAngularPartMass_uniform_smallness
    hO hD g g2 hg hg2 L hL (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨etaG,hEtaG,hEtaG1,hGuardG⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ δ hδ (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨etaM,hEtaM,hEtaM1,hGuardM⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ mixed.δ mixed.δ_pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨etaD,hEtaD,hEtaD1,hGuardD⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ data.δ data.δ_pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  let eta2 := min data.eta0 (min etaG (min etaM etaD))
  have hEta2 : 0 < eta2 := lt_min data.eta0_pos (lt_min hEtaG (lt_min hEtaM hEtaD))
  have hEta20 : eta2 ≤ data.eta0 := min_le_left _ _
  have hEta2G : eta2 ≤ etaG := (min_le_right _ _).trans (min_le_left _ _)
  have hEta2M : eta2 ≤ etaM :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hEta2D : eta2 ≤ etaD :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨C2*CB,mul_pos hC2 hCB,eta2,hEta2,hEta20,hEta2G.trans hEtaG1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta2 x hx hxBall hb hs hH8
  have heta1 : eta ≤ 1 := heta2.trans (hEta2G.trans hEtaG1)
  have htG : (Tq dr Ar p q) x ∈ ParamRoom δ :=
    (higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x
      (hGuardG q hq dr hdr hdr1 Ar hAr p hp eta heta (heta2.trans hEta2G) x hx hxBall hb hs)).self_of_nhds
  have htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ :=
    (higherSParam_eventually_mem y0 ρ mixed.δ L dr Ar q p hdr hAr x
      (hGuardM q hq dr hdr hdr1 Ar hAr p hp eta heta (heta2.trans hEta2M) x hx hxBall hb hs)).self_of_nhds
  have htD : (Tq dr Ar p q) x ∈ ParamRoom data.δ :=
    (higherSParam_eventually_mem y0 ρ data.δ L dr Ar q p hdr hAr x
      (hGuardD q hq dr hdr hdr1 Ar hAr p hp eta heta (heta2.trans hEta2D) x hx hxBall hb hs)).self_of_nhds
  refine ⟨htG,htM,htD,?_⟩
  intro i j
  have hmass := hB q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hH8 hs i
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hbpos : 0 < beta := by change 1 ≤ beta at hb; linarith
  have hb2 : 1 ≤ beta^2 := by change 1 ≤ beta at hb; nlinarith
  have hr1 : r ≤ 1 := by
    have hh : r ≤ r*beta^2 := by nlinarith
    exact (hh.trans hs).trans heta1
  have hr2 : r^2 ≤ 1 := by nlinarith
  have hrate : 0 ≤ eta/beta := div_nonneg heta hbpos.le
  calc
    ‖TC mixed δ gen g2 q dr Ar p i j x‖ ≤
        C2*r^2*nativeBAngularPartMass g g2 L q dr Ar p i x :=
      hRow q hq dr Ar p x hx htG htM i j
    _ ≤ C2*r^2*(CB*eta/beta) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hC2.le (sq_nonneg r))
    _ = (C2*CB)*(r^2*(eta/beta)) := by ring
    _ ≤ (C2*CB)*(eta/beta) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr2 hrate)
        (mul_nonneg hC2.le hCB.le)
    _ = C2*CB*eta/beta := by ring

/-- Both actual endpoint rooms and all fixed-g2 constants are produced before
profiles. All retained witnesses are exactly data.δ0/data.germs. -/
theorem exists_retained_secondRow_uniform_profile_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ mixed : MRoom, ∃ δ : ℝ, 0 < δ ∧ ∃ gen : GRoom δ,
      SecondRowUniformProfileBound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data mixed δ gen g2 := by
  obtain ⟨mixed⟩ := exists_actual_mixedAngular_physical_endpoint_room
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hL hreg hKernel
    data.δ0 data.δ0_pos data.germs
  obtain ⟨δ,hδ,_hδ0,_hδρ,_hOmega,⟨gen⟩⟩ := exists_retained_generator_paired_endpoints
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
    data.δ0 data.δ0_pos data.germs
  exact ⟨mixed,δ,hδ,gen,secondRowUniformProfileBound_of_rooms
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ hδ gen g2 hg2 hL⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
