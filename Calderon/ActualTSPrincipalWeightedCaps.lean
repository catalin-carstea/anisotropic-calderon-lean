import Calderon.ActualTSPrincipalAngularCaps
import Calderon.ActualTSPrincipalWeightedCoefficients
import Calderon.ActualMixedAngularFullOutputForm
import Calderon.ActualHigherSScalarCommutatorNativeForm
import Calderon.ActualHigherSIntegratedPairing

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalWeightedCaps
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

private lemma use_scalar_family_cap {P : ℝ → Prop} {Result : Prop}
    (h : ∃ M : ℝ, 1 ≤ M ∧ P M)
    (use : ∀ M : ℝ, 1 ≤ M → P M → Result) : Result := by
  rcases h with ⟨M,hM,hP⟩
  exact use M hM hP

/-- The original scalar factors and full R² weight act on any of the two actual principal families. -/
private lemma principal_weighted_pointwise_caps
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (x : R3) (l k : Fin 3)
    (Mf Ms B0 B1 J eta : ℝ) (hMf : 1 ≤ Mf) (hMs : 1 ≤ Ms)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hJ : 0 ≤ J)
    (hdr : 0 < dr) (hAr : 0 < Ar)
    (G : Fin 3 → Fin 3 → R3 → Hi →L[ℝ] Neg)
    (hFcap : ∀ i : Fin 3,
      ContDiffAt ℝ ∞ (fun y => referenceMetricGramFrame g L (q,y) i l) x ∧
      |referenceMetricGramFrame g L (q,x) i l| ≤ Mf ∧
      ‖fderiv ℝ (fun y => referenceMetricGramFrame g L (q,y) i l) x‖ ≤ Mf)
    (hScap : ∀ j : Fin 3,
      ContDiffAt ℝ ∞ (fun y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y)) x ∧
      |firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x)| ≤ Ms ∧
      ‖fderiv ℝ (fun y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y)) x‖ ≤ Ms)
    (hGcap : ∀ i j : Fin 3,
      ContDiffAt ℝ ∞ (G i j) x ∧ ‖G i j x‖ ≤ B0 ∧ ‖fderiv ℝ (G i j) x‖ ≤ B1)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (hjet : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x) :
    let coeff := weightedMixedSecondCoefficient (referenceRadius dr Ar p L)
      (fun i y => referenceMetricGramFrame g L (q,y) i l)
      (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y)) G
    ContDiffAt ℝ ∞ coeff x ∧
      ‖coeff x‖ ≤ mixedCoefficientBudget (Mf+Ms) B0 B1 J*eta/(actualReferenceBeta g L q dr Ar p x) ∧
      ‖fderiv ℝ coeff x‖ ≤ mixedCoefficientBudget (Mf+Ms) B0 B1 J*eta := by
  exact weightedMixedSecondCoefficient_first_caps (E := Hi) (F := Neg) (Mf+Ms) B0 B1 J
    (add_nonneg (zero_le_one.trans hMf) (zero_le_one.trans hMs)) hB0 hB1 hJ
    (referenceRadius dr Ar p L)
    (fun i y => referenceMetricGramFrame g L (q,y) i l)
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y)) G x
    (contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
    (fun i => (hFcap i).1) (fun j => (hScap j).1) (fun i j => (hGcap i j).1)
    (fun i => by simpa only [Real.norm_eq_abs] using
      ((hFcap i).2.1.trans (le_add_of_nonneg_right (zero_le_one.trans hMs))))
    (fun i => (hFcap i).2.2.trans (le_add_of_nonneg_right (zero_le_one.trans hMs)))
    (fun j => by simpa only [Real.norm_eq_abs] using
      ((hScap j).2.1.trans (le_add_of_nonneg_left (zero_le_one.trans hMf))))
    (fun j => (hScap j).2.2.trans (le_add_of_nonneg_left (zero_le_one.trans hMf)))
    (fun i j => (hGcap i j).2.1) (fun i j => (hGcap i j).2.2)
    (actualReferenceBeta g L q dr Ar p x) eta (referenceRadius_pos dr Ar p L x hdr hAr).le
    hb heta heta1 hs hjet

/-- For fixed g2, one pre-profile constant bounds the literal principal coefficient and its true transpose. -/
theorem exists_principalCoordinate_uniform_first_caps (hL : 0 < L)
    (data : PrincipalAngularPhysicalRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ l k : Fin 3,
        (ContDiffAt ℝ ∞ (PC g2 dr Ar p q l k) x ∧
          ‖PC g2 dr Ar p q l k x‖ ≤ Q*eta/(actualReferenceBeta g L q dr Ar p x) ∧
          ‖fderiv ℝ (PC g2 dr Ar p q l k) x‖ ≤ Q*eta) ∧
        (ContDiffAt ℝ ∞ (PCt g2 dr Ar p q l k) x ∧
          ‖PCt g2 dr Ar p q l k x‖ ≤ Q*eta/(actualReferenceBeta g L q dr Ar p x) ∧
          ‖fderiv ℝ (PCt g2 dr Ar p q l k) x‖ ≤ Q*eta) := by
  apply use_scalar_family_cap (exists_metricFrame_uniform_first_caps g hg L y0 ρ)
  intro Mf hMf hFrame
  apply use_scalar_family_cap
    (exists_physical_firstCoordinateWeight_uniform_first_caps g g2 hg hg2 L y0 ρ)
  intro Ms hMs hScalar
  let jetWitness := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL (closedBall y0 ρ) (isCompact_closedBall _ _) 1
  let J : ℝ := Classical.choose jetWitness
  have jetFacts := Classical.choose_spec jetWitness
  have hJ := jetFacts.1
  have hB0 := data.M_nonneg
  have hB1 : 0 ≤ data.M*data.KT := mul_nonneg data.M_nonneg data.KT_pos.le
  refine ⟨mixedCoefficientBudget (Mf+Ms) data.M (data.M*data.KT) J,?_,?_⟩
  · unfold mixedCoefficientBudget
    positivity
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs l k
  have hFc (i : Fin 3) := hFrame q hq x hx i l
  have hSc (j : Fin 3) := hScalar q hq x hx dr Ar p k j
  have hG (i j : Fin 3) :=
    (data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs).2 i j
  have hjet : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤
      J*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x := by
    simpa only [norm_iteratedFDeriv_one,pow_one,actualReferenceBeta,J,jetWitness]
      using (jetFacts.2 q hq dr hdr hdr1 Ar hAr p hp x hx).1
  constructor
  · exact principal_weighted_pointwise_caps g L g2 q dr Ar p x l k Mf Ms data.M (data.M*data.KT) J eta
      hMf hMs hB0 hB1 hJ.le hdr hAr
      (fun i j y => PK i j ((Tq dr Ar p q) y))
      (fun i => ⟨(hFc i).1.contDiffAt,(hFc i).2⟩)
      (fun j => ⟨(hSc j).1.contDiffAt,(hSc j).2⟩)
      (fun i j => (hG i j).1) hb heta (heta0.trans data.eta0_le) hs hjet
  · exact principal_weighted_pointwise_caps g L g2 q dr Ar p x l k Mf Ms data.M (data.M*data.KT) J eta
      hMf hMs hB0 hB1 hJ.le hdr hAr
      (fun i j y => PT i j ((Tq dr Ar p q) y))
      (fun i => ⟨(hFc i).1.contDiffAt,(hFc i).2⟩)
      (fun j => ⟨(hSc j).1.contDiffAt,(hSc j).2⟩)
      (fun i j => (hG i j).2) hb heta (heta0.trans data.eta0_le) hs hjet


/-- Actual ordinary/W neighborhood membership proves the true transpose pairing on a neighborhood. -/
lemma principalCoordinate_pairing_germ
    (ordinary : PrincipalOrdinaryRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (hOrd : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom ordinary.δ)
    (hW : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom δ0) :
    ∀ᶠ y in 𝓝 x, ∀ u1 u2 : Hi,
      highDualPairingL u2 (PC g2 dr Ar p q l k y u1)=
        highDualPairingL u1 (PCt g2 dr Ar p q l k y u2) := by
  filter_upwards [hOrd,hW] with y hyO hyW
  intro u1 u2
  exact principalCoordinate_paired hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    hreg δ0 W g2 dr Ar p q l k y hyW
    (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      ordinary.room_sub ((Tq dr Ar p q) y).1 hyO.1) u1 u2

/-- One original strict profile threshold supplies the full actual principal pairing germ, before g2. -/
theorem exists_principalCoordinate_pairing_profile_room (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W) :
    ∃ etaP : ℝ, 0 < etaP ∧ etaP ≤ data.eta0 ∧
      ∀ g2 : MatrixField, ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaP →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ l k : Fin 3, ∀ᶠ y in 𝓝 x, ∀ u1 u2 : Hi,
        highDualPairingL u2 (PC g2 dr Ar p q l k y u1)=
          highDualPairingL u1 (PCt g2 dr Ar p q l k y u2) := by
  let ordinary := Classical.choice (exists_principalOrdinaryRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg)
  let δ : ℝ := min ordinary.δ data.δ
  have hd : 0 < δ := lt_min ordinary.δ_pos data.δ_pos
  let guardWitness := exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ δ hd
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaRoom : ℝ := Classical.choose guardWitness
  have guardFacts := Classical.choose_spec guardWitness
  refine ⟨min data.eta0 etaRoom,lt_min data.eta0_pos guardFacts.1,min_le_left _ _,?_⟩
  intro g2 q hq dr hdr hdr1 Ar hAr p hp eta heta hetaP x hx hxBall hb hs l k
  have hGuard := guardFacts.2.2 q hq dr hdr hdr1 Ar hAr p hp eta heta
    (hetaP.trans (min_le_right _ _)) x hx hxBall hb hs
  have hmem := higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x hGuard
  have hOrd : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom ordinary.δ :=
    hmem.mono (fun y hy => ⟨commonRoom_mono y0 ρ (min_le_left _ _) hy.1,hy.2⟩)
  have hW : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom δ0 :=
    hmem.mono (fun y hy => ⟨commonRoom_mono y0 ρ
      ((min_le_right _ _).trans data.δ_le0) hy.1,hy.2⟩)
  exact principalCoordinate_pairing_germ hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    ordinary hreg δ0 W g2 dr Ar p q l k x hOrd hW

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalWeightedCaps
