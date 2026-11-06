import Calderon.ActualLeadingFullOutputCore
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

local notation "CH" => physicalLeadingHighCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "NH" => actualLeadingSignedSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "NN" => actualLeadingSignedSecondNeg g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "NO" => actualLeadingSignedSecondOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room


attribute [local irreducible] physicalLeadingHighCoefficient physicalLeadingCoefficient

/-- A supported input has zero concrete second-sum output away from its closed support. -/
theorem leading_second_sum_eq_zero_off
    (A : Fin 3 → Fin 3 → R3 → Hi →L[ℝ] Half) (u : R3 → Hi)
    (K : Set R3) (hK : IsClosed K) (hzero : ∀ x ∉ K, u x = 0)
    (x : R3) (hx : x ∉ K) :
    (∑ l : Fin 3, ∑ k : Fin 3, A l k x
      (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x)) = 0 := by
  have hd0 (k : Fin 3) : ∀ y ∉ K, directionalFDeriv (coordinateDirection k) u y = 0 :=
    fun y hy => directional_eq_zero_off u _ hK hzero _ y hy
  have hdd0 (l k : Fin 3) : ∀ y ∉ K,
      directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) y = 0 :=
    fun y hy => directional_eq_zero_off _ _ hK (hd0 k) _ y hy
  apply Finset.sum_eq_zero
  intro l _
  apply Finset.sum_eq_zero
  intro k _
  rw [hdd0 l k x hx,map_zero]

/-- All actual leading rows vanish off the original support by derivative locality. -/
theorem actualLeadingSignedSecondHalf_eq_zero_off (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (hx : x ∉ tsupport F.val) :
    NH hreg data g2 dr Ar p q F x = 0 := by
  have built := leading_second_sum_eq_zero_off
    (fun l k => CH hreg data g2 dr Ar p q l k)
    (ActualHigherSFormation.higherSInput hO hD F) (tsupport F.val) (isClosed_tsupport F.val)
    (higherSInput_eq_zero_off hO hD F) x hx
  unfold actualLeadingSignedSecondHalf
  endpoint_literal_transport built

/-- The genuine Half and full physical outputs are smooth compact and preserve input support. -/
theorem actualLeadingSignedSecondOut_regular (hreg : FixedDirichletRegularity)
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
    ContDiff ℝ ∞ (NH hreg data g2 dr Ar p q F) ∧
    tsupport (NH hreg data g2 dr Ar p q F) ⊆ tsupport F.val ∧
    HasCompactSupport (NH hreg data g2 dr Ar p q F) ∧
    ContDiff ℝ ∞ (NO hreg data g2 dr Ar p q F) ∧
    tsupport (NO hreg data g2 dr Ar p q F) ⊆ tsupport F.val ∧
    HasCompactSupport (NO hreg data g2 dr Ar p q F) := by
  have hNH : ContDiff ℝ ∞ (NH hreg data g2 dr Ar p q F) :=
    actualLeadingSignedSecondHalf_contDiff
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2
      dr Ar p q hq hdr hdr1 hAr hp eta heta heta0 F hball hb hs
  have hzNH : ∀ x ∉ tsupport F.val, NH hreg data g2 dr Ar p q F x = 0 :=
    actualLeadingSignedSecondHalf_eq_zero_off
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F
  have hSupportNH : Function.support (NH hreg data g2 dr Ar p q F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hnot
    exact hx (hzNH x hnot)
  have hNHsupp : tsupport (NH hreg data g2 dr Ar p q F) ⊆ tsupport F.val :=
    closure_minimal hSupportNH (isClosed_tsupport F.val)

  have hNHc : HasCompactSupport (NH hreg data g2 dr Ar p q F) := HasCompactSupport.intro F.property.2.1 hzNH

  have hNO : ContDiff ℝ ∞ (NO hreg data g2 dr Ar p q F) :=
    contDiff_leading_physical_embedding hO hD (NH hreg data g2 dr Ar p q F) hNH
  have hzNO : ∀ x ∉ tsupport F.val, NO hreg data g2 dr Ar p q F x = 0 := by
    intro x hx
    simp only [actualLeadingSignedSecondOut,hzNH x hx,map_zero]
  have hSupportNO : Function.support (NO hreg data g2 dr Ar p q F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hnot
    exact hx (hzNO x hnot)
  have hNOsupp : tsupport (NO hreg data g2 dr Ar p q F) ⊆ tsupport F.val :=
    closure_minimal hSupportNO (isClosed_tsupport F.val)
  have hNOc : HasCompactSupport (NO hreg data g2 dr Ar p q F) := HasCompactSupport.intro F.property.2.1 hzNO

  exact ⟨hNH,hNHsupp,hNHc,hNO,hNOsupp,hNOc⟩

/-- The original leading reference bound now has a full smooth physical output and literal signed graph. -/
theorem exists_actual_leading_full_output_reference_form (hL : 0 < L)
    (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ CRef : ℝ, 0 < CRef ∧ ∃ etaG : ℝ, 0 < etaG ∧ etaG ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaG →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ContDiff ℝ ∞ (NO hreg data g2 dr Ar p q F) ∧
      tsupport (NO hreg data g2 dr Ar p q F) ⊆ tsupport F.val ∧
      HasCompactSupport (NO hreg data g2 dr Ar p q F) ∧
      (∀ x, JL (NH hreg data g2 dr Ar p q F x) = NN hreg data g2 dr Ar p q F x) ∧
      (∀ x ∈ K, ∀ l k : Fin 3, physicalLeadingGainGraph
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*⟪F.val x,NO hreg data g2 dr Ar p q F x⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,NO hreg data g2 dr Ar p q F x⟫_ℝ| ≤
        CRef*eta*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by

  obtain ⟨CRef,hC,hform⟩ := exists_actual_leading_signed_second_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg data g2 hg2
  let gw := exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ data.δ data.δ_pos
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaRoom : ℝ := Classical.choose gw
  have gf := Classical.choose_spec gw
  refine ⟨CRef,hC,min data.eta0 etaRoom,lt_min data.eta0_pos gf.1,min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K hK hKball F hsupp hb hs
  have heta0 : eta ≤ data.eta0 := hetaG.trans (min_le_left _ _)
  have hmem (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom data.δ := by
    have ht := gf.2.2 q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaG.trans (min_le_right _ _))
      x (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx)
    exact (higherSParam_eventually_mem y0 ρ data.δ L dr Ar q p hdr hAr x ht).self_of_nhds
  have hgraph := actualLeadingSignedSecondHalf_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F
    (fun x hx => hmem x (hsupp hx))
  have hregO := actualLeadingSignedSecondOut_regular
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2
    dr Ar p q hq hdr hdr1 hAr hp eta heta heta0 F (fun x hx => hKball (hsupp hx))
    (fun x hx => hb x (hsupp hx)) (fun x hx => hs x (hsupp hx))
  have hn := hform q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs
  have he : (fun x => referenceDensityFamily g L (q,x)*PP (halfInput hO hD F x)
      (NN hreg data g2 dr Ar p q F x)) =
      (fun x => referenceDensityFamily g L (q,x)*⟪F.val x,NO hreg data g2 dr Ar p q F x⟫_ℝ) := by
    funext x
    have hp := ActualHigherSPhysicalPairing.physical_pairing_of_graph hO hD F
      (NH hreg data g2 dr Ar p q F) (NN hreg data g2 dr Ar p q F) hgraph x
    have hp' : PP (halfInput hO hD F x) (NN hreg data g2 dr Ar p q F x) =
        ⟪F.val x,NO hreg data g2 dr Ar p q F x⟫_ℝ := by
      simpa only [halfInput,ActualHigherSFormation.higherSInput,actualLeadingSignedSecondOut] using hp
    exact congrArg (fun z : ℝ => referenceDensityFamily g L (q,x)*z) hp' 
  have hi := congrArg (fun f : R3 → ℝ => ∫ x, f x) he
  have hInt : Integrable (fun x => referenceDensityFamily g L (q,x)*
      ⟪F.val x,NO hreg data g2 dr Ar p q F x⟫_ℝ) :=
    Eq.mp (congrArg (fun f : R3 → ℝ => Integrable f) he) hn.1
  refine ⟨hregO.2.2.2.1,hregO.2.2.2.2.1,hregO.2.2.2.2.2,hgraph,?_,hInt,hn.2.1,?_⟩
  · intro x hx l k
    exact physicalLeadingCoefficient_gain_graph_on_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q l k x (hmem x hx)
  · calc
      |∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,NO hreg data g2 dr Ar p q F x⟫_ℝ| =
          |∫ x, referenceDensityFamily g L (q,x)*PP (halfInput hO hD F x)
            (NN hreg data g2 dr Ar p q F x)| := congrArg abs hi.symm
      _ ≤ CRef*eta*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := hn.2.2

/-- The leading full-output contract uses Main’s actual endpoint existence and one fixed record. -/
theorem exists_actual_leading_full_output_reference_form_of_trace_kernel (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ selectedRoom : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)),
    ∃ data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg,
    ∀ g2 : MatrixField, ∀ hg2 : IsAdmissibleMetric g2,
    ∃ CRef : ℝ, 0 < CRef ∧ ∃ etaG : ℝ, 0 < etaG ∧ etaG ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaG →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ContDiff ℝ ∞ (actualLeadingSignedSecondOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 dr Ar p q F) ∧
      tsupport (actualLeadingSignedSecondOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 dr Ar p q F) ⊆ tsupport F.val ∧
      HasCompactSupport (actualLeadingSignedSecondOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 dr Ar p q F) ∧
      (∀ x, JL (actualLeadingSignedSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 dr Ar p q F x) = actualLeadingSignedSecondNeg g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 dr Ar p q F x) ∧
      (∀ x ∈ K, ∀ l k : Fin 3, physicalLeadingGainGraph
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 dr Ar p q l k x) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*⟪F.val x,actualLeadingSignedSecondOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 dr Ar p q F x⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,actualLeadingSignedSecondOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 dr Ar p q F x⟫_ℝ| ≤
        CRef*eta*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨selectedRoom,⟨data⟩⟩ := exists_actual_fullE_physical_endpoint_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hL hreg hKernel
  refine ⟨selectedRoom,data,?_⟩
  intro g2 hg2
  exact exists_actual_leading_full_output_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hL hreg data g2 hg2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
