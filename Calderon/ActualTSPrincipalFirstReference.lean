import Calderon.ActualFullEGainedJointEndpoints
import Calderon.ActualTSPrincipalWeightedCaps
import Calderon.ActualTSPrincipalLowerReferenceOrders
import Calderon.ActualTSGainedFirstReference
import Calderon.ActualTSPrincipalPhysicalRegularity
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
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFirstReference
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
local notation "GCt" => gainedTransposeCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

private lemma symmetric_lower_abs_bound (a c d l r Kc Ka eta E : ℝ)
    (heq : a=(c+d)/2+(l-r)/2)
    (hc : |c| ≤ Kc*eta*E) (hd : |d| ≤ Kc*eta*E)
    (hl : |l| ≤ Ka*eta*E) (hr : |r| ≤ Ka*eta*E) :
    |a| ≤ (Kc+Ka)*eta*E := by
  rw [heq]
  calc
    _ ≤ |(c+d)/2|+|(l-r)/2| := abs_add_le _ _
    _ = |c+d|/2+|l-r|/2 := by simp only [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    _ ≤ (|c|+|d|)/2+(|l|+|r|)/2 := by
      have h1 := abs_add_le c d
      have h2 : |l-r| ≤ |l|+|r| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le l (-r)
      linarith only [h1,h2]
    _ ≤ (Kc+Ka)*eta*E := by nlinarith only [hc,hd,hl,hr]

private theorem principal_reference_fixed_spaces
    (mu : R3 → ℝ) (U : R3 → Hi) (A At C Ct : R3 → Hi →L[ℝ] Half)
    (K : Set R3) (hK : IsCompact K) (hm : ContDiff ℝ ∞ mu)
    (hu : ContDiff ℝ ∞ U) (hz : ∀ x ∉ K, U x=0)
    (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x) (hAt : ∀ x ∈ K, ContDiffAt ℝ ∞ At x)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (hCt : ∀ x ∈ K, ContDiffAt ℝ ∞ Ct x)
    (hAdj : ∀ x ∈ K, ∀ u v : Hi, highDualPairingL u (At x v)=highDualPairingL v (A x u))
    (hCadj : ∀ x ∈ K, ∀ u v : Hi, highDualPairingL u (Ct x v)=highDualPairingL v (C x u))
    (hSym : ∀ x ∈ K, A x+At x=C x+Ct x) (X Y : R3) (Kc Ka eta J : ℝ)
    (hc : |firstForm highDualPairingL mu U C X Y| ≤ Kc*eta*J)
    (hd : |firstForm highDualPairingL mu U C Y X| ≤ Kc*eta*J)
    (hl : |lowerForm highDualPairingL mu U A Y X| ≤ Ka*eta*J)
    (hr : |lowerForm highDualPairingL mu U A X Y| ≤ Ka*eta*J) :
    |firstForm highDualPairingL mu U A X Y| ≤ (Kc+Ka)*eta*J := by
  have heq := ActualTSPrincipalSymmetricFirstForm.principal_firstForm_eq_symmetric_gained_and_lower
    highDualPairingL mu U A At C Ct K hK hm hu hz hA hAt hC hCt hAdj hCadj hSym X Y
  exact symmetric_lower_abs_bound _ _ _ _ _ Kc Ka eta J heq hc hd hl hr

/-- Actual full principal first form in the original reference energy; fixed-g2 constant only. -/
theorem exists_principal_first_reference_form_bound (hL : 0 < L)
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
      |firstForm highDualPairingL (fun x => referenceDensityFamily g L (q,x))
        (ActualHigherSFormation.higherSInput hO hD F0) (PC g2 dr Ar p q l k)
        (coordinateDirection l) (coordinateDirection k)| ≤
      Bc*eta*∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F0 x := by
  classical
  let lowerWitness := ActualTSPrincipalLowerReferenceOrders.exists_principal_lower_reference_all_orders_bound
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hL hreg δ0 W data
  let etaK : ℝ := Classical.choose lowerWitness
  have lowerFacts := Classical.choose_spec lowerWitness
  let gainWitness := ActualTSGainedFirstReference.exists_gained_first_reference_form_bound
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hL hreg δ0 W data
  let etaC : ℝ := Classical.choose gainWitness
  have gainFacts := Classical.choose_spec gainWitness
  let ordinary := Classical.choice (exists_principalOrdinaryRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg)
  let δ : ℝ := min ordinary.δ data.δ
  have hd : 0 < δ := lt_min ordinary.δ_pos data.δ_pos
  let guardWitness := exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ δ hd
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaRoom : ℝ := Classical.choose guardWitness
  have guardFacts := Classical.choose_spec guardWitness
  refine ⟨min etaK (min etaC etaRoom),lt_min lowerFacts.1 (lt_min gainFacts.1 guardFacts.1),
    (min_le_left _ _).trans lowerFacts.2.1,?_⟩
  intro g2 hg2
  obtain ⟨Bk,hBk,hLower⟩ := lowerFacts.2.2 g2 hg2
  obtain ⟨Bc,hBc,hGain⟩ := gainFacts.2.2 g2 hg2
  refine ⟨Bc+Bk,add_pos hBc hBk,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 F0 hsupp hb hs l k
  have hetaK : eta ≤ etaK := heta0.trans (min_le_left _ _)
  have hetaC : eta ≤ etaC := heta0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaRoom : eta ≤ etaRoom := heta0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hetaData : eta ≤ data.eta0 := hetaK.trans lowerFacts.2.1
  let K : Set R3 := tsupport F0.val
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let U := ActualHigherSFormation.higherSInput hO hD F0
  have hK : IsCompact K := F0.property.2.1
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hu : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hz : ∀ x ∉ K, U x=0 := ActualHigherSZeroScalarNativeForm.highInput_eq_zero_off hO hD F0
  have hmem (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom δ := by
    have ht := guardFacts.2.2 q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom x
      (ball_subset_closedBall (hsupp hx)) (hsupp hx) (hb x hx) (hs x hx)
    exact (higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x ht).self_of_nhds
  have hOrd (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom ordinary.δ :=
    ⟨commonRoom_mono y0 ρ (min_le_left _ _) (hmem x hx).1,(hmem x hx).2⟩
  have hDataRoom (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom data.δ :=
    ⟨commonRoom_mono y0 ρ (min_le_right _ _) (hmem x hx).1,(hmem x hx).2⟩
  have hWRoom (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom δ0 :=
    ⟨commonRoom_mono y0 ρ data.δ_le0 (hDataRoom x hx).1,(hDataRoom x hx).2⟩
  have hSeg (x : R3) (hx : x ∈ K) :=
    segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      ordinary.room_sub ((Tq dr Ar p q) x).1 (hOrd x hx).1
  have hPC (x : R3) (hx : x ∈ K) := principal_physical_coordinate_regular
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg ordinary g2 hg2 dr Ar p q hdr hAr x (hOrd x hx) l k
  have hGC (x : R3) (hx : x ∈ K) := gained_physical_coordinate_regular
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 hg2
    dr Ar p q hq hdr hdr1 hAr hp eta heta hetaData x (ball_subset_closedBall (hsupp hx)) (hsupp hx)
    (hb x hx) (hs x hx) l k
  have hAdj (x : R3) (hx : x ∈ K) (u1 u2 : Hi) :
      highDualPairingL u1 (PCt g2 dr Ar p q l k x u2)=highDualPairingL u2 (PC g2 dr Ar p q l k x u1) :=
    (principalCoordinate_paired hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W
      g2 dr Ar p q l k x (hWRoom x hx) (hSeg x hx) u1 u2).symm
  have hCadj (x : R3) (hx : x ∈ K) (u1 u2 : Hi) :
      highDualPairingL u1 (GCt hreg δ0 W data g2 dr Ar p q l k x u2)=
        highDualPairingL u2 (GC hreg δ0 W data g2 dr Ar p q l k x u1) :=
    (gainedCoordinate_paired hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data
      g2 dr Ar p q l k x (hDataRoom x hx) (hSeg x hx) u1 u2).symm
  have hSym (x : R3) (hx : x ∈ K) := principalCoordinate_symmetric_sum
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x (hDataRoom x hx)
  have hc1 := hGain q hq dr hdr hdr1 Ar hAr p hp eta heta hetaC F0 hsupp hb hs l k l k
  have hc2 := hGain q hq dr hdr hdr1 Ar hAr p hp eta heta hetaC F0 hsupp hb hs l k k l
  have hk1 := hLower q hq dr hdr hdr1 Ar hAr p hp eta heta hetaK F0 hsupp hb hs l k k l
  have hk2 := hLower q hq dr hdr hdr1 Ar hAr p hp eta heta hetaK F0 hsupp hb hs l k l k
  exact principal_reference_fixed_spaces (fun x => referenceDensityFamily g L (q,x))
    (ActualHigherSFormation.higherSInput hO hD F0)
    (PC g2 dr Ar p q l k) (PCt g2 dr Ar p q l k)
    (GC hreg δ0 W data g2 dr Ar p q l k) (GCt hreg δ0 W data g2 dr Ar p q l k)
    K hK hm hu hz (fun x hx => (hPC x hx).1) (fun x hx => (hPC x hx).2)
    (fun x hx => (hGC x hx).1) (fun x hx => (hGC x hx).2) hAdj hCadj hSym
    (coordinateDirection l) (coordinateDirection k) Bc Bk eta
    (∫ x, referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F0 x)
    hc1 hc2 hk1 hk2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFirstReference
