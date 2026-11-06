import Calderon.ActualMixedAngularSecondReferenceForm
import Calderon.ActualLeadingFullOutputReferenceForm
import Calderon.ActualHigherSScalarCommutatorNativeForm
import Calderon.ActualHigherSIntegratedPairing

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
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

open ActualHigherSFormation ActualHigherSFirstPhysicalCommutatorGraph ActualFullEGainedAssembly
  ActualHigherSCoordinateWeightBounds ActualHigherSLeadingBracketGain SmoothMetricFrame MovingFrameConnection
  FixedParameterProfilePullback FixedParameterProfileBudgets
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- Original upper inclusion for the genuine mixed high coefficient. -/
theorem mixedAngularSecondHighCoefficient_negative_graph (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom data.δ) (v : Hi) :
    JL (mixedAngularSecondHighCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x v) =
      mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x (IH v) := by
  have h := congrArg (fun T : Hi →L[ℝ] Neg => T v)
    (mixedAngularSecondCoefficient_upper_graph hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x hx)
  simpa only [ContinuousLinearMap.comp_apply] using h.symm

section GenericSmooth
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
private theorem contDiffAt_mixedWeightedCoefficient (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G : Fin 3 → Fin 3 → R3 → E →L[ℝ] F) (x : R3)
    (hR : ContDiffAt ℝ ∞ R x) (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x)
    (hb : ∀ j, ContDiffAt ℝ ∞ (b j) x) (hG : ∀ i j, ContDiffAt ℝ ∞ (G i j) x) :
    ContDiffAt ℝ ∞ (weightedMixedSecondCoefficient R a b G) x := by
  have hW : ContDiffAt ℝ ∞ (fun y => ∑ i : Fin 3, ∑ j : Fin 3, (a i y*b j y) • G i j y) x := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact ((ha i).mul (hb j)).smul (hG i j)
  unfold weightedMixedSecondCoefficient
  exact (hR.pow 2).smul hW
end GenericSmooth

/-- All nine high mixed second-band rows applied to the original finite input. -/
def mixedAngularSecondHalfField (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  ∑ l : Fin 3, ∑ k : Fin 3,
    mixedAngularSecondHighCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x
      (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k)
        (ActualHigherSFormation.higherSInput hO hD F)) x)

/-- Full SphereL2 output, with no finite angular-output restriction. -/
def mixedAngularSecondFullOutput (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  sphereSobolevHalfToSphereL2L hO hD (mixedAngularSecondHalfField
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q F x)

local notation "CH" => mixedAngularSecondHighCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "NH" => mixedAngularSecondHalfField hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "NN" => mixedAngularSecondNegativeField hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "NO" => mixedAngularSecondFullOutput hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

/-- The exact global negative graph; support locality closes points outside the room. -/
theorem mixedAngularSecondHalfField_negative_graph (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom data.δ) (x : R3) :
    JL (NH hreg δ0 W data g2 dr Ar p q F x) = NN hreg δ0 W data g2 dr Ar p q F x := by
  let U : R3 → Hi := ActualHigherSFormation.higherSInput hO hD F
  have hu : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hz : ∀ y ∉ tsupport F.val, U y = 0 := higherSInput_eq_zero_off hO hD F
  have hSecondInput (l k : Fin 3) : directionalFDeriv (coordinateDirection l)
      (directionalFDeriv (coordinateDirection k) (halfInput hO hD F)) x =
      IH (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) U) x) :=
    leading_second_halfInput hO hD F l k x
  unfold mixedAngularSecondHalfField mixedAngularSecondNegativeField
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _

  let v : Hi := directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) U) x
  let dv : Half := directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) (halfInput hO hD F)) x
  let CL : Half →L[ℝ] Neg := mixedAngularSecondCoefficient
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x
  have hRight : CL dv = CL (IH v) := congrArg (fun z : Half => CL z) (hSecondInput l k)

  by_cases hx : x ∈ tsupport F.val
  · have hLeft : JL (CH hreg δ0 W data g2 dr Ar p q l k x v) = CL (IH v) :=
      mixedAngularSecondHighCoefficient_negative_graph hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x (hTF x hx) v
    have rowResult : JL (CH hreg δ0 W data g2 dr Ar p q l k x v) = CL dv := hLeft.trans hRight.symm

    endpoint_literal_transport rowResult
  · have hd0 : ∀ y ∉ tsupport F.val, directionalFDeriv (coordinateDirection k) U y = 0 :=
      fun y hy => directional_eq_zero_off U _ (isClosed_tsupport F.val) hz _ y hy
    have hdd : v = 0 := directional_eq_zero_off _ _ (isClosed_tsupport F.val) hd0 (coordinateDirection l) x hx
    have hLeft : JL (CH hreg δ0 W data g2 dr Ar p q l k x v) = CL (IH v) := by
      simp only [hdd,map_zero]
    have rowResult : JL (CH hreg δ0 W data g2 dr Ar p q l k x v) = CL dv := hLeft.trans hRight.symm

    endpoint_literal_transport rowResult

/-- Smoothness of the genuine high coefficient from the actual endpoint cap record. -/
theorem mixedAngularSecondHighCoefficient_contDiffAt (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (hdr : 0 < dr) (hdr1 : dr ≤ 1) (hAr : 0 < Ar) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0)
    (x : R3) (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (l k : Fin 3) : ContDiffAt ℝ ∞ (CH hreg δ0 W data g2 dr Ar p q l k) x := by
  have ha := exists_physical_firstCoordinateWeight_uniform_first_caps g g2 hg hg2 L y0 ρ
  have hweights := (Classical.choose_spec ha).2
  have hG (i j : Fin 3) := (data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0
    x hx hxBall hb hs i j).1.1
  unfold mixedAngularSecondHighCoefficient
  exact contDiffAt_mixedWeightedCoefficient (referenceRadius dr Ar p L)
    (fun i y => referenceMetricGramFrame g L (q,y) i l)
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => loweringEHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg data.G δ0 W i j ((Tq dr Ar p q) y)) x
    (contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
    (fun i => ((ActualBalancedFirstPrincipalError.contDiff_frameEntry g hg L i l).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt)
    (fun j => (hweights q hq x hx dr Ar p k j).1.contDiffAt) hG

/-- Global smoothness of the actual nine-row Half output, with the original hypotheses. -/
theorem mixedAngularSecondHalfField_contDiff (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (hdr : 0 < dr) (hdr1 : dr ≤ 1) (hAr : 0 < Ar) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hball : tsupport F.val ⊆ ball y0 ρ)
    (hb : ∀ x ∈ tsupport F.val, 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ tsupport F.val,
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    ContDiff ℝ ∞ (NH hreg δ0 W data g2 dr Ar p q F) := by
  have hCH (l k : Fin 3) (x : R3) (hx : x ∈ tsupport F.val) :
      ContDiffAt ℝ ∞ (CH hreg δ0 W data g2 dr Ar p q l k) x :=
    mixedAngularSecondHighCoefficient_contDiffAt hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W data g2 hg2 dr Ar p q hq hdr hdr1 hAr hp eta heta heta0 x
      (ball_subset_closedBall (hball hx)) (hball hx) (hb x hx) (hs x hx) l k
  have built := contDiff_supported_leading_second_sum
    (fun l k => CH hreg δ0 W data g2 dr Ar p q l k)
    (ActualHigherSFormation.higherSInput hO hD F) (tsupport F.val) (isClosed_tsupport F.val)
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F) (higherSInput_eq_zero_off hO hD F) hCH
  unfold mixedAngularSecondHalfField
  endpoint_literal_transport built

/-- All actual mixed second-band rows vanish off the original support by derivative locality. -/
theorem mixedAngularSecondHalfField_eq_zero_off (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (hx : x ∉ tsupport F.val) :
    NH hreg δ0 W data g2 dr Ar p q F x = 0 := by
  have built := leading_second_sum_eq_zero_off
    (fun l k => CH hreg δ0 W data g2 dr Ar p q l k)
    (ActualHigherSFormation.higherSInput hO hD F) (tsupport F.val) (isClosed_tsupport F.val)
    (higherSInput_eq_zero_off hO hD F) x hx
  unfold mixedAngularSecondHalfField
  endpoint_literal_transport built

/-- The genuine Half and full physical outputs are smooth compact and preserve input support. -/
theorem mixedAngularSecondFullOutput_regular (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (hdr : 0 < dr) (hdr1 : dr ≤ 1) (hAr : 0 < Ar) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hball : tsupport F.val ⊆ ball y0 ρ)
    (hb : ∀ x ∈ tsupport F.val, 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ tsupport F.val,
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    ContDiff ℝ ∞ (NH hreg δ0 W data g2 dr Ar p q F) ∧
    tsupport (NH hreg δ0 W data g2 dr Ar p q F) ⊆ tsupport F.val ∧
    HasCompactSupport (NH hreg δ0 W data g2 dr Ar p q F) ∧
    ContDiff ℝ ∞ (NO hreg δ0 W data g2 dr Ar p q F) ∧
    tsupport (NO hreg δ0 W data g2 dr Ar p q F) ⊆ tsupport F.val ∧
    HasCompactSupport (NO hreg δ0 W data g2 dr Ar p q F) := by
  have hNH : ContDiff ℝ ∞ (NH hreg δ0 W data g2 dr Ar p q F) :=
    mixedAngularSecondHalfField_contDiff
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 hg2
      dr Ar p q hq hdr hdr1 hAr hp eta heta heta0 F hball hb hs
  have hzNH : ∀ x ∉ tsupport F.val, NH hreg δ0 W data g2 dr Ar p q F x = 0 :=
    mixedAngularSecondHalfField_eq_zero_off
      hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q F
  have hSupportNH : Function.support (NH hreg δ0 W data g2 dr Ar p q F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hnot
    exact hx (hzNH x hnot)
  have hNHsupp : tsupport (NH hreg δ0 W data g2 dr Ar p q F) ⊆ tsupport F.val :=
    closure_minimal hSupportNH (isClosed_tsupport F.val)

  have hNHc : HasCompactSupport (NH hreg δ0 W data g2 dr Ar p q F) := HasCompactSupport.intro F.property.2.1 hzNH

  have hNO : ContDiff ℝ ∞ (NO hreg δ0 W data g2 dr Ar p q F) :=
    contDiff_leading_physical_embedding hO hD (NH hreg δ0 W data g2 dr Ar p q F) hNH
  have hzNO : ∀ x ∉ tsupport F.val, NO hreg δ0 W data g2 dr Ar p q F x = 0 := by
    intro x hx
    simp only [mixedAngularSecondFullOutput,hzNH x hx,map_zero]
  have hSupportNO : Function.support (NO hreg δ0 W data g2 dr Ar p q F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hnot
    exact hx (hzNO x hnot)
  have hNOsupp : tsupport (NO hreg δ0 W data g2 dr Ar p q F) ⊆ tsupport F.val :=
    closure_minimal hSupportNO (isClosed_tsupport F.val)
  have hNOc : HasCompactSupport (NO hreg δ0 W data g2 dr Ar p q F) := HasCompactSupport.intro F.property.2.1 hzNO

  exact ⟨hNH,hNHsupp,hNHc,hNO,hNOsupp,hNOc⟩


/-- The explicit mixed second-band reference bound now has a full smooth physical output and literal signed graph. -/
theorem exists_mixedAngularSecond_full_output_reference_form (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ CRef : ℝ, 0 < CRef ∧ ∃ etaG : ℝ, 0 < etaG ∧ etaG ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaG →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ContDiff ℝ ∞ (NO hreg δ0 W data g2 dr Ar p q F) ∧
      tsupport (NO hreg δ0 W data g2 dr Ar p q F) ⊆ tsupport F.val ∧
      HasCompactSupport (NO hreg δ0 W data g2 dr Ar p q F) ∧
      (∀ x, JL (NH hreg δ0 W data g2 dr Ar p q F x) = NN hreg δ0 W data g2 dr Ar p q F x) ∧
      (∀ x ∈ K, ∀ l k : Fin 3,
        (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x).comp IH =
          (JL).comp (CH hreg δ0 W data g2 dr Ar p q l k x)) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*⟪F.val x,NO hreg δ0 W data g2 dr Ar p q F x⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,NO hreg δ0 W data g2 dr Ar p q F x⟫_ℝ| ≤
        CRef*eta*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by

  obtain ⟨CRef,hC,hform⟩ := exists_mixedAngularSecond_reference_form
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hL hreg δ0 W data g2 hg2
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
  have hgraph := mixedAngularSecondHalfField_negative_graph
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q F
    (fun x hx => hmem x (hsupp hx))
  have hregO := mixedAngularSecondFullOutput_regular
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 hg2
    dr Ar p q hq hdr hdr1 hAr hp eta heta heta0 F (fun x hx => hKball (hsupp hx))
    (fun x hx => hb x (hsupp hx)) (fun x hx => hs x (hsupp hx))
  have hn := hform q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs
  have he : (fun x => referenceDensityFamily g L (q,x)*PP (halfInput hO hD F x)
      (NN hreg δ0 W data g2 dr Ar p q F x)) =
      (fun x => referenceDensityFamily g L (q,x)*⟪F.val x,NO hreg δ0 W data g2 dr Ar p q F x⟫_ℝ) := by
    funext x
    have hp := ActualHigherSPhysicalPairing.physical_pairing_of_graph hO hD F
      (NH hreg δ0 W data g2 dr Ar p q F) (NN hreg δ0 W data g2 dr Ar p q F) hgraph x
    have hp' : PP (halfInput hO hD F x) (NN hreg δ0 W data g2 dr Ar p q F x) =
        ⟪F.val x,NO hreg δ0 W data g2 dr Ar p q F x⟫_ℝ := by
      simpa only [halfInput,ActualHigherSFormation.higherSInput,mixedAngularSecondFullOutput] using hp
    exact congrArg (fun z : ℝ => referenceDensityFamily g L (q,x)*z) hp' 
  have hi := congrArg (fun f : R3 → ℝ => ∫ x, f x) he
  have hInt : Integrable (fun x => referenceDensityFamily g L (q,x)*
      ⟪F.val x,NO hreg δ0 W data g2 dr Ar p q F x⟫_ℝ) :=
    Eq.mp (congrArg (fun f : R3 → ℝ => Integrable f) he) hn.1
  refine ⟨hregO.2.2.2.1,hregO.2.2.2.2.1,hregO.2.2.2.2.2,hgraph,?_,hInt,hn.2.1,?_⟩
  · intro x hx l k
    exact mixedAngularSecondCoefficient_upper_graph hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W data g2 dr Ar p q l k x (hmem x hx)
  · calc
      |∫ x, referenceDensityFamily g L (q,x)*⟪F.val x,NO hreg δ0 W data g2 dr Ar p q F x⟫_ℝ| =
          |∫ x, referenceDensityFamily g L (q,x)*PP (halfInput hO hD F x)
            (NN hreg δ0 W data g2 dr Ar p q F x)| := congrArg abs hi.symm
      _ ≤ CRef*eta*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := hn.2.2


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualMixedAngularPairedGains
