import Calderon.ActualTSPrincipalGreen
import Calderon.ActualTSPrincipalOrdinaryRoom
import Calderon.ActualTSPrincipalWeightedCoefficients
import Calderon.ActualMixedAngularFullOutputForm
import Calderon.ActualHigherSScalarCommutatorNativeForm
import Calderon.ActualHigherSIntegratedPairing

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalPhysicalGreen
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

section GenericSmooth
variable {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
private lemma weighted_contDiffAt (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G : Fin 3 → Fin 3 → R3 → V →L[ℝ] Z) (x : R3)
    (hR : ContDiffAt ℝ ∞ R x) (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x)
    (hb : ∀ i, ContDiffAt ℝ ∞ (b i) x) (hG : ∀ i j, ContDiffAt ℝ ∞ (G i j) x) :
    ContDiffAt ℝ ∞ (weightedMixedSecondCoefficient R a b G) x := by
  unfold weightedMixedSecondCoefficient
  apply (hR.pow 2).smul
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((ha i).mul (hb j)).smul (hG i j)
end GenericSmooth

/-- Native ordinary smoothness survives the exact physical profile and the two angular compositions. -/
lemma principal_physical_angular_regular
    (ordinary : PrincipalOrdinaryRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (hdr : 0 < dr) (hAr : 0 < Ar) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom ordinary.δ) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => angularPrincipalHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      i j ((Tq dr Ar p q) y)) x ∧
    ContDiffAt ℝ ∞ (fun y => angularPrincipalTransposeHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      i j ((Tq dr Ar p q) y)) x := by
  have ht : ContDiffAt ℝ ∞ (Tq dr Ar p q) x :=
    (contDiff_radiusProfileMap q (referenceRadius dr Ar p L)
      (contDiff_referenceRadius_actual dr Ar p L hdr hAr)).contDiffAt
  have hs := ordinary.regular j ((Tq dr Ar p q) x) hx
  have hEH := hs.1.comp x ht
  have hEL := hs.2.1.comp x ht
  have heH := hs.2.2.1.comp x ht
  have heL := hs.2.2.2.comp x ht
  unfold angularPrincipalHigh angularPrincipalTransposeHigh
  constructor
  · exact (contDiffAt_const.clm_comp hEH).sub (contDiffAt_const.clm_comp heH)
  · exact (heL.clm_comp contDiffAt_const).sub (hEL.clm_comp contDiffAt_const)


private lemma physical_coordinate_weight_smooth
    (g0 : MatrixField) (hg0 : IsAdmissibleMetric g0) (L0 : ℝ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (k j : Fin 3) :
    ContDiff ℝ ∞ (fun y => firstCoordinateWeight g0 g2 L0 k j
      (ActualHigherSFormation.higherSParam L0 dr Ar p q y)) := by
  rw [physical_firstCoordinateWeight_eq_base]
  exact (contDiff_coordinateWeightBase g0 g2 hg0 hg2 L0 k j).comp (contDiff_const.prodMk contDiff_id)

local notation "PC" => principalCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "PCt" => principalTransposeCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "GC" => gainedCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "GCt" => gainedTransposeCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

/-- Both literal high principal coefficient fields are smooth on the actual ordinary room. -/
lemma principal_physical_coordinate_regular
    (ordinary : PrincipalOrdinaryRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (hdr : 0 < dr) (hAr : 0 < Ar) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom ordinary.δ) (l k : Fin 3) :
    ContDiffAt ℝ ∞ (PC g2 dr Ar p q l k) x ∧ ContDiffAt ℝ ∞ (PCt g2 dr Ar p q l k) x := by
  have hR : ContDiffAt ℝ ∞ (referenceRadius dr Ar p L) x :=
    (contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
  have ha (i : Fin 3) : ContDiffAt ℝ ∞ (fun y => referenceMetricGramFrame g L (q,y) i l) x :=
    ((ActualBalancedFirstPrincipalError.contDiff_frameEntry g hg L i l).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt
  have hb (j : Fin 3) := (physical_coordinate_weight_smooth g hg L g2 hg2 dr Ar p q k j).contDiffAt (x := x)
  have hG (i j : Fin 3) := principal_physical_angular_regular hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    ordinary dr Ar p q hdr hAr x hx i j
  constructor
  · exact weighted_contDiffAt _ _ _ _ x hR ha hb (fun i j => (hG i j).1)
  · exact weighted_contDiffAt _ _ _ _ x hR ha hb (fun i j => (hG i j).2)

/-- The original checked C/H physical record supplies both gained coefficient fields' regularity. -/
lemma gained_physical_coordinate_regular (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (hdr : 0 < dr) (hdr1 : dr ≤ 1) (hAr : 0 < Ar) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0)
    (x : R3) (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (l k : Fin 3) :
    ContDiffAt ℝ ∞ (GC hreg δ0 W data g2 dr Ar p q l k) x ∧
      ContDiffAt ℝ ∞ (GCt hreg δ0 W data g2 dr Ar p q l k) x := by
  have hR : ContDiffAt ℝ ∞ (referenceRadius dr Ar p L) x :=
    (contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt
  have ha (i : Fin 3) : ContDiffAt ℝ ∞ (fun y => referenceMetricGramFrame g L (q,y) i l) x :=
    ((ActualBalancedFirstPrincipalError.contDiff_frameEntry g hg L i l).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt
  have hw (j : Fin 3) := (physical_coordinate_weight_smooth g hg L g2 hg2 dr Ar p q k j).contDiffAt (x := x)
  have hCH (i j : Fin 3) :=
    (data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i j).1.1
  have hHH (i j : Fin 3) :=
    (data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i j).2.1.1
  constructor
  · exact weighted_contDiffAt _ _ _ _ x hR ha hw
      (fun i j => contDiffAt_const.clm_comp (hCH i j))
  · exact weighted_contDiffAt _ _ _ _ x hR ha hw
      (fun i j => contDiffAt_const.clm_comp (hHH i j).neg)



end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalPhysicalGreen
