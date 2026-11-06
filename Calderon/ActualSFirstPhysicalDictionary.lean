import Calderon.ActualHigherSZeroPhysicalGraph
import Calderon.ActualHigherSAdjointLeadingCoordinate
import Calderon.ActualReverseELowInputDerivative

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSFirstPhysicalDictionary
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore
  ActualHigherSFormation ActualHigherSAdjointFormation ActualHigherSLeadingBracketGain
  ActualHigherSFirstPhysicalCommutatorGraph ActualHigherSZeroPhysicalGraph
  ActualHigherSAdjointCoefficientExtraction ActualHigherSAdjointLeadingCoordinate
  ActualCommonFirstWordQuadraticAdjoint ReferenceDensityBounds ConformalDepth

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete


private lemma split_original_remainder {E : Type*} [AddCommGroup E] (s a : E) :
    s = a+(s-a) := by abel

private lemma zero_graph_of_first_graph {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : E →L[ℝ] F) (s a : E) (b c : F)
    (hS : J s=b+c) (hA : J a=b) : J (s-a)=c := by
  rw [map_sub,hS,hA]
  abel

private lemma weighted_first_action_contract {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℝ) (a : Fin 3 → Fin 3 → ℝ) (A : Fin 3 → E →L[ℝ] F) (v : Fin 3 → E) :
    r • (∑ k : Fin 3, ∑ j : Fin 3, a k j • A j (v k)) =
      ∑ k : Fin 3, (r • (∑ j : Fin 3, a k j • A j)) (v k) := by
  simp only [_root_.smul_apply,_root_.sum_apply,Finset.smul_sum]

private lemma weighted_negative_graph {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (I : E →L[ℝ] F) (J : F →L[ℝ] G) (A : Fin 3 → E →L[ℝ] F)
    (B : Fin 3 → F →L[ℝ] G) (a : Fin 3 → Fin 3 → ℝ) (r : ℝ) (v : Fin 3 → E)
    (h : ∀ j u, J (A j u)=B j (I u)) :
    J (-(r • ∑ k : Fin 3, ∑ j : Fin 3, a k j • A j (v k))) =
      ∑ k : Fin 3, ((-r) • (∑ j : Fin 3, a k j • B j)) (I (v k)) := by
  simp only [map_neg,map_smul,map_sum,_root_.smul_apply,_root_.sum_apply,
    neg_smul,Finset.smul_sum,Finset.sum_neg_distrib]
  simp_rw [h]
  simp only [ContinuousLinearMap.neg_apply,_root_.sum_apply,_root_.smul_apply,
    Finset.sum_neg_distrib]

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" dr:max Ar:max p:max q:max => higherSParam L dr Ar p q
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HCC" => highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BR" => orderedReverseFirstCoordinateFactorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "SH" => nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "ADJ" => higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => higherSAdjointZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UF" => higherSInput hO hD

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  nativeHigherSHalf higherSAdjointHalf nativeZeroHalf higherSAdjointZeroCoefficient
  sphereSobolevInclusionL

/-- Original first S part, with both Q orders and all angular outputs. -/
def referenceSFirstHalf (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (U : R3 → Hi) (x : R3) : Half :=
  (referenceRadius dr Ar p L x)^2 •
    ∑ k : Fin 3, ∑ j : Fin 3, firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x) •
      EH j ((Tq dr Ar p q) x) (fderiv ℝ U x (coordinateDirection k))

/-- Original negative ordered first S-adjoint part. -/
def referenceSAdjointFirstHalf (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (U : R3 → Hi) (x : R3) : Half :=
  -((referenceRadius dr Ar p L x)^2 •
    ∑ k : Fin 3, ∑ j : Fin 3, firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x) •
      eH j ((Tq dr Ar p q) x) (fderiv ℝ U x (coordinateDirection k)))

local notation "S1" => referenceSFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Sd1" => referenceSAdjointFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The named first part is exactly the already extracted original coordinate action. -/
theorem referenceSFirstHalf_eq_coordinate_action (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (U : R3 → Hi) (x : R3) :
    S1 g2 dr Ar p q U x =
      coordinateFirstAction (fun k y => HCC g2 dr Ar p q y k) U x := by
  unfold referenceSFirstHalf coordinateFirstAction highFirstCoordinateCoefficient
  simp_rw [highFirstCoordinateFactor_eq_contracted]
  exact weighted_first_action_contract _ _ _ _

/-- Complete original S with its unchanged original zero Half realization. -/
theorem nativeS_eq_first_and_original_zero (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    SH dr Ar p hdr hAr q hreg d0 germs g2 F x =
      S1 g2 dr Ar p q (UF F) x+ZH hreg d0 germs g2 dr Ar p hdr hAr q F x := by
  rw [referenceSFirstHalf_eq_coordinate_action g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0]
  unfold nativeZeroHalf
  exact split_original_remainder _ _

/-- The full adjoint zero remainder, retaining every original correction. -/
def nativeAdjointZeroHalf (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  ADJ hreg d0 germs g2 dr Ar p hdr hAr q F x-Sd1 g2 dr Ar p q (UF F) x

local notation "Sd0" => nativeAdjointZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

theorem nativeSdag_eq_first_and_original_zero (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ADJ hreg d0 germs g2 dr Ar p hdr hAr q F x =
      Sd1 g2 dr Ar p q (UF F) x+Sd0 hreg d0 germs g2 dr Ar p hdr hAr q F x := by
  unfold nativeAdjointZeroHalf
  exact split_original_remainder _ _

/-- The first adjoint has exactly the extracted negative-space coordinate coefficient. -/
theorem adjointFirstHalf_negative_graph (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (d : ℝ) (room : CRoom hreg d0 germs d)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (U : R3 → Hi) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom d) :
    JL (Sd1 g2 dr Ar p q U x) =
      ∑ k : Fin 3, ((-(referenceRadius dr Ar p L x)^2) • BR g2 k ((Tq dr Ar p q) x))
        (IH (fderiv ℝ U x (coordinateDirection k))) := by
  have hCompat (j : Fin 3) (v : Hi) :
      JL (eH j ((Tq dr Ar p q) x) v) = eL j ((Tq dr Ar p q) x) (IH v) := by
    have h := room.rev.compat j _ hx v
    simpa only [ActualHigherSAdjointLeadingCoordinate.reverseEHigh_eq_ordered,
      ActualHigherSAdjointLeadingCoordinate.reverseELow_eq_ordered] using h
  unfold referenceSAdjointFirstHalf orderedReverseFirstCoordinateFactorLow
  exact weighted_negative_graph IH JL _ _ _ _ _ hCompat

/-- This is the original full adjoint zero coefficient, on the same retained room. -/
theorem nativeAdjointZeroHalf_negative_graph (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (d : ℝ) (room : CRoom hreg d0 germs d)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ z ∈ tsupport F.val, (Tq dr Ar p q) z ∈ ParamRoom d)
    (x : R3) (hx : x ∈ tsupport F.val) :
    JL (Sd0 hreg d0 germs g2 dr Ar p hdr hAr q F x) =
      CZ g2 dr Ar p q x (UF F x) := by
  have hFull := actual_higherS_adjoint_coordinate_coefficient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg d0 germs d room g2 dr Ar p hdr hAr q F hT x
  have hFirst := adjointFirstHalf_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg d0 germs d room g2 dr Ar p q (UF F) x (hT x hx)
  exact zero_graph_of_first_graph JL _ _ _ _ hFull hFirst

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSFirstPhysicalDictionary

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSFirstPhysicalDictionary.nativeS_eq_first_and_original_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSFirstPhysicalDictionary.nativeSdag_eq_first_and_original_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSFirstPhysicalDictionary.nativeAdjointZeroHalf_negative_graph
