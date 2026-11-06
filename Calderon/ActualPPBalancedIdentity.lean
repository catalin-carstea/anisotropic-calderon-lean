import Calderon.ActualPPWeakLower
import Calderon.ClmInheritedStructureData
import Mathlib.Tactic.LinearCombination
import Calderon.ActualPPCoefficientCaps
import Calderon.ActualHigherSAdjointFormation
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPBalancedIdentity
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualHigherSLeadingBracketGain ConformalDepth PrincipalCommutator
  ActualPPCoefficientCaps FixedParameterProfilePullback ActualPPLowerRemainder
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
attribute [local irreducible] sphereSobolevInclusionL
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh

/-- Exact six-term transpose on opaque coefficient maps. Actual smooth pivots
and their derivatives are discharged in the unchanged public theorem below. -/
private lemma transpose_six_term_row
    (Q : Half →L[ℝ] Neg →L[ℝ] ℝ)
    (Pc Dc : Fin 3 → Hi →L[ℝ] Half) (Pl Dl : Fin 3 → Half →L[ℝ] Neg)
    (dPc dDc : Fin 3 → Fin 3 → Hi →L[ℝ] Half)
    (dPl dDl : Fin 3 → Fin 3 → Half →L[ℝ] Neg)
    (hSym : ∀ a b : Half, Q a (JL b) = Q b (JL a))
    (hP : ∀ i : Fin 3, ∀ v : Hi, ∀ z : Half, Q (IH v) (Dl i z) = -Q (Pc i v) (JL z))
    (hReversePivot : ∀ i : Fin 3, ∀ v : Hi, ∀ z : Half, Q (IH v) (Pl i z) = -Q (Dc i v) (JL z))
    (hDP : ∀ dir i : Fin 3, ∀ v : Hi, ∀ z : Half,
      Q (IH v) (dDl dir i z) = -Q (dPc dir i v) (JL z))
    (hDD : ∀ dir i : Fin 3, ∀ v : Hi, ∀ z : Half,
      Q (IH v) (dPl dir i z) = -Q (dDc dir i v) (JL z))
    (UU : Hi) (DU : Fin 3 → Hi) (mu0 dmul dmuk : ℝ) (l k : Fin 3) :
    mu0*(Q (IH UU) (dDl l l (Pc k (DU k)))+
        Q (IH UU) (Dl l (dPc l k (DU k)))-
        Q (IH UU) (dPl k k (Dc l (DU l)))-
        Q (IH UU) (Pl k (dDc k l (DU l))))+
      dmul*Q (IH UU) (Dl l (Pc k (DU k)))-
      dmuk*Q (IH UU) (Pl k (Dc l (DU l))) =
      mu0*(Q (IH (DU k)) (Dl k (dPc l l UU))+
        Q (IH (DU k)) (dDl l k (Pc l UU))-
        Q (IH (DU l)) (Pl l (dDc k k UU))-
        Q (IH (DU l)) (dPl k l (Dc k UU)))+
      dmul*Q (IH (DU k)) (Dl k (Pc l UU))-
      dmuk*Q (IH (DU l)) (Pl l (Dc k UU)) := by
  have hNative1 := ActualPPWeakLower.transpose_two_factors Q IH JL
    (dPc l l) (Pc k) (dDl l l) (Dl k) hSym (hDP l l) (hP k) UU (DU k)
  have hNative2 := ActualPPWeakLower.transpose_two_factors Q IH JL
    (Pc l) (dPc l k) (Dl l) (dDl l k) hSym (hP l) (hDP l k) UU (DU k)
  have hNative3 := ActualPPWeakLower.transpose_two_factors Q IH JL
    (dDc k k) (Dc l) (dPl k k) (Pl l) hSym (hDD k k) (hReversePivot l) UU (DU l)
  have hNative4 := ActualPPWeakLower.transpose_two_factors Q IH JL
    (Dc k) (dDc k l) (Pl k) (dPl k l) hSym (hReversePivot k) (hDD k l) UU (DU l)
  have hNative5 := ActualPPWeakLower.transpose_two_factors Q IH JL
    (Pc l) (Pc k) (Dl l) (Dl k) hSym (hP l) (hP k) UU (DU k)
  have hNative6 := ActualPPWeakLower.transpose_two_factors Q IH JL
    (Dc k) (Dc l) (Pl k) (Pl l) hSym (hReversePivot k) (hReversePivot l) UU (DU l)
  try simp only [clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq]
      at hNative1 hNative2 hNative3 hNative4 hNative5 hNative6
  have h1 : Q (IH UU) (dDl l l (Pc k (DU k))) =
      Q (IH (DU k)) (Dl k (dPc l l UU)) := hNative1
  have h2 : Q (IH UU) (Dl l (dPc l k (DU k))) =
      Q (IH (DU k)) (dDl l k (Pc l UU)) := hNative2
  have h3 : Q (IH UU) (dPl k k (Dc l (DU l))) =
      Q (IH (DU l)) (Pl l (dDc k k UU)) := hNative3
  have h4 : Q (IH UU) (Pl k (dDc k l (DU l))) =
      Q (IH (DU l)) (dPl k l (Dc k UU)) := hNative4
  have h5 : Q (IH UU) (Dl l (Pc k (DU k))) =
      Q (IH (DU k)) (Dl k (Pc l UU)) := hNative5
  have h6 : Q (IH UU) (Pl k (Dc l (DU l))) =
      Q (IH (DU l)) (Pl l (Dc k UU)) := hNative6
  linear_combination mu0*h1+mu0*h2-mu0*h3-mu0*h4+dmul*h5-dmuk*h6

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
  (g2 : MatrixField)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "PH" => ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "PL" => ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DL" => ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "HU" => ActualHigherSScalarCommutatorNativeForm.halfInput hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Lead" => actualLeadingSignedSecondNeg
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2


local notation "DH" => ActualPPLowerRemainder.actualPPReverseFirstHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "BR" => ActualPPLowerRemainder.actualPPBalancedRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "QPP" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

def actualPPRawRow (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (l k : Fin 3) : ℝ :=
  let U := UF F x
  let dU := fun i => directionalFDeriv (coordinateDirection i) (UF F) x
  let mu := fun y : R3 => referenceDensityFamily g L (q,y)
  mu x*(PP (IH U) ((directionalFDeriv (coordinateDirection l) (fun y => DL dr Ar p q y l) x)
      (PH dr Ar p q x k (dU k)))+
    PP (IH U) (DL dr Ar p q x l
      ((directionalFDeriv (coordinateDirection l) (fun y => PH dr Ar p q y k) x) (dU k)))-
    PP (IH U) ((directionalFDeriv (coordinateDirection k) (fun y => PL dr Ar p q y k) x)
      (DH dr Ar p q x l (dU l)))-
    PP (IH U) (PL dr Ar p q x k
      ((directionalFDeriv (coordinateDirection k) (fun y => DH dr Ar p q y l) x) (dU l))))+
  directionalFDeriv (coordinateDirection l) mu x*
    PP (IH U) (DL dr Ar p q x l (PH dr Ar p q x k (dU k)))-
  directionalFDeriv (coordinateDirection k) mu x*
    PP (IH U) (PL dr Ar p q x k (DH dr Ar p q x l (dU l)))
local notation "RR" => actualPPRawRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
attribute [local irreducible] actualPPRawRow ActualPPLowerRemainder.actualPPBalancedRow

/-- Exact actual six-term balancing, from original data caps and genuine pivots
on a proved physical neighborhood. The only local geometric premise is explicit
neighborhood room membership, to be derived by the final original threshold. -/
theorem actual_raw_row_eq_balanced (hL : 0 < L) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0) (x : R3)
    (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (hT : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom data.δ)
    (F : smoothCompactFiniteSphereCore hO hD) (l k : Fin 3) :
    RR dr Ar p q F x l k=BR dr Ar p q F x l k := by
  obtain ⟨M,hM,hcaps⟩ := exists_actual_first_coefficient_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  have hc (i : Fin 3) := hcaps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs i
  let Pc : Fin 3 → Hi →L[ℝ] Half := fun i => PH dr Ar p q x i
  let Dc : Fin 3 → Hi →L[ℝ] Half := fun i => DH dr Ar p q x i
  let Pl : Fin 3 → Half →L[ℝ] Neg := fun i => PL dr Ar p q x i
  let Dl : Fin 3 → Half →L[ℝ] Neg := fun i => DL dr Ar p q x i
  let dPc : Fin 3 → Fin 3 → Hi →L[ℝ] Half := fun a i =>
    directionalFDeriv (coordinateDirection a) (fun y => PH dr Ar p q y i) x
  let dDc : Fin 3 → Fin 3 → Hi →L[ℝ] Half := fun a i =>
    directionalFDeriv (coordinateDirection a) (fun y => DH dr Ar p q y i) x
  let dPl : Fin 3 → Fin 3 → Half →L[ℝ] Neg := fun a i =>
    directionalFDeriv (coordinateDirection a) (fun y => PL dr Ar p q y i) x
  let dDl : Fin 3 → Fin 3 → Half →L[ℝ] Neg := fun a i =>
    directionalFDeriv (coordinateDirection a) (fun y => DL dr Ar p q y i) x
  have hSym (a b : Half) : QPP a (JL b)=QPP b (JL a) := by
    change PP a (JL b)=PP b (JL a)
    rw [ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD a b,
      ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD b a]
    exact real_inner_comm _ _
  have hP (i : Fin 3) (v : Hi) (z : Half) : QPP (IH v) (Dl i z)=-QPP (Pc i v) (JL z) := by
    exact (ActualPPLowerRemainder.actual_first_high_pivots
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q x hT.self_of_nhds i v z).1
  have hReversePivot (i : Fin 3) (v : Hi) (z : Half) : QPP (IH v) (Pl i z)=-QPP (Dc i v) (JL z) := by
    exact (ActualPPLowerRemainder.actual_first_high_pivots
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q x hT.self_of_nhds i v z).2
  have hDP (dir i : Fin 3) (v : Hi) (z : Half) :
      QPP (IH v) (dDl dir i z)=-QPP (dPc dir i v) (JL z) := by
    apply ActualPPWeakLower.differentiated_low_pivot QPP IH JL
      (fun y => PH dr Ar p q y i) (fun y => DL dr Ar p q y i) x (coordinateDirection dir)
      ((hc i).1.1.differentiableAt (by simp)) ((hc i).2.2.2.1.differentiableAt (by simp))
    filter_upwards [hT] with y hy
    intro vv zz
    exact (ActualPPLowerRemainder.actual_first_high_pivots
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q y hy i vv zz).1
  have hDD (dir i : Fin 3) (v : Hi) (z : Half) :
      QPP (IH v) (dPl dir i z)=-QPP (dDc dir i v) (JL z) := by
    apply ActualPPWeakLower.differentiated_low_pivot QPP IH JL
      (fun y => DH dr Ar p q y i) (fun y => PL dr Ar p q y i) x (coordinateDirection dir)
      ((hc i).2.2.1.1.differentiableAt (by simp)) ((hc i).2.1.1.differentiableAt (by simp))
    filter_upwards [hT] with y hy
    intro vv zz
    exact (ActualPPLowerRemainder.actual_first_high_pivots
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q y hy i vv zz).2
  let UU := UF F x
  let DU : Fin 3 → Hi := fun i => directionalFDeriv (coordinateDirection i) (UF F) x
  let mu : R3 → ℝ := fun y => referenceDensityFamily g L (q,y)
  have hdu (i : Fin 3) : directionalFDeriv (coordinateDirection i) (HU F) x=IH (DU i) :=
    ActualHigherSScalarCommutatorNativeForm.directional_halfInput hO hD F (coordinateDirection i) x
  have hbalance := transpose_six_term_row QPP Pc Dc Pl Dl dPc dDc dPl dDl
    hSym hP hReversePivot hDP hDD UU DU (mu x)
    (directionalFDeriv (coordinateDirection l) mu x)
    (directionalFDeriv (coordinateDirection k) mu x) l k
  simpa only [actualPPRawRow,ActualPPLowerRemainder.actualPPBalancedRow,
    ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply,
    Pc,Dc,Pl,Dl,dPc,dDc,dPl,dDl,UU,DU,mu,hdu] using hbalance
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPBalancedIdentity
