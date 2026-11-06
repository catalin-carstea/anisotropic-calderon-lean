import Calderon.ActualLeadingPhysicalSignedSecondForm
import Calderon.ActualHigherSAdjointFormation
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPLowerRemainder
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualHigherSLeadingBracketGain ConformalDepth PrincipalCommutator
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
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

def actualPPReverseFirstHigh (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (l : Fin 3) : Hi →L[ℝ] Half :=
  (-(referenceRadius dr Ar p L x)^2) • orderedReverseFirstCoordinateFactorHigh
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l ((Tq dr Ar p q) x)
local notation "DH" => actualPPReverseFirstHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2

def actualPPFirstOut (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  KL (∑ k : Fin 3, PH dr Ar p q x k (directionalFDeriv (coordinateDirection k) (UF F) x))
def actualPPReverseFirstOut (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  KL (∑ l : Fin 3, DH dr Ar p q x l (directionalFDeriv (coordinateDirection l) (UF F) x))

def actualPPBalancedRow (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (l k : Fin 3) : ℝ :=
  let U := UF F x
  let du := fun i => directionalFDeriv (coordinateDirection i) (HU F) x
  let mu := fun y : R3 => referenceDensityFamily g L (q,y)
  mu x*(PP (du k) (DL dr Ar p q x k
      ((directionalFDeriv (coordinateDirection l) (fun y => PH dr Ar p q y l) x) U))+
    PP (du k) ((directionalFDeriv (coordinateDirection l) (fun y => DL dr Ar p q y k) x)
      (PH dr Ar p q x l U))-
    PP (du l) (PL dr Ar p q x l
      ((directionalFDeriv (coordinateDirection k) (fun y => DH dr Ar p q y k) x) U))-
    PP (du l) ((directionalFDeriv (coordinateDirection k) (fun y => PL dr Ar p q y l) x)
      (DH dr Ar p q x k U)))+
  directionalFDeriv (coordinateDirection l) mu x*
    PP (du k) (DL dr Ar p q x k (PH dr Ar p q x l U))-
  directionalFDeriv (coordinateDirection k) mu x*
    PP (du l) (PL dr Ar p q x l (DH dr Ar p q x k U))


local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "QPP" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL

/-- Actual arbitrary-Half pivot from the SAME retained Pi germ/segment.
The proof is reproduced from the checked source API, not imported from an
unqualified other author body or assumed as a callback. -/
lemma actual_low_pivot (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom data.δ) (v z : Half) :
    PP v (EL i t z)=PP z (BL i t v) := by
  have ht0 : t ∈ ParamRoom data.δ0 :=
    ⟨commonRoom_mono y0 ρ data.δ_le0 ht.1,ht.2⟩
  have hp := (data.germs.piGerm i t ht0).self_of_nhds
  have hseg := segment_of_mem_commonRoom hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData data.parameter_subset t.1 ht.1
  have hpiv := canonicalLow_explicit_ordered_reverse_pairing
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t hseg
    (ActualPiJacobiRadialGainedRows.piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      data.δ0 data.germs i t) hp.2.1 hp.2.2 v z
  simpa only [orderedReverseLow,originalRadialReverseLow,jacobiAngularReverseLow] using hpiv

lemma actual_high_low_graphs (i : Fin 3) (t : Tpar)
    (ht : t ∈ ParamRoom data.δ) (v : Hi) :
    JL (EH i t v)=EL i t (IH v) ∧ JL (BH i t v)=BL i t (IH v) := by
  have ht0 : t ∈ ParamRoom data.δ0 :=
    ⟨commonRoom_mono y0 ρ data.δ_le0 ht.1,ht.2⟩
  have hp := (data.germs.piGerm i t ht0).self_of_nhds
  have hseg := segment_of_mem_commonRoom hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData data.parameter_subset t.1 ht.1
  let jets := ActualPiJacobiRadialGainedRows.piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    data.δ0 data.germs i t
  refine ⟨?_,?_⟩
  · exact canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg i t hseg jets hp.1 hp.2.1 v
  · simpa only [orderedReverseHigh,orderedReverseLow,originalRadialReverseHigh,
      originalRadialReverseLow,jacobiAngularReverseHigh,jacobiAngularReverseLow] using
      explicit_ordered_reverse_high_low_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t hseg jets hp.2.1 hp.2.2 v

/- Small typed algebra boundaries avoid unfolding any physical operator body. -/
private lemma weighted_inclusion_graph {E H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (I : E →L[ℝ] H) (J : H →L[ℝ] N)
    (A : Fin 3 → E →L[ℝ] H) (B : Fin 3 → H →L[ℝ] N)
    (h : ∀ i (v : E), J (A i v)=B i (I v))
    (r : ℝ) (a : Fin 3 → ℝ) (v : E) :
    J ((r • ∑ i : Fin 3, a i • A i) v)=(r • ∑ i : Fin 3, a i • B i) (I v) := by
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum]
  simp_rw [h]

private lemma weighted_low_pivot {H N : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : H →L[ℝ] N →L[ℝ] ℝ) (A B : Fin 3 → H →L[ℝ] N)
    (h : ∀ i (v z : H), P v (A i z)=P z (B i v))
    (r : ℝ) (a : Fin 3 → ℝ) (v z : H) :
    P v ((r • ∑ i : Fin 3, a i • A i) z)=
      -P z (((-r) • ∑ i : Fin 3, a i • B i) v) := by
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum,smul_eq_mul]
  simp_rw [h]
  ring

/-- Typed four contractions retain precisely the checked original coefficient definitions. -/
lemma actual_first_coordinate_contractions (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (k : Fin 3) :
    let t := (Tq dr Ar p q) x
    let r := referenceRadius dr Ar p L x
    let a := fun i => firstCoordinateWeight g g2 L k i t
    PH dr Ar p q x k=r^2 • (∑ i : Fin 3,a i • EH i t) ∧
    PL dr Ar p q x k=r^2 • (∑ i : Fin 3,a i • EL i t) ∧
    DH dr Ar p q x k=(-r^2) • (∑ i : Fin 3,a i • BH i t) ∧
    DL dr Ar p q x k=(-r^2) • (∑ i : Fin 3,a i • BL i t) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · unfold ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
    exact congrArg (fun A : Hi →L[ℝ] Half => (referenceRadius dr Ar p L x)^2 • A)
      (highFirstCoordinateFactor_eq_contracted g L y0 Φ B ε C ρ H a w hData hg hcalc
        hF hO hD τ0 g2 k ((Tq dr Ar p q) x))
  · unfold ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
    exact congrArg (fun A : Half →L[ℝ] Neg => (referenceRadius dr Ar p L x)^2 • A)
      (firstCoordinateFactor_eq_contracted g L y0 Φ B ε C ρ H a w hData hg hcalc
        hF hO hD τ0 g2 k ((Tq dr Ar p q) x))
  · rfl
  · have hh := ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient_eq_contracted
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x k
    simpa only [orderedReverseFirstCoordinateFactorLow] using hh

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  actualPPReverseFirstHigh sphereSobolevInclusionL sphereSobolevHalfToSphereL2L
  ActualHigherSFormation.higherSInput ActualHigherSScalarCommutatorNativeForm.halfInput

/-- Both original first-coefficient graphs, with the genuine minus reverse. -/
lemma actual_first_high_low_graphs (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom data.δ) (k : Fin 3) (v : Hi) :
    JL (PH dr Ar p q x k v)=PL dr Ar p q x k (IH v) ∧
    JL (DH dr Ar p q x k v)=DL dr Ar p q x k (IH v) := by
  let t : Tpar := (Tq dr Ar p q) x
  let r : ℝ := referenceRadius dr Ar p L x
  let weight : Fin 3 → ℝ := fun i => firstCoordinateWeight g g2 L k i t
  have hbase (i : Fin 3) (vv : Hi) : JL (EH i t vv)=EL i t (IH vv) ∧
      JL (BH i t vv)=BL i t (IH vv) :=
    actual_high_low_graphs g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 Room hreg data i t ht vv
  have hPH : PH dr Ar p q x k=r^2 • (∑ i : Fin 3,weight i • EH i t) :=
    (actual_first_coordinate_contractions g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 g2 dr Ar p q x k).1
  have hPL : PL dr Ar p q x k=r^2 • (∑ i : Fin 3,weight i • EL i t) :=
    (actual_first_coordinate_contractions g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 g2 dr Ar p q x k).2.1
  have hDH : DH dr Ar p q x k=(-r^2) • (∑ i : Fin 3,weight i • BH i t) :=
    (actual_first_coordinate_contractions g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 g2 dr Ar p q x k).2.2.1
  have hDL : DL dr Ar p q x k=(-r^2) • (∑ i : Fin 3,weight i • BL i t) :=
    (actual_first_coordinate_contractions g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 g2 dr Ar p q x k).2.2.2
  have hWeightedP : JL ((r^2 • ∑ i : Fin 3,weight i • EH i t) v)=
      (r^2 • ∑ i : Fin 3,weight i • EL i t) (IH v) :=
    weighted_inclusion_graph IH JL (fun i => EH i t) (fun i => EL i t)
      (fun i vv => (hbase i vv).1) (r^2) weight v
  have hWeightedD : JL (((-r^2) • ∑ i : Fin 3,weight i • BH i t) v)=
      ((-r^2) • ∑ i : Fin 3,weight i • BL i t) (IH v) :=
    weighted_inclusion_graph IH JL (fun i => BH i t) (fun i => BL i t)
      (fun i vv => (hbase i vv).2) (-r^2) weight v
  have hpv := congrArg (fun A : Hi →L[ℝ] Half => A v) hPH
  have hplv := congrArg (fun A : Half →L[ℝ] Neg => A (IH v)) hPL
  have hdv := congrArg (fun A : Hi →L[ℝ] Half => A v) hDH
  have hdlv := congrArg (fun A : Half →L[ℝ] Neg => A (IH v)) hDL
  exact ⟨(congrArg (fun z : Half => JL z) hpv).trans (hWeightedP.trans hplv.symm),
    (congrArg (fun z : Half => JL z) hdv).trans (hWeightedD.trans hdlv.symm)⟩

/-- Actual complete first-coordinate low pivot, arbitrary Half arguments.
Both scalar coordinate contractions and both Q orders remain unchanged. -/
lemma actual_first_low_pivot (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom data.δ) (k : Fin 3) (v z : Half) :
    PP v (PL dr Ar p q x k z) = -PP z (DL dr Ar p q x k v) := by
  let t : Tpar := (Tq dr Ar p q) x
  let r : ℝ := referenceRadius dr Ar p L x
  let weight : Fin 3 → ℝ := fun i => firstCoordinateWeight g g2 L k i t
  have hbase (i : Fin 3) (v1 v2 : Half) : QPP v1 (EL i t v2)=QPP v2 (BL i t v1) :=
    actual_low_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 Room hreg data i t ht v1 v2
  have hPL : PL dr Ar p q x k=r^2 • (∑ i : Fin 3,weight i • EL i t) :=
    (actual_first_coordinate_contractions g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 g2 dr Ar p q x k).2.1
  have hDL : DL dr Ar p q x k=(-r^2) • (∑ i : Fin 3,weight i • BL i t) :=
    (actual_first_coordinate_contractions g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 g2 dr Ar p q x k).2.2.2
  have hWeighted : QPP v ((r^2 • ∑ i : Fin 3,weight i • EL i t) z)=
      -QPP z (((-r^2) • ∑ i : Fin 3,weight i • BL i t) v) :=
    weighted_low_pivot QPP (fun i => EL i t) (fun i => BL i t) hbase (r^2) weight v z
  have hplz := congrArg (fun A : Half →L[ℝ] Neg => A z) hPL
  have hdlv := congrArg (fun A : Half →L[ℝ] Neg => A v) hDL
  change QPP v (PL dr Ar p q x k z)=-QPP z (DL dr Ar p q x k v)
  exact (congrArg (fun n : Neg => QPP v n) hplz).trans
    (hWeighted.trans (congrArg (fun n : Neg => -QPP z n) hdlv).symm)

/-- The two genuine high-to-low adjunctions for arbitrary Half output tests. -/
lemma actual_first_high_pivots (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom data.δ) (k : Fin 3) (v : Hi) (z : Half) :
    PP (IH v) (DL dr Ar p q x k z)=-PP (PH dr Ar p q x k v) (JL z) ∧
    PP (IH v) (PL dr Ar p q x k z)=-PP (DH dr Ar p q x k v) (JL z) := by
  have hsym (a b : Half) : PP a (JL b)=PP b (JL a) := by
    rw [ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD a b,
      ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD b a]
    exact real_inner_comm _ _
  have hgraphs := actual_first_high_low_graphs g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 Room hreg data g2 dr Ar p q x ht k v
  have hlow1 := actual_first_low_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 Room hreg data g2 dr Ar p q x ht k z (IH v)
  have hlow2 := actual_first_low_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 Room hreg data g2 dr Ar p q x ht k (IH v) z
  refine ⟨?_,?_⟩
  · calc
      _ = -PP z (PL dr Ar p q x k (IH v)) := by linarith only [hlow1]
      _ = -PP z (JL (PH dr Ar p q x k v)) := congrArg (fun n : Neg => -PP z n) hgraphs.1.symm
      _ = _ := congrArg Neg.neg (hsym z (PH dr Ar p q x k v))
  · calc
      _ = -PP z (DL dr Ar p q x k (IH v)) := hlow2
      _ = -PP z (JL (DH dr Ar p q x k v)) := congrArg (fun n : Neg => -PP z n) hgraphs.2.symm
      _ = _ := congrArg Neg.neg (hsym z (DH dr Ar p q x k v))

private lemma norm_sum_sq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (K : V →L[ℝ] W) (v : Fin 3 → V) :
    ‖K (∑ i : Fin 3, v i)‖^2 =
      ∑ i : Fin 3, ∑ j : Fin 3, ⟪K (v i),K (v j)⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [map_sum,sum_inner,inner_sum]
  exact Finset.sum_comm

private lemma sum_two_sub_of_rows (A B R : Fin 3 → Fin 3 → ℝ)
    (h : ∀ l k : Fin 3, A l k-B l k=R l k) :
    (∑ l : Fin 3,∑ k : Fin 3,A l k)-(∑ l : Fin 3,∑ k : Fin 3,B l k)=
      ∑ l : Fin 3,∑ k : Fin 3,R l k := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun k _ => h l k)

/-- Exact full physical first/first norm expansion at an actual retained point.
The derivative test vectors are Hi inputs; no angular output is assumed finite. -/
theorem actual_first_first_norm_pointwise (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom data.δ) :
    ‖actualPPFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x‖^2-
    ‖actualPPReverseFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x‖^2 =
    ∑ l : Fin 3, ∑ k : Fin 3,
      (-PP (directionalFDeriv (coordinateDirection l) (HU F) x)
        (DL dr Ar p q x l (PH dr Ar p q x k
          (directionalFDeriv (coordinateDirection k) (UF F) x)))+
      PP (directionalFDeriv (coordinateDirection k) (HU F) x)
        (PL dr Ar p q x k (DH dr Ar p q x l
          (directionalFDeriv (coordinateDirection l) (UF F) x)))) := by
  let dU : Fin 3 → Hi := fun i => directionalFDeriv (coordinateDirection i) (UF F) x
  let phVec : Fin 3 → Half := fun i => PH dr Ar p q x i (dU i)
  let dhVec : Fin 3 → Half := fun i => DH dr Ar p q x i (dU i)
  have hdu (i : Fin 3) : directionalFDeriv (coordinateDirection i) (HU F) x=IH (dU i) :=
    ActualHigherSScalarCommutatorNativeForm.directional_halfInput hO hD F (coordinateDirection i) x
  have hrow (l k : Fin 3) :
      ⟪KL (phVec l),KL (phVec k)⟫_ℝ-⟪KL (dhVec l),KL (dhVec k)⟫_ℝ =
      -PP (IH (dU l)) (DL dr Ar p q x l (PH dr Ar p q x k (dU k)))+
      PP (IH (dU k)) (PL dr Ar p q x k (DH dr Ar p q x l (dU l))) := by
    have hp := (actual_first_high_pivots g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 Room hreg data g2 dr Ar p q x ht l (dU l) (phVec k)).1
    have hd := (actual_first_high_pivots g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 Room hreg data g2 dr Ar p q x ht k (dU k) (dhVec l)).2
    rw [ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD] at hp hd
    have hp' : PP (IH (dU l)) (DL dr Ar p q x l (PH dr Ar p q x k (dU k)))=
        -⟪KL (phVec l),KL (phVec k)⟫_ℝ := by simpa only [phVec] using hp
    have hd' : PP (IH (dU k)) (PL dr Ar p q x k (DH dr Ar p q x l (dU l)))=
        -⟪KL (dhVec k),KL (dhVec l)⟫_ℝ := by simpa only [dhVec] using hd
    have hCommD : ⟪KL (dhVec k),KL (dhVec l)⟫_ℝ=⟪KL (dhVec l),KL (dhVec k)⟫_ℝ :=
      real_inner_comm _ _
    have hd'' := hd'.trans (congrArg Neg.neg hCommD)
    linarith only [hp',hd'']
  have hPn : ‖KL (∑ i : Fin 3,phVec i)‖^2=
      ∑ l : Fin 3,∑ k : Fin 3,⟪KL (phVec l),KL (phVec k)⟫_ℝ :=
    norm_sum_sq (V := Half) (W := SphereL2) KL phVec
  have hDn : ‖KL (∑ i : Fin 3,dhVec i)‖^2=
      ∑ l : Fin 3,∑ k : Fin 3,⟪KL (dhVec l),KL (dhVec k)⟫_ℝ :=
    norm_sum_sq (V := Half) (W := SphereL2) KL dhVec
  have hPOut : actualPPFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x=
      KL (∑ i : Fin 3,phVec i) := rfl
  have hDOut : actualPPReverseFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x=
      KL (∑ i : Fin 3,dhVec i) := rfl
  have hPnorm : ‖actualPPFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x‖^2=
      ∑ l : Fin 3,∑ k : Fin 3,⟪KL (phVec l),KL (phVec k)⟫_ℝ :=
    (congrArg (fun v1 : SphereL2 => ‖v1‖^2) hPOut).trans hPn
  have hDnorm : ‖actualPPReverseFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x‖^2=
      ∑ l : Fin 3,∑ k : Fin 3,⟪KL (dhVec l),KL (dhVec k)⟫_ℝ :=
    (congrArg (fun v1 : SphereL2 => ‖v1‖^2) hDOut).trans hDn
  have hDiff := congrArg₂ (fun n1 n2 : ℝ => n1-n2) hPnorm hDnorm
  let rowP : Fin 3 → Fin 3 → ℝ := fun l k => ⟪KL (phVec l),KL (phVec k)⟫_ℝ
  let rowD : Fin 3 → Fin 3 → ℝ := fun l k => ⟪KL (dhVec l),KL (dhVec k)⟫_ℝ
  let rowR : Fin 3 → Fin 3 → ℝ := fun l k =>
    -PP (directionalFDeriv (coordinateDirection l) (HU F) x)
      (DL dr Ar p q x l (PH dr Ar p q x k (dU k)))+
    PP (directionalFDeriv (coordinateDirection k) (HU F) x)
      (PL dr Ar p q x k (DH dr Ar p q x l (dU l)))
  have hRows (l k : Fin 3) : rowP l k-rowD l k=rowR l k := by
    have hLeft := congrArg (fun vv : Half =>
      -PP vv (DL dr Ar p q x l (PH dr Ar p q x k (dU k)))) (hdu l).symm
    have hRight := congrArg (fun vv : Half =>
      PP vv (PL dr Ar p q x k (DH dr Ar p q x l (dU l)))) (hdu k).symm
    exact (hrow l k).trans (congrArg₂ (fun n1 n2 : ℝ => n1+n2) hLeft hRight)
  have hsum : (∑ l : Fin 3,∑ k : Fin 3,rowP l k)-
      (∑ l : Fin 3,∑ k : Fin 3,rowD l k)=∑ l : Fin 3,∑ k : Fin 3,rowR l k :=
    sum_two_sub_of_rows rowP rowD rowR hRows
  exact hDiff.trans hsum
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPLowerRemainder
