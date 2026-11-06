import Calderon.ActualPPBalancedIdentity
import Calderon.ActualPPBalancedBound
import Calderon.ActualPPProductDerivative
import Calderon.ActualHigherSAdjointFormation
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPLowerRemainder
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualHigherSLeadingBracketGain ConformalDepth PrincipalCommutator
  ActualPPCoefficientCaps ActualHigherSScalarCommutatorForm
  ActualScalarPrincipalSelfFormBound FixedParameterProfilePullback
  ActualHigherSScalarCommutatorCoefficients
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
private lemma expand_two_composed_rows_at
    {V M N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : V →L[ℝ] N →L[ℝ] ℝ)
    (Lmap Kmap : R3 → M →L[ℝ] N) (Amap Bmap : R3 → V →L[ℝ] M)
    (x X Y : R3) (v dvK dvL : V) (mu dmL dmK : ℝ)
    (hLmap : DifferentiableAt ℝ Lmap x) (hAmap : DifferentiableAt ℝ Amap x)
    (hKmap : DifferentiableAt ℝ Kmap x) (hBmap : DifferentiableAt ℝ Bmap x) :
    dmL*P v (((Lmap x).comp (Amap x)) dvK)+
      mu*P v ((directionalFDeriv X (fun y => (Lmap y).comp (Amap y)) x) dvK)-
      dmK*P v (((Kmap x).comp (Bmap x)) dvL)-
      mu*P v ((directionalFDeriv Y (fun y => (Kmap y).comp (Bmap y)) x) dvL) =
    mu*(P v ((directionalFDeriv X Lmap x) (Amap x dvK))+
      P v (Lmap x ((directionalFDeriv X Amap x) dvK))-
      P v ((directionalFDeriv Y Kmap x) (Bmap x dvL))-
      P v (Kmap x ((directionalFDeriv Y Bmap x) dvL)))+
      dmL*P v (Lmap x (Amap x dvK))-dmK*P v (Kmap x (Bmap x dvL)) := by
  have hProduct := ActualPPProductDerivative.directional_composition_apply_at
    (E := V) (H := M) (N := N)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hProduct
  have hLeft := hProduct Lmap Amap x X hLmap hAmap dvK
  have hRight := hProduct Kmap Bmap x Y hKmap hBmap dvL
  rw [hLeft,hRight]
  simp only [ContinuousLinearMap.comp_apply,map_add]
  ring

private lemma leading_row_of_clm_graph
    {V M N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (I : V →L[ℝ] M) (P : M →L[ℝ] N →L[ℝ] ℝ)
    (A B : V →L[ℝ] N) (Cmap : M →L[ℝ] N)
    (hGraph : Cmap.comp I=A-B)
    (u w1 w2 : V) (v s : M) (mu : ℝ)
    (hV : v=I u) (hS : s=I w1) (hComm : w2=w1) :
    mu*(P (I u) (A w1)-P (I u) (B w2))=mu*P v (Cmap s) := by
  have hValue : Cmap (I w1)=A w1-B w1 := by
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply] using
      congrArg (fun D : V →L[ℝ] N => D w1) hGraph
  rw [hV,hS,hComm,hValue,map_sub]

private lemma weighted_pair_fin3_sum2
    {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : M →L[ℝ] N →L[ℝ] ℝ) (u : M) (v : Fin 3 → Fin 3 → N) (mu : ℝ) :
    mu*P u (∑ l : Fin 3, ∑ k : Fin 3, v l k)=
      ∑ l : Fin 3, ∑ k : Fin 3, mu*P u (v l k) := by
  simp only [map_sum,Finset.mul_sum]

private lemma abs_zero_le_nonneg_product (z c eta e : ℝ)
    (hz : z=0) (hc : 0 ≤ c) (heta : 0 ≤ eta) (he : 0 ≤ e) :
    |z| ≤ (c*eta)*e := by
  rw [hz,abs_zero]
  exact mul_nonneg (mul_nonneg hc heta) he

private lemma half_pairing_zero_left (z : Neg) : PP (0 : Half) z=0 := by
  change ActualHigherSScalarCommutatorNativeForm.halfDualPairingL (0 : Half) z=0
  simp only [map_zero,ContinuousLinearMap.zero_apply]

attribute [local irreducible]
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh
  ActualPPBalancedIdentity.actualPPRawRow ActualPPLowerRemainder.actualPPBalancedRow

attribute [local irreducible] orderedReverseFirstCoordinateFactorLow
  orderedReverseFirstCoordinateFactorHigh
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateFactor
  ActualHigherSFirstCoefficientJets.firstCoordinateFactor physicalLeadingCoefficient

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


local notation "DH" => actualPPReverseFirstHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "QPP" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
local notation "PO" => actualPPFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DO" => actualPPReverseFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "BR" => actualPPBalancedRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2

private def composedPPRow (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (l k : Fin 3) : ℝ :=
  let U := UF F
  let dU := fun i => directionalFDeriv (coordinateDirection i) U
  let mu := fun y : R3 => referenceDensityFamily g L (q,y)
  let Q : Hi →L[ℝ] Neg →L[ℝ] ℝ := (QPP).comp IH
  let C1 := fun y => (DL dr Ar p q y l).comp (PH dr Ar p q y k)
  let C2 := fun y => (PL dr Ar p q y k).comp (DH dr Ar p q y l)
  directionalFDeriv (coordinateDirection l) mu x*Q (U x) (C1 x (dU k x))+
    mu x*Q (U x) (directionalFDeriv (coordinateDirection l) C1 x (dU k x))-
    directionalFDeriv (coordinateDirection k) mu x*Q (U x) (C2 x (dU l x))-
    mu x*Q (U x) (directionalFDeriv (coordinateDirection k) C2 x (dU l x))
local notation "CR" => composedPPRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2

private lemma composedPPRow_eq_balanced_at (hL : 0 < L) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p) (eta : ℝ)
    (heta : 0 ≤ eta) (heta0 : eta ≤ data.eta0) (x : R3)
    (hx : x ∈ closedBall y0 ρ) (hxBall : x ∈ ball y0 ρ)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (hT : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈
      Set.prod (commonRoom y0 ρ data.δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1))
    (F : smoothCompactFiniteSphereCore hO hD) (l k : Fin 3)
    (hdL : DifferentiableAt ℝ (fun y => DL dr Ar p q y l) x)
    (hdA : DifferentiableAt ℝ (fun y => PH dr Ar p q y k) x)
    (hdK : DifferentiableAt ℝ (fun y => PL dr Ar p q y k) x)
    (hdB : DifferentiableAt ℝ (fun y => DH dr Ar p q y l) x) :
    CR dr Ar p q F x l k=BR dr Ar p q F x l k := by
  have hExpand0 := expand_two_composed_rows_at (V := Hi) (M := Half) (N := Neg)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hExpand0
  have hExpand := hExpand0 ((QPP).comp IH)
    (fun y => DL dr Ar p q y l) (fun y => PL dr Ar p q y k)
    (fun y => PH dr Ar p q y k) (fun y => DH dr Ar p q y l)
    x (coordinateDirection l) (coordinateDirection k) (UF F x)
    (directionalFDeriv (coordinateDirection k) (UF F) x)
    (directionalFDeriv (coordinateDirection l) (UF F) x)
    (referenceDensityFamily g L (q,x))
    (directionalFDeriv (coordinateDirection l) (fun y => referenceDensityFamily g L (q,y)) x)
    (directionalFDeriv (coordinateDirection k) (fun y => referenceDensityFamily g L (q,y)) x)
    hdL hdA hdK hdB
  have hRaw : CR dr Ar p q F x l k=ActualPPBalancedIdentity.actualPPRawRow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x l k := by
    simpa only [composedPPRow,ActualPPBalancedIdentity.actualPPRawRow,
      ContinuousLinearMap.comp_apply,
      ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hExpand
  have hBalanced := ActualPPBalancedIdentity.actual_raw_row_eq_balanced
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hL hg2
    q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs hT F l k
  exact hRaw.trans hBalanced

private lemma actual_pp_DL_wrapper (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (l : Fin 3) :
    DL dr Ar p q x l = (-(referenceRadius dr Ar p L x)^2) •
      orderedReverseFirstCoordinateFactorLow g L y0 Φ B ε C ρ H a w hData hg hcalc
        hF hO hD τ0 g2 l ((Tq dr Ar p q) x) := by
  have hNative := ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient_eq_contracted
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x l
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hNative
  exact hNative

private lemma actual_pp_PH_wrapper (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (k : Fin 3) :
    PH dr Ar p q x k = (referenceRadius dr Ar p L x)^2 •
      ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateFactor
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k ((Tq dr Ar p q) x) := by
  unfold ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  rfl

private lemma actual_pp_PL_wrapper (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (k : Fin 3) :
    PL dr Ar p q x k = (referenceRadius dr Ar p L x)^2 •
      ActualHigherSFirstCoefficientJets.firstCoordinateFactor
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k ((Tq dr Ar p q) x) := by
  unfold ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  rfl

private lemma actual_pp_DH_wrapper (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (l : Fin 3) :
    DH dr Ar p q x l = (-(referenceRadius dr Ar p L x)^2) •
      orderedReverseFirstCoordinateFactorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc
        hF hO hD τ0 g2 l ((Tq dr Ar p q) x) := by
  unfold actualPPReverseFirstHigh
  rfl

private lemma actual_pp_physical_leading_graph
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (ht : (Tq dr Ar p q) x ∈
      Set.prod (commonRoom y0 ρ data.δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)) :
    (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q l k x).comp IH =
      (DL dr Ar p q x l).comp (PH dr Ar p q x k)-
        (PL dr Ar p q x k).comp (DH dr Ar p q x l) := by
  let r : ℝ := referenceRadius dr Ar p L x
  let t := (Tq dr Ar p q) x
  let Lraw : Half →L[ℝ] Neg := (-r^2) • orderedReverseFirstCoordinateFactorLow
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l t
  let Araw : Hi →L[ℝ] Half := r^2 •
    ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateFactor
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k t
  let Kraw : Half →L[ℝ] Neg := r^2 • ActualHigherSFirstCoefficientJets.firstCoordinateFactor
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k t
  let Braw : Hi →L[ℝ] Half := (-r^2) • orderedReverseFirstCoordinateFactorHigh
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 l t
  have hLraw : Lraw=DL dr Ar p q x l :=
    (actual_pp_DL_wrapper g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x l).symm
  have hAraw : Araw=PH dr Ar p q x k :=
    (actual_pp_PH_wrapper g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x k).symm
  have hKraw : Kraw=PL dr Ar p q x k :=
    (actual_pp_PL_wrapper g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x k).symm
  have hBraw : Braw=DH dr Ar p q x l :=
    (actual_pp_DH_wrapper g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x l).symm
  have hFirst : Lraw.comp Araw=(DL dr Ar p q x l).comp (PH dr Ar p q x k) :=
    congrArg₂ (fun (V1 : Half →L[ℝ] Neg) (V2 : Hi →L[ℝ] Half) => V1.comp V2) hLraw hAraw
  have hSecond : Kraw.comp Braw=(PL dr Ar p q x k).comp (DH dr Ar p q x l) :=
    congrArg₂ (fun (V1 : Half →L[ℝ] Neg) (V2 : Hi →L[ℝ] Half) => V1.comp V2) hKraw hBraw
  have hRaw : (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q l k x).comp IH=Lraw.comp Araw-Kraw.comp Braw :=
    physicalLeadingCoefficient_gain_graph_on_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x ht
  exact hRaw.trans (congrArg₂ (fun (V1 V2 : Hi →L[ℝ] Neg) => V1-V2) hFirst hSecond)

private lemma actual_pp_second_input (F : smoothCompactFiniteSphereCore hO hD)
    (l k : Fin 3) (x : R3) :
    directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) (HU F)) x =
      IH (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) (UF F)) x) := by
  have hU : ContDiff ℝ ∞ (UF F) := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hDerivative := ActualHigherSFirstPhysicalCommutatorGraph.directional_second_linear_input
    (E := Hi) (M := Half)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hDerivative
  exact hDerivative IH (UF F) hU (coordinateDirection l) (coordinateDirection k) x

private lemma actual_pp_leading_row_at
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (l k : Fin 3)
    (ht : (Tq dr Ar p q) x ∈
      Set.prod (commonRoom y0 ρ data.δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)) :
    let U := UF F
    let u := HU F
    let mu := fun y : R3 => referenceDensityFamily g L (q,y)
    mu x*(PP (IH (U x)) (((DL dr Ar p q x l).comp (PH dr Ar p q x k))
        (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) U) x))-
      PP (IH (U x)) (((PL dr Ar p q x k).comp (DH dr Ar p q x l))
        (directionalFDeriv (coordinateDirection k) (directionalFDeriv (coordinateDirection l) U) x))) =
    mu x*PP (u x) ((physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q l k x)
        (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x)) := by
  have hU : ContDiff ℝ ∞ (UF F) := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hComm :
      directionalFDeriv (coordinateDirection k) (directionalFDeriv (coordinateDirection l) (UF F)) x =
      directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) (UF F)) x :=
    directionalFDeriv_commute (coordinateDirection k) (coordinateDirection l) (UF F) hU x
  have hInput : HU F x=IH (UF F x) := rfl
  have hSecond := actual_pp_second_input hO hD F l k x
  have hMap := actual_pp_physical_leading_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q l k x ht
  have hRow0 := leading_row_of_clm_graph (V := Hi) (M := Half) (N := Neg)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hRow0
  have hRow := hRow0 IH QPP
    ((DL dr Ar p q x l).comp (PH dr Ar p q x k))
    ((PL dr Ar p q x k).comp (DH dr Ar p q x l))
    (physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q l k x) hMap
    (UF F x)
    (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) (UF F)) x)
    (directionalFDeriv (coordinateDirection k) (directionalFDeriv (coordinateDirection l) (UF F)) x)
    (HU F x)
    (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) (HU F)) x)
    (referenceDensityFamily g L (q,x)) hInput hSecond hComm
  simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hRow

private lemma actual_pp_outputs_zero_of_derivatives
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hzero : ∀ i : Fin 3, directionalFDeriv (coordinateDirection i) (UF F) x=0) :
    PO dr Ar p q F x=0 ∧ DO dr Ar p q F x=0 := by
  constructor
  · simp only [actualPPFirstOut,hzero,map_zero,Finset.sum_const_zero]
  · simp only [actualPPReverseFirstOut,hzero,map_zero,Finset.sum_const_zero]

/-- Exact ACTUAL original-hypothesis target; no structural/cap callback is a premise. -/
def ActualPPLowerRemainderContract : Prop :=
  ∃ CPP etaPP : ℝ, 0 < CPP ∧ 0 < etaPP ∧ etaPP ≤ data.eta0 ∧
    ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaPP →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    let mu := fun x : R3 => referenceDensityFamily g L (q,x)
    let lead := fun x : R3 => mu x*PP (HU F x) (Lead dr Ar p q F x)
    let rem := fun x : R3 => ∑ l : Fin 3, ∑ k : Fin 3, BR dr Ar p q F x l k
    let energy := fun x : R3 => mu x*finiteCoreReferenceProfileEnergy
      hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x
    Integrable (fun x => mu x*‖PO dr Ar p q F x‖^2) ∧
    Integrable (fun x => mu x*‖DO dr Ar p q F x‖^2) ∧
    Integrable lead ∧ Integrable rem ∧ Integrable energy ∧
    (∀ l k : Fin 3, Integrable (fun x => BR dr Ar p q F x l k)) ∧
    ((∫ x, mu x*(‖PO dr Ar p q F x‖^2-‖DO dr Ar p q F x‖^2))=
      (∫ x, lead x)+(∫ x, rem x)) ∧
    |∫ x, rem x| ≤ CPP*eta*(∫ x, energy x)


/-- Complete actual P/P weak lower remainder and original-energy bound.
Every structural/cap hypothesis is derived below from the same original endpoint
record. -/
theorem exists_actual_pp_lower_remainder (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) (hg2 : IsAdmissibleMetric g2) :
    ActualPPLowerRemainderContract g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 Room hreg data g2 := by
  obtain ⟨CRow,hCRow,hpoint⟩ := ActualPPBalancedBound.exists_actual_balanced_row_point_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hL hg2
  obtain ⟨Mc,hMc,hcaps⟩ := exists_actual_first_coefficient_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  obtain ⟨epsG,hepsG,hepsG1,hguard⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ data.δ data.δ_pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨CLead,hCLead,hleading⟩ := exists_actual_leading_signed_second_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg data g2 hg2
  unfold ActualPPLowerRemainderContract
  refine ⟨9*(CRow+1),min data.eta0 epsG,by positivity,
    lt_min data.eta0_pos hepsG,min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaPP K hK hKball F hsupp hb hs
  have heta0 : eta ≤ data.eta0 := hetaPP.trans (min_le_left _ _)
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let U : R3 → Hi := UF F
  let u : R3 → Half := HU F
  let energy : R3 → ℝ := fun x => mu x*finiteCoreReferenceProfileEnergy
    hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x
  let Q : Hi →L[ℝ] Neg →L[ℝ] ℝ := (QPP).comp IH
  let dU : Fin 3 → R3 → Hi := fun i => directionalFDeriv (coordinateDirection i) U
  let C1 : Fin 3 → Fin 3 → R3 → Hi →L[ℝ] Neg :=
    fun l k x => (DL dr Ar p q x l).comp (PH dr Ar p q x k)
  let C2 : Fin 3 → Fin 3 → R3 → Hi →L[ℝ] Neg :=
    fun l k x => (PL dr Ar p q x k).comp (DH dr Ar p q x l)
  let Nrow : Fin 3 → Fin 3 → R3 → ℝ := fun l k x =>
    mu x*(-Q (dU l x) (C1 l k x (dU k x))+Q (dU k x) (C2 l k x (dU l x)))
  let Lraw : Fin 3 → Fin 3 → R3 → ℝ := fun l k x =>
    mu x*(Q (U x) (C1 l k x (directionalFDeriv (coordinateDirection l) (dU k) x))-
      Q (U x) (C2 l k x (directionalFDeriv (coordinateDirection k) (dU l) x)))
  let Rcomp : Fin 3 → Fin 3 → R3 → ℝ := fun l k x =>
    directionalFDeriv (coordinateDirection l) mu x*Q (U x) (C1 l k x (dU k x))+
    mu x*Q (U x) (directionalFDeriv (coordinateDirection l) (C1 l k) x (dU k x))-
    directionalFDeriv (coordinateDirection k) mu x*Q (U x) (C2 l k x (dU l x))-
    mu x*Q (U x) (directionalFDeriv (coordinateDirection k) (C2 l k) x (dU l x))
  let PCL : Fin 3 → Fin 3 → R3 → Half →L[ℝ] Neg := fun l k =>
    physicalLeadingCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q l k
  let Lrow : Fin 3 → Fin 3 → R3 → ℝ := fun l k x => mu x*PP (u x)
    (PCL l k x (directionalFDeriv (coordinateDirection l)
      (directionalFDeriv (coordinateDirection k) u) x))
  let Rrow : Fin 3 → Fin 3 → R3 → ℝ := fun l k x => BR dr Ar p q F x l k
  have hU : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hu : ContDiff ℝ ∞ u := ActualHigherSScalarCommutatorNativeForm.contDiff_halfInput hO hD F
  have h0 : ∀ x ∉ K, U x = 0 := by
    intro x hx
    have hxF : x ∉ tsupport F.val := fun ht => hx (hsupp ht)
    exact ActualHigherSFormation.finiteCoreSobolevLift_eq_zero_of_eval hO hD (3/2 : ℝ) F x
      (image_eq_zero_of_notMem_tsupport hxF)
  have hu0 : ∀ x ∉ K, u x = 0 := by intro x hx; change IH (U x)=0; rw [h0 x hx,map_zero]
  have hdUs (i : Fin 3) : ContDiff ℝ ∞ (dU i) := contDiff_directionalFDeriv _ U hU
  have hdU0 (i : Fin 3) : ∀ x ∉ K, dU i x = 0 :=
    fun x hx => directional_eq_zero_off U K hK.isClosed h0 _ x hx
  have hddUs (i j : Fin 3) : ContDiff ℝ ∞ (directionalFDeriv (coordinateDirection i) (dU j)) :=
    contDiff_directionalFDeriv _ _ (hdUs j)
  have hddU0 (i j : Fin 3) : ∀ x ∉ K, directionalFDeriv (coordinateDirection i) (dU j) x=0 :=
    fun x hx => directional_eq_zero_off (dU j) K hK.isClosed (hdU0 j) _ x hx
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hclosed (x : R3) (hx : x ∈ K) : x ∈ closedBall y0 ρ := ball_subset_closedBall (hKball hx)
  have hT (x : R3) (hx : x ∈ K) : ∀ᶠ y in 𝓝 x,
      (Tq dr Ar p q) y ∈ Set.prod (commonRoom y0 ρ data.δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1) := by
    have hg := hguard q hq dr hdr hdr1 Ar hAr p hp eta heta
      (hetaPP.trans (min_le_right _ _)) x (hclosed x hx) (hKball hx) (hb x hx) (hs x hx)
    exact higherSParam_eventually_mem y0 ρ data.δ L dr Ar q p hdr hAr x hg
  have hc (i : Fin 3) (x : R3) (hx : x ∈ K) :=
    hcaps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x (hclosed x hx) (hKball hx) (hb x hx) (hs x hx) i
  have hC1 (l k : Fin 3) : ∀ x ∈ K, ContDiffAt ℝ ∞ (C1 l k) x :=
    fun x hx => ((hc l x hx).2.2.2.1).clm_comp ((hc k x hx).1.1)
  have hC2 (l k : Fin 3) : ∀ x ∈ K, ContDiffAt ℝ ∞ (C2 l k) x :=
    fun x hx => ((hc k x hx).2.1.1).clm_comp ((hc l x hx).2.2.1.1)
  have hNint (l k : Fin 3) : Integrable (Nrow l k) := by
    have h1 := integrable_weighted_supported_operator_pair Q mu (dU l) (dU k) (C1 l k)
      K hK hmu.continuous (hdUs l).continuous (hdUs k) (hdU0 k) (hC1 l k)
    have h2 := integrable_weighted_supported_operator_pair Q mu (dU k) (dU l) (C2 l k)
      K hK hmu.continuous (hdUs k).continuous (hdUs l) (hdU0 l) (hC2 l k)
    refine (h1.neg.add h2).congr (Filter.Eventually.of_forall (fun x => ?_))
    dsimp [Nrow]
    ring
  have hLint (l k : Fin 3) : Integrable (Lraw l k) := by
    have h1 := integrable_weighted_supported_operator_pair Q mu U _ (C1 l k) K hK
      hmu.continuous hU.continuous (hddUs l k) (hddU0 l k) (hC1 l k)
    have h2 := integrable_weighted_supported_operator_pair Q mu U _ (C2 l k) K hK
      hmu.continuous hU.continuous (hddUs k l) (hddU0 k l) (hC2 l k)
    refine (h1.sub h2).congr (Filter.Eventually.of_forall (fun x => ?_))
    dsimp [Lraw]
    ring
  have hRint (l k : Fin 3) : Integrable (Rcomp l k) := by
    have h1 := integrable_weighted_supported_operator_pair Q (directionalFDeriv (coordinateDirection l) mu)
      U (dU k) (C1 l k) K hK (contDiff_directionalFDeriv _ mu hmu).continuous
      hU.continuous (hdUs k) (hdU0 k) (hC1 l k)
    have h2 := integrable_weighted_supported_operator_pair Q mu U (dU k)
      (directionalFDeriv (coordinateDirection l) (C1 l k)) K hK hmu.continuous
      hU.continuous (hdUs k) (hdU0 k)
      (fun x hx => contDiffAt_directional _ x _ (hC1 l k x hx))
    have h3 := integrable_weighted_supported_operator_pair Q (directionalFDeriv (coordinateDirection k) mu)
      U (dU l) (C2 l k) K hK (contDiff_directionalFDeriv _ mu hmu).continuous
      hU.continuous (hdUs l) (hdU0 l) (hC2 l k)
    have h4 := integrable_weighted_supported_operator_pair Q mu U (dU l)
      (directionalFDeriv (coordinateDirection k) (C2 l k)) K hK hmu.continuous
      hU.continuous (hdUs l) (hdU0 l)
      (fun x hx => contDiffAt_directional _ x _ (hC2 l k x hx))
    exact ((h1.add h2).sub h3).sub h4
  have hRcompZero (l k : Fin 3) (x : R3) (hx : x ∉ K) : Rcomp l k x=0 := by
    simp only [Rcomp,hdU0 _ x hx,map_zero,mul_zero,zero_add,sub_zero]
  have hRfun (l k : Fin 3) : Rcomp l k=Rrow l k := by
    funext x
    by_cases hx : x ∈ K
    · have hdL : DifferentiableAt ℝ (fun y => DL dr Ar p q y l) x :=
        (hc l x hx).2.2.2.1.differentiableAt (by simp)
      have hdA : DifferentiableAt ℝ (fun y => PH dr Ar p q y k) x :=
        (hc k x hx).1.1.differentiableAt (by simp)
      have hdK : DifferentiableAt ℝ (fun y => PL dr Ar p q y k) x :=
        (hc k x hx).2.1.1.differentiableAt (by simp)
      have hdB : DifferentiableAt ℝ (fun y => DH dr Ar p q y l) x :=
        (hc l x hx).2.2.1.1.differentiableAt (by simp)
      have hLiteral : Rcomp l k x=CR dr Ar p q F x l k := by
        unfold composedPPRow
        rfl
      exact hLiteral.trans (composedPPRow_eq_balanced_at
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hL hg2
        q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x (hclosed x hx) (hKball hx)
        (hb x hx) (hs x hx) (hT x hx) F l k hdL hdA hdK hdB)
    · have hluActual (i : Fin 3) :
          directionalFDeriv (coordinateDirection i) (HU F) x=0 :=
        directional_eq_zero_off u K hK.isClosed hu0 _ x hx
      have hRowZero : Rrow l k x=0 := by
        simp only [Rrow,ActualPPLowerRemainder.actualPPBalancedRow,hluActual,
          half_pairing_zero_left,mul_zero,zero_add,sub_zero]
      exact (hRcompZero l k x hx).trans hRowZero.symm
  have hLfun (l k : Fin 3) : Lraw l k=Lrow l k := by
    funext x
    by_cases hx : x ∈ K
    · have hActual := actual_pp_leading_row_at
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
        dr Ar p q F x l k (hT x hx).self_of_nhds
      simpa only [Lraw,Lrow,C1,C2,dU,Q,U,u,mu,PCL,ContinuousLinearMap.comp_apply,
        ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hActual
    · simp only [Lraw,Lrow,h0 x hx,hu0 x hx,map_zero,ContinuousLinearMap.zero_apply,
        sphereSobolevDualPairing,inner_zero_left,inner_zero_right,
        zero_mul,mul_zero,sub_self]
  have hRow (l k : Fin 3) : (∫ x, Nrow l k x)=(∫ x,Lrow l k x)+(∫ x,Rrow l k x) := by
    have hh := ActualPPWeakLower.first_first_weak_row Q mu U (C1 l k) (C2 l k) K hK
      hmu hU h0 (hC1 l k) (hC2 l k) (coordinateDirection l) (coordinateDirection k)
    change (∫ x,Nrow l k x)=(∫ x,Lraw l k x)+(∫ x,Rcomp l k x) at hh
    rw [hLfun l k,hRfun l k] at hh
    exact hh
  have hLRint (l k : Fin 3) : Integrable (Lrow l k) := (hLfun l k) ▸ hLint l k
  have hRRint (l k : Fin 3) : Integrable (Rrow l k) := (hRfun l k) ▸ hRint l k
  have hLsum : Integrable (fun x => ∑ l : Fin 3, ∑ k : Fin 3, Lrow l k x) :=
    ActualHigherSIntegratedPairing.integrable_sum2 Lrow hLRint
  have hRsum : Integrable (fun x => ∑ l : Fin 3, ∑ k : Fin 3, Rrow l k x) :=
    ActualHigherSIntegratedPairing.integrable_sum2 Rrow hRRint
  have hNsum : Integrable (fun x => ∑ l : Fin 3, ∑ k : Fin 3, Nrow l k x) :=
    ActualHigherSIntegratedPairing.integrable_sum2 Nrow hNint
  have hLeadFun : (fun x => mu x*PP (u x) (Lead dr Ar p q F x))=
      (fun x => ∑ l : Fin 3, ∑ k : Fin 3, Lrow l k x) := by
    funext x
    have hSum0 := weighted_pair_fin3_sum2 (M := Half) (N := Neg)
    try simp only [clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hSum0
    have hSum := hSum0 QPP (u x) (fun l k => PCL l k x
      (directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k) u) x)) (mu x)
    simpa only [actualLeadingSignedSecondNeg,Lrow,PCL,u,
      ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hSum
  have hNormFun : (fun x => mu x*(‖PO dr Ar p q F x‖^2-‖DO dr Ar p q F x‖^2))=
      (fun x => ∑ l : Fin 3, ∑ k : Fin 3, Nrow l k x) := by
    funext x
    by_cases hx : x ∈ K
    · have hh := actual_first_first_norm_pointwise g L y0 Φ B ε C ρ H a w hData hg hcalc
        hF hO hD τ0 Room hreg data g2 dr Ar p q F x (hT x hx).self_of_nhds
      have hWeighted := congrArg (fun z : ℝ => mu x*z) hh
      simpa only [Nrow,Q,C1,C2,dU,U,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.neg_apply,Finset.mul_sum,
        ActualHigherSScalarCommutatorNativeForm.directional_halfInput,
        ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hWeighted
    · have hActualDuZero (i : Fin 3) :
          directionalFDeriv (coordinateDirection i) (UF F) x=0 := hdU0 i x hx
      have hOutputs := actual_pp_outputs_zero_of_derivatives
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x hActualDuZero
      have hNsumZero : (∑ l : Fin 3, ∑ k : Fin 3, Nrow l k x)=0 := by
        simp only [Nrow,hdU0 _ x hx,map_zero,ContinuousLinearMap.zero_apply,
          neg_zero,zero_add,mul_zero,Finset.sum_const_zero]
      simp only [hOutputs.1,hOutputs.2,hNsumZero,norm_zero,zero_pow,sub_self,mul_zero]
  have hWhole : (∫ x,mu x*(‖PO dr Ar p q F x‖^2-‖DO dr Ar p q F x‖^2))=
      (∫ x,mu x*PP (u x) (Lead dr Ar p q F x))+
      (∫ x,∑ l : Fin 3, ∑ k : Fin 3,Rrow l k x) := by
    rw [show (fun x => mu x*(‖PO dr Ar p q F x‖^2-‖DO dr Ar p q F x‖^2))=
      (fun x => ∑ l : Fin 3, ∑ k : Fin 3,Nrow l k x) from hNormFun]
    rw [ActualHigherSIntegratedPairing.integral_sum2 Nrow hNint]
    simp_rw [hRow]
    rw [hLeadFun,ActualHigherSIntegratedPairing.integral_sum2 Lrow hLRint,
      ActualHigherSIntegratedPairing.integral_sum2 Rrow hRRint]
    simp only [Finset.sum_add_distrib]
  have hLeading := hleading q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs
  have hEint : Integrable energy := hLeading.2.1
  have hEnergy0 (x : R3) : 0 ≤ energy x := by
    have hbpos := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
    exact mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q _ hbpos.le F x)
  have hEI0 : 0 ≤ ∫ x, energy x := integral_nonneg hEnergy0
  have hRpoint (l k : Fin 3) (x : R3) : |Rrow l k x| ≤ (CRow*eta)*energy x := by
    by_cases hx : x ∈ K
    · have hh := hpoint q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x (hclosed x hx)
        (hKball hx) (hb x hx) (hs x hx) F l k
      convert hh using 1 <;> dsimp [Rrow,energy,mu] <;> ring
    · have hzero : Rrow l k x=0 :=
        (congrFun (hRfun l k) x).symm.trans (hRcompZero l k x hx)
      exact abs_zero_le_nonneg_product (Rrow l k x) CRow eta (energy x)
        hzero hCRow heta (hEnergy0 x)
  have hRIntegral (l k : Fin 3) : |∫ x,Rrow l k x| ≤ CRow*eta*(∫ x,energy x) := by
    calc
      _ = ‖∫ x,Rrow l k x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x,(CRow*eta)*energy x := norm_integral_le_of_norm_le
        (hEint.const_mul (CRow*eta)) (Filter.Eventually.of_forall (fun x => by
          simpa only [Real.norm_eq_abs] using hRpoint l k x))
      _ = _ := integral_const_mul _ _
  have hRemBound : |∫ x,∑ l : Fin 3, ∑ k : Fin 3,Rrow l k x| ≤
      (9*(CRow+1))*eta*(∫ x,energy x) := by
    rw [ActualHigherSIntegratedPairing.integral_sum2 Rrow hRRint]
    calc
      _ = ‖∑ l : Fin 3, ∑ k : Fin 3,∫ x,Rrow l k x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑ l : Fin 3, ‖∑ k : Fin 3,∫ x,Rrow l k x‖ := norm_sum_le _ _
      _ ≤ ∑ l : Fin 3, ∑ k : Fin 3,‖∫ x,Rrow l k x‖ := Finset.sum_le_sum (fun l _ => norm_sum_le _ _)
      _ = ∑ l : Fin 3, ∑ k : Fin 3,|∫ x,Rrow l k x| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑ _l : Fin 3, ∑ _k : Fin 3,CRow*eta*(∫ x,energy x) :=
        Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun k _ => hRIntegral l k))
      _ = 9*CRow*eta*(∫ x,energy x) := by simp only [Fin.sum_univ_three]; ring
      _ ≤ _ := by nlinarith only [mul_nonneg heta hEI0]
  have hPHs (i : Fin 3) : ContDiff ℝ ∞ (fun x => PH dr Ar p q x i (dU i x)) :=
    contDiff_supported_operator_apply (dU i) _ K hK.isClosed (hdUs i) (hdU0 i)
      (fun x hx => (hc i x hx).1.1)
  have hDHs (i : Fin 3) : ContDiff ℝ ∞ (fun x => DH dr Ar p q x i (dU i x)) :=
    contDiff_supported_operator_apply (dU i) _ K hK.isClosed (hdUs i) (hdU0 i)
      (fun x hx => (hc i x hx).2.2.1.1)
  have hPOs : ContDiff ℝ ∞ (PO dr Ar p q F) :=
    (KL).contDiff.comp (ContDiff.sum (fun i _ => hPHs i))
  have hDOs : ContDiff ℝ ∞ (DO dr Ar p q F) :=
    (KL).contDiff.comp (ContDiff.sum (fun i _ => hDHs i))
  have hOutputsOffK (x : R3) (hx : x ∉ K) :
      PO dr Ar p q F x=0 ∧ DO dr Ar p q F x=0 := by
    have hActualDuZero (i : Fin 3) :
        directionalFDeriv (coordinateDirection i) (UF F) x=0 := hdU0 i x hx
    exact actual_pp_outputs_zero_of_derivatives
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x hActualDuZero
  have hPOc : HasCompactSupport (PO dr Ar p q F) :=
    HasCompactSupport.intro hK (fun x hx => (hOutputsOffK x hx).1)
  have hDOc : HasCompactSupport (DO dr Ar p q F) :=
    HasCompactSupport.intro hK (fun x hx => (hOutputsOffK x hx).2)
  have hPOint := integrable_weighted_norm_sq_of_continuous_compact mu hmu.continuous
    (PO dr Ar p q F) hPOs.continuous hPOc
  have hDOint := integrable_weighted_norm_sq_of_continuous_compact mu hmu.continuous
    (DO dr Ar p q F) hDOs.continuous hDOc
  exact ⟨hPOint,hDOint,hLeading.1,hRsum,hEint,hRRint,hWhole,hRemBound⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPPLowerRemainder
