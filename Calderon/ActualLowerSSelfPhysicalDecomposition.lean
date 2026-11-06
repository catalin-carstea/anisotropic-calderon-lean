import Calderon.ActualPPLowerRemainder
import Calderon.ActualHigherSZeroWordLiteralDictionary
import Calderon.ActualHigherSQuadraticZeroNegativeGraphs
import Calderon.ActualLowerSSelfFormation
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerSSelfPhysicalDecomposition
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
 ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
 ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth FixedParameterProfilePullback
 PrincipalCommutator SectionFiveErrorForms

/-- Finite-sum graph transport through an injective inclusion, then a fixed output map. -/
private lemma map_sum_add_add_of_graphs
    {V N X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (J : V →L[ℝ] N) (K : V →L[ℝ] X) (hJ : Function.Injective J)
    (v z l : V) (u : Fin 3 → V) (a : Fin 3 → N) (c : N)
    (hcoef : J v = (∑ k : Fin 3, a k)+c)
    (hfirst : ∀ k : Fin 3, a k = J (u k)) (hzero : c = J z+J l) :
    K v = K (∑ k : Fin 3, u k)+K z+K l := by
  have hv : v = (∑ k : Fin 3, u k)+z+l := by
    apply hJ
    calc
      J v = (∑ k : Fin 3, a k)+c := hcoef
      _ = (∑ k : Fin 3, J (u k))+(J z+J l) :=
        congrArg₂ (fun a b : N => a+b)
          (Finset.sum_congr rfl (fun k _ => hfirst k)) hzero
      _ = J ((∑ k : Fin 3, u k)+z+l) := by
        simp only [map_add,map_sum,add_assoc]
  calc
    K v = K ((∑ k : Fin 3, u k)+z+l) := congrArg K hv
    _ = K (∑ k : Fin 3, u k)+K z+K l := by rw [map_add,map_add]

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
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
local notation "SF" => ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "TF" => ActualHigherSAdjointFormation.higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PF" => ActualPPLowerRemainder.actualPPFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PR" => ActualPPLowerRemainder.actualPPReverseFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Z2" => ActualHigherSQuadraticZeroQuartic.actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => ActualHigherSQuadraticZeroQuartic.actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z1" => ActualHigherSLinearZero.linearZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => ActualHigherSLinearZero.linearAdjointZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "U" => ActualHigherSFormation.higherSInput hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
/-- Exact statement: no residual definitions or extra callback. -/
def SamePacketPhysicalFirstZeroSplit (g2 : MatrixField) : Prop :=
  ∃ etaSplit : ℝ, 0 < etaSplit ∧ etaSplit ≤ data.eta0 ∧
    ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaSplit →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    ∀ x : R3,
      SF dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x =
        PF g2 dr Ar p q F x + KL (Z2 g2 dr Ar p q F x) + KL (Z1 g2 dr Ar p q x (U F x)) ∧
      TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x =
        PR g2 dr Ar p q F x + KL (T2 g2 dr Ar p q F x) + KL (T1 g2 dr Ar p q x (U F x))

local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "PH" => ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DH" => ActualPPLowerRemainder.actualPPReverseFirstHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CL" => ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DL" => ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BC" => ActualHigherSCoefficientExtraction.higherSFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "SH" => ActualHigherSFormation.nativeHigherSHalf
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "TH" => ActualHigherSAdjointFormation.higherSAdjointHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CT" => ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevHalfToSphereL2L
  ActualHigherSFormation.higherSInput ActualHigherSFormation.nativeHigherSHalf
  ActualHigherSAdjointFormation.higherSAdjointHalf
  ActualHigherSQuadraticZeroQuartic.actualZ2Half ActualHigherSQuadraticZeroQuartic.actualT2Half
  ActualHigherSLinearZero.linearZeroHigh ActualHigherSLinearZero.linearAdjointZeroHigh
  ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient

/-- Complete forward physical point construction from the same retained room and evaluated zero graph. -/
private theorem physical_forward_at
    (dA : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dA)
    (hJac : ∀ z ∈ commonRoom y0 ρ dA, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hAdj : ActualHigherSAdjointFormation.HigherSAdjointContract
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dA)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dA)
    (x : R3) (hTA : (Tq dr Ar p q) x ∈ ParamRoom dA)
    (hTD : (Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (hCZ : CZ g2 dr Ar p q x (U F x) =
      JL (Z2 g2 dr Ar p q F x)+JL (Z1 g2 dr Ar p q x (U F x))) :
    SF dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x =
      PF g2 dr Ar p q F x+KL (Z2 g2 dr Ar p q F x)+KL (Z1 g2 dr Ar p q x (U F x)) := by
  let du : Fin 3 → Hi := fun k => directionalFDeriv (coordinateDirection k) (U F) x
  obtain ⟨hout,_hAH,_hAO,_hsAH,_hcAH,_hcAO,_hadj⟩ :=
    hAdj g2 hg2 dr Ar p hdr hAr q hq F hTF
  have hFirst (k : Fin 3) := ActualPPLowerRemainder.actual_first_high_low_graphs
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
    dr Ar p q x hTD k (du k)
  have hForward (k : Fin 3) :
      BC g2 dr Ar p q x k (IH (du k)) = JL (PH g2 dr Ar p q x k (du k)) := by
    have hc := ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient_eq_original_at_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs dA Cm hJac g2 dr Ar p hdr hAr q hq x hTA k
    exact (congrArg (fun A : Half →L[ℝ] Neg => A (IH (du k))) hc.symm).trans (hFirst k).1.symm
  have hFcoef := ActualHigherSCoefficientExtraction.actual_higherS_coordinate_coefficient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs dA Cm hJac g2 dr Ar p hdr hAr q hq F hTF x
  have hSF : JL (SH dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x) =
      (∑ k : Fin 3, BC g2 dr Ar p q x k (IH (du k)))+CZ g2 dr Ar p q x (U F x) :=
    (hout.2.2.2.1 x).trans hFcoef
  have hJ : Function.Injective JL :=
    sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  change KL (SH dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x) =
    KL (∑ k : Fin 3, PH g2 dr Ar p q x k (du k))+
      KL (Z2 g2 dr Ar p q F x)+KL (Z1 g2 dr Ar p q x (U F x))
  exact map_sum_add_add_of_graphs JL KL hJ
    (SH dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x)
    (Z2 g2 dr Ar p q F x) (Z1 g2 dr Ar p q x (U F x))
    (fun k => PH g2 dr Ar p q x k (du k))
    (fun k => BC g2 dr Ar p q x k (IH (du k))) (CZ g2 dr Ar p q x (U F x))
    hSF hForward hCZ

/-- Complete reverse physical point construction with the original negative radius-squared factor. -/
private theorem physical_reverse_at
    (dA : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dA)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dA)
    (x : R3) (hTD : (Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (hCT : CT g2 dr Ar p q x (U F x) =
      JL (T2 g2 dr Ar p q F x)+JL (T1 g2 dr Ar p q x (U F x))) :
    TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x =
      PR g2 dr Ar p q F x+KL (T2 g2 dr Ar p q F x)+KL (T1 g2 dr Ar p q x (U F x)) := by
  let du : Fin 3 → Hi := fun k => directionalFDeriv (coordinateDirection k) (U F) x
  have hFirst (k : Fin 3) := ActualPPLowerRemainder.actual_first_high_low_graphs
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
    dr Ar p q x hTD k (du k)
  have hReverse (k : Fin 3) :
      ((-(referenceRadius dr Ar p L x)^2) •
        ActualHigherSLeadingBracketGain.orderedReverseFirstCoordinateFactorLow
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 k ((Tq dr Ar p q) x))
          (IH (du k)) = JL (DH g2 dr Ar p q x k (du k)) := by
    have hc := ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient_eq_contracted
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x k
    exact (congrArg (fun A : Half →L[ℝ] Neg => A (IH (du k))) hc.symm).trans (hFirst k).2.symm
  have hTcoef : JL (TH hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x) =
      (∑ k : Fin 3,
        ((-(referenceRadius dr Ar p L x)^2) •
          ActualHigherSLeadingBracketGain.orderedReverseFirstCoordinateFactorLow
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
              g2 k ((Tq dr Ar p q) x)) (IH (du k)))+CT g2 dr Ar p q x (U F x) :=
    ActualHigherSAdjointLeadingCoordinate.actual_higherS_adjoint_coordinate_coefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs dA Cm g2 dr Ar p hdr hAr q F hTF x
  have hJ : Function.Injective JL :=
    sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  change KL (TH hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x) =
    KL (∑ k : Fin 3, DH g2 dr Ar p q x k (du k))+
      KL (T2 g2 dr Ar p q F x)+KL (T1 g2 dr Ar p q x (U F x))
  exact map_sum_add_add_of_graphs JL KL hJ
    (TH hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x)
    (T2 g2 dr Ar p q F x) (T1 g2 dr Ar p q x (U F x))
    (fun k => DH g2 dr Ar p q x k (du k))
    (fun k => ((-(referenceRadius dr Ar p L x)^2) •
      ActualHigherSLeadingBracketGain.orderedReverseFirstCoordinateFactorLow
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          g2 k ((Tq dr Ar p q) x)) (IH (du k)))
    (CT g2 dr Ar p q x (U F x)) hTcoef hReverse hCT

/-- Complete off-input-support physical construction, with both actual quadratic graphs. -/
private theorem physical_off_support_at
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (hxF : x ∉ tsupport F.val)
    (hGZ : JL (Z2 g2 dr Ar p q F x) =
      ActualHigherSQuadraticZeroWords.quadraticZeroNegative
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x (U F x))
    (hGT : JL (T2 g2 dr Ar p q F x) =
      ActualHigherSQuadraticZeroWords.quadraticZeroReverseNegative
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x (U F x)) :
    SF dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x =
      PF g2 dr Ar p q F x+KL (Z2 g2 dr Ar p q F x)+KL (Z1 g2 dr Ar p q x (U F x)) ∧
    TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x =
      PR g2 dr Ar p q F x+KL (T2 g2 dr Ar p q F x)+KL (T1 g2 dr Ar p q x (U F x)) := by
  have hJ : Function.Injective JL :=
    sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hU0 := ActualHigherSFormation.higherSInput_eq_zero
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q F x hxF
  have hUev := ActualHigherSFormation.higherSInput_eventually_zero
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q F x hxF
  have hdU : fderiv ℝ (U F) x=0 := hUev.fderiv_eq.trans (fderiv_const_apply _)
  have hZ0 : Z2 g2 dr Ar p q F x=0 := by
    apply hJ
    simpa only [hU0,map_zero] using hGZ
  have hT0 : T2 g2 dr Ar p q F x=0 := by
    apply hJ
    simpa only [hU0,map_zero] using hGT
  have hSF0 := ActualHigherSFormation.nativeHigherSHalf_eq_zero
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x hxF
  have hTF0 := ActualHigherSAdjointFormation.higherSAdjointHalf_eq_zero_off_support
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x hxF
  constructor
  · change KL (SH dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x)=_
    simp only [hSF0,ActualPPLowerRemainder.actualPPFirstOut,directionalFDeriv,hdU,_root_.zero_apply,
      hU0,hZ0,map_zero,Finset.sum_const_zero,add_zero]
  · change KL (TH hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x)=_
    simp only [hTF0,ActualPPLowerRemainder.actualPPReverseFirstOut,directionalFDeriv,hdU,_root_.zero_apply,
      hU0,hT0,map_zero,Finset.sum_const_zero,add_zero]

set_option diagnostics true in
/-- Literal physical decomposition, with every threshold derived before profiles. -/
theorem exists_same_packet_physical_first_zero_split (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    SamePacketPhysicalFirstZeroSplit g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 := by
  obtain ⟨dA,hdA,_hdA0,_hdArho,Cm,hJac,hAdj⟩ :=
    ActualHigherSAdjointFormation.exists_retained_higherS_adjoint
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨etaG,hetaG,hetaG0,hGraphs⟩ :=
    ActualHigherSQuadraticZeroNegativeGraphs.exists_uniform_actualZ2T2_negative_graphs
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel g2
  obtain ⟨etaW,hetaW,hetaW0,hWords⟩ :=
    ActualHigherSZeroWordDictionary.exists_same_packet_zero_word_dictionary_literal
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel g2 hg2
  let d : ℝ := min dA data.δ
  have hd : 0 < d := lt_min hdA data.δ_pos
  obtain ⟨eps,heps,_heps1,hGuard⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ d hd (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaSplit := min data.eta0 (min etaG (min etaW eps))
  refine ⟨etaSplit,lt_min data.eta0_pos (lt_min hetaG (lt_min hetaW heps)),min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaSplit K hK hKball F hsupp hb hs
  have heG : eta ≤ etaG := hetaSplit.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heW : eta ≤ etaW := hetaSplit.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hepsEta : eta ≤ eps := hetaSplit.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hT (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom d := by
    have hguard := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta hepsEta x
      (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx)
    exact (higherSParam_eventually_mem y0 ρ d L dr Ar q p hdr hAr x hguard).self_of_nhds
  have hTA (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom dA :=
    ⟨commonRoom_mono y0 ρ (min_le_left _ _) (hT x hx).1,(hT x hx).2⟩
  have hTD (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom data.δ :=
    ⟨commonRoom_mono y0 ρ (min_le_right _ _) (hT x hx).1,(hT x hx).2⟩
  have hTF : ∀ x ∈ tsupport F.val,(Tq dr Ar p q) x ∈ ParamRoom dA :=
    fun x hx => hTA x (hsupp hx)
  have hG := hGraphs q hq dr hdr hdr1 Ar hAr p hp eta heta heG K hK hKball F hsupp hb hs
  intro x
  by_cases hx : x ∈ K
  · have hW := hWords q hq dr hdr hdr1 Ar hAr p hp eta heta heW x
      (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx)
    have hCZ : CZ g2 dr Ar p q x (U F x)=
        JL (Z2 g2 dr Ar p q F x)+JL (Z1 g2 dr Ar p q x (U F x)) := by
      have h := congrArg (fun A : Hi →L[ℝ] Neg => A (U F x)) hW.1
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply] at h
      exact h.trans (congrArg (fun n : Neg => n+JL (Z1 g2 dr Ar p q x (U F x))) (hG x).1.symm)
    have hCT : CT g2 dr Ar p q x (U F x)=
        JL (T2 g2 dr Ar p q F x)+JL (T1 g2 dr Ar p q x (U F x)) := by
      have h := congrArg (fun A : Hi →L[ℝ] Neg => A (U F x)) hW.2
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply] at h
      exact h.trans (congrArg (fun n : Neg => n+JL (T1 g2 dr Ar p q x (U F x))) (hG x).2.symm)
    constructor
    · exact physical_forward_at
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        dA Cm hJac hAdj g2 hg2 dr Ar p hdr hAr q hq F hTF x (hTA x hx) (hTD x hx) hCZ
    · exact physical_reverse_at
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        dA Cm g2 dr Ar p hdr hAr q F hTF x (hTD x hx) hCT
  · have hxF : x ∉ tsupport F.val := fun h => hx (hsupp h)
    exact physical_off_support_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 dr Ar p hdr hAr q F x hxF (hG x).1 (hG x).2

/-- Exhaustive algebra after the two actual field equalities, with all six categories. -/
lemma signed_three_block_expansion {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a b c d e f : V) :
    ‖a+b+c‖^2-‖d+e+f‖^2 =
      (‖a‖^2-‖d‖^2)+2*(⟪a,b⟫_ℝ-⟪d,e⟫_ℝ)+(‖b‖^2-‖e‖^2)+
      2*(⟪a,c⟫_ℝ-⟪d,f⟫_ℝ)+2*(⟪b,c⟫_ℝ-⟪e,f⟫_ℝ)+(‖c‖^2-‖f‖^2) := by
  simp only [norm_add_sq_real,inner_add_left]
  ring
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerSSelfPhysicalDecomposition
