import Calderon.ActualFullECanonicalEndpoints
import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.NativeHalfCoefficientCommutation

/-! The HH band. The final actual producer uses the exact shared Pi/Jacobi germs of the
ordinary endpoints.
No high norm is used to infer a low endpoint. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualJacobiAngularGainedRows
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualCanonicalAngularGainedBracket
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

section Algebra
variable {E F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- Exact three-term [P a,A Q] cancellation at the required two endpoint levels. -/
private lemma coefficientAngularBracket_graph
    (I : E →L[ℝ] F) (J : F →L[ℝ] N)
    (PL : F →L[ℝ] F) (PN : N →L[ℝ] N) (QH : E →L[ℝ] E) (QL : F →L[ℝ] F)
    (aH AH : E →L[ℝ] F) (aL AL : F →L[ℝ] N)
    (C : E →L[ℝ] F) (U : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hP : ∀ v, J (PL v) = PN (J v))
    (hC : ∀ u, J (C u) = aL (AH u)-AL (aH u))
    (hU : ∀ u, I (U u) = aH (QH u)-QL (aH u))
    (hA : ∀ u, J (AH u) = AL (I u))
    (hV : ∀ v, J (V v) = PN (AL v)-AL (PL v))
    (hComm : ∀ v, PL (QL v) = QL (PL v)) (u : E) :
    J (((PL.comp (C.comp QH) + PL.comp (AH.comp U)) + V.comp (QL.comp aH)) u) =
      PN (aL (AH (QH u))) - AL (QL (PL (aH u))) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add,
    hP,hC,hA,hU,hV,map_sub,hComm]
  abel

/-- The finite index swap needed to turn all ordered pairs into the full bracket. -/
private lemma finiteBracket_graph
    (J : F →L[ℝ] N) (aL : Fin 3 → F →L[ℝ] N) (AH : Fin 3 → E →L[ℝ] F)
    (AL : Fin 3 → F →L[ℝ] N) (aH : Fin 3 → E →L[ℝ] F)
    (G : Fin 3 → Fin 3 → E →L[ℝ] F)
    (hG : ∀ m n u, J (G m n u) = aL m (AH n u)-AL n (aH m u)) (u : E) :
    J ((∑ m : Fin 3, ∑ n : Fin 3, G m n) u) =
      (∑ m : Fin 3, aL m) ((∑ n : Fin 3, AH n) u) -
        (∑ n : Fin 3, AL n) ((∑ m : Fin 3, aH m) u) := by
  have hSum : (∑ m : Fin 3, ∑ n : Fin 3, J (G m n u)) =
      ∑ m : Fin 3, ∑ n : Fin 3, (aL m (AH n u)-AL n (aH m u)) :=
    Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hG m n u))
  have hSwap : (∑ m : Fin 3, ∑ n : Fin 3, aL m (AH n u)) =
      ∑ n : Fin 3, ∑ m : Fin 3, aL m (AH n u) := Finset.sum_comm
  simp only [ContinuousLinearMap.sum_apply,map_sum,Finset.sum_sub_distrib] at hSum ⊢
  exact hSum.trans (congrArg (fun z : N => z-(∑ m : Fin 3, ∑ n : Fin 3, AL n (aH m u))) hSwap)
end Algebra

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "Guard" => finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData

/-- Exact current native Jacobi jets from the retained support data of the ordinary endpoints. -/
def jacobiJets (δ0 : ℝ) (W : CoeffRoom δ0) (i m : Fin 3) (p : Pphys) : SmoothCoefficientJets 3 :=
  commonSupportCoefficientFamily 3 (W.jacobiScalar i m) (W.jacobiSmooth i m)
    (W.jacobiSupport i m) (W.jacobiCompact i m) (W.jacobiZero i m) p
local notation "Q" => jacobiJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def jacobiAngularOperatorHigh (i : Fin 3) (p : Pphys) : Hi →L[ℝ] Half :=
  ∑ m : Fin 3, (raisingHigh hF hO hD m).comp (NH (NJ3 i m p))
def jacobiAngularOperatorLow (i : Fin 3) (p : Pphys) : Half →L[ℝ] Neg :=
  ∑ m : Fin 3, (raisingLow hF hO hD m).comp (NL (NJ2 i m p))
def jacobiAngularReverseHigh (i : Fin 3) (p : Pphys) : Hi →L[ℝ] Half :=
  ∑ m : Fin 3, (NL (NJ2 i m p)).comp (loweringHigh hF hO hD m)
def jacobiAngularReverseLow (i : Fin 3) (p : Pphys) : Half →L[ℝ] Neg :=
  ∑ m : Fin 3, (NN (NJ2 i m p)).comp (loweringLow hF hO hD m)

/-- The concrete three-term high map for each H1/H1 ordered summand. -/
def jacobiAngularPairHigh (δ0 : ℝ) (W : CoeffRoom δ0) (i j m n : Fin 3) (p : Pphys) : Hi →L[ℝ] Half :=
  ((NL (smoothMultiplierLowerJets (Q δ0 W i m p))).comp
    ((gainedAtOrder hF hO hD (3/2 : ℝ) m n).comp (NH (Q δ0 W j n p))) +
  (NL (smoothMultiplierLowerJets (Q δ0 W i m p))).comp
    ((raisingHigh hF hO hD n).comp
      (loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg (Q δ0 W j n p) m p.1 p.2.1))) +
  (raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData (Q δ0 W i m p) n p.1 p.2.1).comp
    ((NL (smoothMultiplierLowerJets (Q δ0 W j n p))).comp (loweringHigh hF hO hD m))

/-- Full H1/H1 high gain, retaining every ordered Jacobi/angular word. -/
def jacobiAngularHigh (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (p : Pphys) : Hi →L[ℝ] Half :=
  ∑ m : Fin 3, ∑ n : Fin 3,
    jacobiAngularPairHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W i j m n p

local notation "PairHigh" => jacobiAngularPairHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HeadHigh" => jacobiAngularOperatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HeadLow" => jacobiAngularOperatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HeadReverseHigh" => jacobiAngularReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HeadReverseLow" => jacobiAngularReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HH" => jacobiAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL loweringHigh loweringLow raisingHigh raisingLow gainedAtOrder
  jacobiAngularPairHigh jacobiAngularHigh jacobiAngularOperatorHigh jacobiAngularOperatorLow jacobiAngularReverseHigh jacobiAngularReverseLow

@[instance_reducible] private def hhOriginalValueNormed : NormedAddCommGroup (Hi) := inferInstance
@[instance_reducible] private def hhOriginalValueModule : NormedSpace ℝ (Hi) := inferInstance
@[instance_reducible] private def hhOriginalMapNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def hhOriginalMapModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def hhValueNormed : NormedAddCommGroup (Hi) := hhOriginalValueNormed
attribute [local instance] hhValueNormed
@[instance_reducible] private def hhValueModule : NormedSpace ℝ (Hi) := hhOriginalValueModule
attribute [local instance] hhValueModule
@[instance_reducible] private def hhMapNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := hhOriginalMapNormed
attribute [local instance] hhMapNormed
@[instance_reducible] private def hhMapModule : NormedSpace ℝ (Hi →L[ℝ] Half) := hhOriginalMapModule
attribute [local instance] hhMapModule
private theorem hhValueNormed_canonical : hhValueNormed = hhOriginalValueNormed := rfl
private theorem hhValueModule_canonical : hhValueModule = hhOriginalValueModule := rfl
private theorem hhMapNormed_canonical : hhMapNormed = hhOriginalMapNormed := rfl
private theorem hhMapModule_canonical : hhMapModule = hhOriginalMapModule := rfl

/-- Actual graph of one ordered H1/H1 summand, with the current coefficient frozen. -/
private theorem jacobiAngularPairHigh_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam : ℝ) (i j m n : Fin 3)
    (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ0) (hG0 : Guard lam Lam (p.1,(p.2.1,0))) (u : Hi) :
    JL (PairHigh δ0 W i j m n p u) =
      NN (NJ2 i m p) (loweringLow hF hO hD m (raisingHigh hF hO hD n (NH (NJ3 j n p) u))) -
        raisingLow hF hO hD n (NL (NJ2 j n p) (NL (NJ2 i m p) (loweringHigh hF hO hD m u))) := by
  have hPi := (W.jacobiGerm i m p hp).self_of_nhds
  have hQj := (W.jacobiGerm j n p hp).self_of_nhds
  have hU := loweringPiGain_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel
    lam Lam (Q δ0 W j n p) m p.1 hp.1 p.2.1 hp.2.1 hG0
  have hV := raisingPiGain_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hKernel
    lam Lam (Q δ0 W i m p) n p.1 hp.1 p.2.1 hp.2.1 hG0
  let I0 : Hi →L[ℝ] Half := IH
  let J0 : Half →L[ℝ] Neg := JL
  let PL : Half →L[ℝ] Half := NL (smoothMultiplierLowerJets (Q δ0 W i m p))
  let PN : Neg →L[ℝ] Neg := NN (smoothMultiplierLowerJets (Q δ0 W i m p))
  let QH : Hi →L[ℝ] Hi := NH (Q δ0 W j n p)
  let QL : Half →L[ℝ] Half := NL (smoothMultiplierLowerJets (Q δ0 W j n p))
  let aH : Hi →L[ℝ] Half := loweringHigh hF hO hD m
  let AH : Hi →L[ℝ] Half := raisingHigh hF hO hD n
  let aL : Half →L[ℝ] Neg := loweringLow hF hO hD m
  let AL : Half →L[ℝ] Neg := raisingLow hF hO hD n
  let Cg : Hi →L[ℝ] Half := gainedAtOrder hF hO hD (3/2 : ℝ) m n
  let U : Hi →L[ℝ] Hi := loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
    (Q δ0 W j n p) m p.1 p.2.1
  let V : Half →L[ℝ] Half := raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    (Q δ0 W i m p) n p.1 p.2.1
  let K : Hi →L[ℝ] Half :=
    (PL.comp (Cg.comp QH)+PL.comp (AH.comp U))+V.comp (QL.comp aH)
  have hMap : PairHigh δ0 W i j m n p = K := by
    unfold jacobiAngularPairHigh
    rfl
  have hP : ∀ v : Half, J0 (PL v)=PN (J0 v) :=
    v017_native_half_negative hcalc hF hO hD τ0 (smoothMultiplierLowerJets (Q δ0 W i m p))
  have hC : ∀ v : Hi, J0 (Cg v)=aL (AH v)-AL (aH v) := gainedHigh_graph hF hO hD m n
  have hUc : ∀ v : Hi, I0 (U v)=aH (QH v)-QL (aH v) := hU
  have hA : ∀ v : Hi, J0 (AH v)=AL (I0 v) := v017_inclusion_raisingHigh hF hO hD n
  have hVc : ∀ v : Half, J0 (V v)=PN (AL v)-AL (PL v) := hV
  have hComm : ∀ v : Half, PL (QL v)=QL (PL v) :=
    nativeHalfCoefficientMulL_lowerJets_comm_apply hcalc hF hO hD τ0 (Q δ0 W i m p) (Q δ0 W j n p)
  have hNative : J0 (K u)=PN (aL (AH (QH u)))-AL (QL (PL (aH u))) := by
    change J0 (((PL.comp (Cg.comp QH)+PL.comp (AH.comp U))+V.comp (QL.comp aH)) u)=_
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add,
      hP,hC,hA,hUc,hVc,map_sub,hComm]
    abel
  have hPiL : PL = NL (NJ2 i m p) := hPi.2.1
  have hPiN : PN = NN (NJ2 i m p) := hPi.2.2
  have hQjH : QH = NH (NJ3 j n p) := hQj.1
  have hQjL : QL = NL (NJ2 j n p) := hQj.2.1
  have hRhs : PN (aL (AH (QH u)))-AL (QL (PL (aH u))) =
      NN (NJ2 i m p) (loweringLow hF hO hD m (raisingHigh hF hO hD n (NH (NJ3 j n p) u))) -
        raisingLow hF hO hD n (NL (NJ2 j n p) (NL (NJ2 i m p) (loweringHigh hF hO hD m u))) := by
    rw [hPiN,hQjH,hQjL,hPiL]
  exact (congrArg (fun A : Hi →L[ℝ] Half => J0 (A u)) hMap).trans (hNative.trans hRhs)

/-- The full actual H1/H1 negative ordered graph, without a gain callback. -/
theorem jacobiAngularHigh_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam : ℝ) (i j : Fin 3)
    (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ0) (hG0 : Guard lam Lam (p.1,(p.2.1,0))) (u : Hi) :
    JL (HH δ0 W i j p u) =
      HeadReverseLow i p (HeadHigh j p u) - HeadLow j p (HeadReverseHigh i p u) := by
  have hPair := jacobiAngularPairHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg hKernel δ0 W lam Lam i j
  have hSum := finiteBracket_graph JL
    (fun m => (NN (NJ2 i m p)).comp (loweringLow hF hO hD m))
    (fun n => (raisingHigh hF hO hD n).comp (NH (NJ3 j n p)))
    (fun n => (raisingLow hF hO hD n).comp (NL (NJ2 j n p)))
    (fun m => (NL (NJ2 i m p)).comp (loweringHigh hF hO hD m))
    (fun m n => PairHigh δ0 W i j m n p)
    (fun m n u => hPair m n p hp hG0 u) u
  simpa only [jacobiAngularHigh,jacobiAngularOperatorHigh,jacobiAngularOperatorLow,
    jacobiAngularReverseHigh,jacobiAngularReverseLow] using hSum


private lemma jacobi_high_half (δ0 : ℝ) (W : CoeffRoom δ0) (i m : Fin 3)
    (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ0) (u : Hi) :
    IH (NH (NJ3 i m p) u) = NL (NJ2 i m p) (IH u) := by
  have hId := (W.jacobiGerm i m p hp).self_of_nhds
  have h := v017_native_high_half hcalc hF hO hD τ0 (Q δ0 W i m p) u
  simpa only [jacobiJets,hId.1,hId.2.1] using h

private lemma jacobi_half_negative (i m : Fin 3) (p : Pphys) (v : Half) :
    JL (NL (NJ2 i m p) v) = NN (NJ2 i m p) (JL v) :=
  v017_native_half_negative hcalc hF hO hD τ0 (NJ2 i m p) v

/-- Separate actual endpoint compatibility for H1 and its genuine ordered reverse. -/
theorem jacobiAngularOperator_endpoint_compatibility
    (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3) (p : Pphys)
    (hp : p ∈ commonRoom y0 ρ δ0) (u : Hi) :
    JL (HeadHigh i p u) = HeadLow i p (IH u) ∧
    JL (HeadReverseHigh i p u) = HeadReverseLow i p (IH u) := by
  refine ⟨?_,?_⟩
  · simp only [jacobiAngularOperatorHigh,jacobiAngularOperatorLow,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply,map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    exact (v017_inclusion_raisingHigh hF hO hD m (NH (NJ3 i m p) u)).trans
      (congrArg (raisingLow hF hO hD m)
        (jacobi_high_half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W i m p hp u))
  · simp only [jacobiAngularReverseHigh,jacobiAngularReverseLow,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply,map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    exact (jacobi_half_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i m p
      (loweringHigh hF hO hD m u)).trans
        (congrArg (NN (NJ2 i m p)) (v017_inclusion_loweringHigh hF hO hD m u))

/-- Genuine actual H1 low pivot, with the native Jacobi scalar in reverse order. -/
theorem jacobiAngularOperator_low_pivot (i : Fin 3) (p : Pphys) (x y : Half) :
    PP x (HeadLow i p y) = PP y (HeadReverseLow i p x) := by
  have hTerm (m : Fin 3) : PP x (raisingLow hF hO hD m (NL (NJ2 i m p) y)) =
      PP y (NN (NJ2 i m p) (loweringLow hF hO hD m x)) :=
    (v017_pairing_loweringLow_raisingLow hF hO hD m (NL (NJ2 i m p) y) x).symm.trans
      (v017_native_pairing hcalc hF hO hD τ0 (NJ2 i m p) y (loweringLow hF hO hD m x))
  change ⟪x,HeadLow i p y⟫_ℝ = ⟪y,HeadReverseLow i p x⟫_ℝ
  simp only [jacobiAngularOperatorLow,jacobiAngularReverseLow,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,inner_sum]
  exact Finset.sum_congr rfl (fun m _ => hTerm m)

/-- The actual paired high adjunction for the complete H1/H1 gained map. -/
theorem jacobiAngularHigh_swapped_pairing
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam : ℝ) (i j : Fin 3)
    (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ0) (hG0 : Guard lam Lam (p.1,(p.2.1,0))) (u v : Hi) :
    PP (IH v) (JL (HH δ0 W i j p u)) = PP (IH u) (JL (HH δ0 W j i p v)) := by
  have hc := jacobiAngularHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg hKernel δ0 W lam Lam i j p hp hG0 u
  have hd := jacobiAngularHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg hKernel δ0 W lam Lam j i p hp hG0 v
  have hForward (k : Fin 3) (z : Hi) (wTest : Half) :
      PP (IH z) (HeadLow k p wTest) = PP wTest (JL (HeadReverseHigh k p z)) :=
    (jacobiAngularOperator_low_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      k p (IH z) wTest).trans
      (congrArg (PP wTest) (jacobiAngularOperator_endpoint_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W k p hp z).2.symm)
  have hReverse (k : Fin 3) (z : Hi) (wTest : Half) :
      PP (IH z) (HeadReverseLow k p wTest) = PP wTest (JL (HeadHigh k p z)) :=
    (jacobiAngularOperator_low_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      k p wTest (IH z)).symm.trans
      (congrArg (PP wTest) (jacobiAngularOperator_endpoint_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W k p hp z).1.symm)
  have h1 : PP (IH v) (HeadReverseLow i p (HeadHigh j p u)) =
      PP (IH u) (HeadReverseLow j p (HeadHigh i p v)) :=
    (hReverse i v (HeadHigh j p u)).trans
      ((v016_pairing_inclusion_symm (HeadHigh j p u) (HeadHigh i p v)).trans
        (hReverse j u (HeadHigh i p v)).symm)
  have h2 : PP (IH v) (HeadLow j p (HeadReverseHigh i p u)) =
      PP (IH u) (HeadLow i p (HeadReverseHigh j p v)) :=
    (hForward j v (HeadReverseHigh i p u)).trans
      ((v016_pairing_inclusion_symm (HeadReverseHigh i p u) (HeadReverseHigh j p v)).trans
        (hForward i u (HeadReverseHigh j p v)).symm)
  have hLeft := (congrArg (fun z : Neg => PP (IH v) z) hc).trans (v016_pairing_sub_right (IH v) _ _)
  have hRight := (congrArg (fun z : Neg => PP (IH u) z) hd).trans (v016_pairing_sub_right (IH u) _ _)
  exact hLeft.trans ((congrArg₂ (fun x y : ℝ => x-y) h1 h2).trans hRight.symm)


private lemma jacobiNative_contDiff (δ0 : ℝ) (W : CoeffRoom δ0) (i m : Fin 3) :
    ContDiff ℝ ∞ (fun p => NH (Q δ0 W i m p)) ∧
    ContDiff ℝ ∞ (fun p => NL (smoothMultiplierLowerJets (Q δ0 W i m p))) := by
  refine ⟨contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m)
      (W.jacobiCompact i m) (W.jacobiZero i m),?_⟩
  simpa only [jacobiJets,smoothMultiplierLowerJets_commonSupport] using
    contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m)
        (W.jacobiCompact i m) (W.jacobiZero i m)

/-- Actual smooth angular/Jacobi zero-order gains on the same support witnesses. -/
private lemma jacobiAngularGains_contDiffOn
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam : ℝ) (S : Set Pphys)
    (hG0 : ∀ p ∈ S, Guard lam Lam (p.1,(p.2.1,0))) (i m n : Fin 3) :
    ContDiffOn ℝ ∞ (fun p =>
      loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
        (Q δ0 W i m p) n p.1 p.2.1) S ∧
    ContDiffOn ℝ ∞ (fun p =>
      raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
        (Q δ0 W i m p) n p.1 p.2.1) S := by
  have hRawH : ContDiffOn ℝ ∞ (fun p : Pphys =>
      rawAdjointMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
        (Q δ0 W i m p) p.1 p.2.1) S := by
    intro p hp
    exact (contDiffAt_rawAdjointMultiplierZero_commonSupport hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData hg
      (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m)
      (W.jacobiCompact i m) (W.jacobiZero i m)
      (fun z : Pphys => z.1) contDiff_fst (fun z : Pphys => z.2.1) contDiff_snd.fst p
      (by
        unfold referenceGaugeNormalHighInvertibleLocus
        exact (hG0 p hp).2.2.2.1)).contDiffWithinAt
  have hRawL : ContDiffOn ℝ ∞ (fun p : Pphys =>
      rawHalfMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
        (Q δ0 W i m p) p.1 p.2.1) S := by
    intro p hp
    exact (contDiffAt_rawHalfMultiplierZero_commonSupport hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData
      (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m)
      (W.jacobiCompact i m) (W.jacobiZero i m)
      (fun z : Pphys => z.1) contDiff_fst (fun z : Pphys => z.2.1) contDiff_snd.fst p
      (hG0 p hp).2.2.1.1 (hG0 p hp).2.2.1.2.1).contDiffWithinAt
  refine ⟨?_,?_⟩
  · unfold loweringPiGain
    apply ContDiffOn.add
    · apply ContDiffOn.sum
      intro k hk
      exact contDiffOn_const.clm_comp
        (contDiff_nativeThreeHalfCoefficientMulL_rotationJets_commonSupport hcalc hF hO hD τ0
          (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m)
          (W.jacobiCompact i m) (W.jacobiZero i m) k n).contDiffOn
    · exact contDiffOn_const.clm_comp hRawH
  · unfold raisingPiGain
    apply ContDiffOn.sub
    · apply ContDiffOn.sum
      intro k hk
      exact (contDiff_nativeHalfCoefficientMulL_rotationJets_commonSupport hcalc hF hO hD τ0
        (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m)
        (W.jacobiCompact i m) (W.jacobiZero i m) k n).contDiffOn.clm_comp contDiffOn_const
    · exact hRawL.clm_comp contDiffOn_const

private lemma jacobiAngularHigh_contDiffOn
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam : ℝ) (S : Set Pphys)
    (hG0 : ∀ p ∈ S, Guard lam Lam (p.1,(p.2.1,0))) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (HH δ0 W i j) S := by
  have hPair (m n : Fin 3) : ContDiffOn ℝ ∞ (PairHigh δ0 W i j m n) S := by
    have hPi := jacobiNative_contDiff g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W i m
    have hQj := jacobiNative_contDiff g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j n
    have hU := (jacobiAngularGains_contDiffOn g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      δ0 W lam Lam S hG0 j n m).1
    have hV := (jacobiAngularGains_contDiffOn g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      δ0 W lam Lam S hG0 i m n).2
    unfold jacobiAngularPairHigh
    exact ((hPi.2.contDiffOn.clm_comp (contDiffOn_const.clm_comp hQj.1.contDiffOn)).add
      (hPi.2.contDiffOn.clm_comp (contDiffOn_const.clm_comp hU))).add
        (hV.clm_comp (hQj.2.contDiffOn.clm_comp contDiffOn_const))
  unfold jacobiAngularHigh
  exact ContDiffOn.sum (fun m _ => ContDiffOn.sum (fun n _ => hPair m n))

private def jacobiAngularRowsFoldedContract (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
    ∃ Cl : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Neg,
      (∀ i j : Fin 3, ContDiffOn ℝ ∞ (HH δ0 W i j) (commonRoom y0 ρ δ) ∧
        ContDiffOn ℝ ∞ (Cl i j) (commonRoom y0 ρ δ)) ∧
      (∀ i j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ u : Hi,
        JL (HH δ0 W i j p u) =
          HeadReverseLow i p (HeadHigh j p u)-HeadLow j p (HeadReverseHigh i p u)) ∧
      (∀ i j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ,
        (Cl i j p).comp IH = (JL).comp (HH δ0 W i j p) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Cl i j p) =
          (v016TransposeL (HH δ0 W j i p)).comp JL ∧
        ‖Cl i j p‖ ≤ (‖HH δ0 W j i p‖+‖HH δ0 W i j p‖)/2) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N →
        ∀ p ∈ commonRoom y0 ρ δ,
          ‖iteratedFDerivWithin ℝ n (HH δ0 W i j) (commonRoom y0 ρ δ) p‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Cl i j) (commonRoom y0 ρ δ) p‖ ≤ M)

attribute [local irreducible] jacobiAngularRowsFoldedContract

private theorem jacobiAngularRowsFoldedContract_proof
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    jacobiAngularRowsFoldedContract (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) δ0 W := by
  classical
  obtain ⟨lam,Lam,dF,_hlam,hdF,hdFρ,hFin⟩ := exists_finiteRoomGuard
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  let δ := min δ0 dF
  have hδ : 0 < δ := lt_min hδ0 hdF
  have hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0 := commonRoom_mono y0 ρ (min_le_left _ _)
  have hG0 (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) : Guard lam Lam (p.1,(p.2.1,0)) :=
    hFin (p.1,(p.2.1,0)) ⟨hp.1,hp.2.1,⟨by linarith,by linarith⟩⟩
  have hSmooth (i j : Fin 3) : ContDiffOn ℝ ∞ (HH δ0 W i j) (commonRoom y0 ρ δ) :=
    jacobiAngularHigh_contDiffOn g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      δ0 W lam Lam (commonRoom y0 ρ δ) hG0 i j
  have hGraph (i j : Fin 3) (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) (u : Hi) :
      JL (HH δ0 W i j p u) =
        HeadReverseLow i p (HeadHigh j p u)-HeadLow j p (HeadReverseHigh i p u) :=
    jacobiAngularHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel δ0 W lam Lam i j p (hSub hp) (hG0 p hp) u
  have hAdj (i j : Fin 3) (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) (u v : Hi) :
      PP (IH v) (JL (HH δ0 W i j p u)) = PP (IH u) (JL (HH δ0 W j i p v)) :=
    jacobiAngularHigh_swapped_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel δ0 W lam Lam i j p (hSub hp) (hG0 p hp) u v
  have hU : UniqueDiffOn ℝ (commonRoom y0 ρ δ) :=
    uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ
  have hLow (i j : Fin 3) : ∃ Cl : Pphys → Half →L[ℝ] Neg,
      ContDiffOn ℝ ∞ Cl (commonRoom y0 ρ δ) ∧ ∀ p ∈ commonRoom y0 ρ δ,
        (Cl p).comp IH = (JL).comp (HH δ0 W i j p) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Cl p) =
          (v016TransposeL (HH δ0 W j i p)).comp JL ∧
        ‖Cl p‖ ≤ (‖v016TransposeL (HH δ0 W j i p)‖+‖HH δ0 W i j p‖)/2 ∧
        ‖Cl p‖ ≤ (‖HH δ0 W j i p‖+‖HH δ0 W i j p‖)/2 :=
    v016_exists_contDiffOn_lowEndpoint (commonRoom y0 ρ δ) hU
      (HH δ0 W i j) (HH δ0 W j i) (hSmooth i j) (hSmooth j i) (hAdj i j)
  choose Cl hCl using hLow
  unfold jacobiAngularRowsFoldedContract
  refine ⟨δ,hδ,min_le_left _ _,(min_le_right _ _).trans hdFρ,Cl,
    fun i j => ⟨hSmooth i j,(hCl i j).1⟩,hGraph,?_,?_⟩
  · intro i j p hp
    have hAt := (hCl i j).2 p hp
    exact ⟨hAt.1,hAt.2.1,hAt.2.2.2⟩
  · intro N
    exact v016_exists_uniform_cap_two (commonRoom y0 ρ δ) (isCompact_commonRoom y0 ρ δ) hU
      (HH δ0 W) Cl hSmooth (fun i j => (hCl i j).1) N


/-- Actual H1/H1 gained producer on ANY retained common Pi/Jacobi witness set.
The only extra room is the standard actual finite physical guard, derived here.
All high/low graphs, smoothness and finite caps are discharged by actual APIs. -/
theorem exists_commonRoom_jacobiAngular_gained_rows
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
    ∃ Cl : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Neg,
      (∀ i j : Fin 3, ContDiffOn ℝ ∞ (HH δ0 W i j) (commonRoom y0 ρ δ) ∧
        ContDiffOn ℝ ∞ (Cl i j) (commonRoom y0 ρ δ)) ∧
      (∀ i j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ u : Hi,
        JL (HH δ0 W i j p u) =
          HeadReverseLow i p (HeadHigh j p u)-HeadLow j p (HeadReverseHigh i p u)) ∧
      (∀ i j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ,
        (Cl i j p).comp IH = (JL).comp (HH δ0 W i j p) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Cl i j p) =
          (v016TransposeL (HH δ0 W j i p)).comp JL ∧
        ‖Cl i j p‖ ≤ (‖HH δ0 W j i p‖+‖HH δ0 W i j p‖)/2) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N →
        ∀ p ∈ commonRoom y0 ρ δ,
          ‖iteratedFDerivWithin ℝ n (HH δ0 W i j) (commonRoom y0 ρ δ) p‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Cl i j) (commonRoom y0 ρ δ) p‖ ≤ M) := by
  simpa only [jacobiAngularRowsFoldedContract] using
    (jacobiAngularRowsFoldedContract_proof (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) hreg hKernel δ0 hδ0 W)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualJacobiAngularGainedRows

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualJacobiAngularGainedRows.exists_commonRoom_jacobiAngular_gained_rows
