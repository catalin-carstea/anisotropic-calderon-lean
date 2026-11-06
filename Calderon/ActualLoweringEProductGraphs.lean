import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.ActualRaisingEHighGraph
import Calderon.ActualHigherSAdjointLeadingCoordinate

/-! Product graphs for the paired lowering/E and reverse-E/raising maps with the same W.
The multiplier and smoothness helper proofs adapt the generator/E construction. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualCanonicalAngularGainedBracket ActualCanonicalGeneratorAngularGainedRows
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GH" => retainedGeneratorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GL" => retainedGeneratorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sh" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sl" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "CH" => gainedAtOrder hF hO hD (3/2 : ℝ)
local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j (1 : ℝ))
local notation "CaT" => loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CAS" => raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData

def loweringMultiplierHigh (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3) (c : RetainedCoefficient)
    (t : Tpar) : Hi →L[ℝ] Hi :=
  (∑ k : Fin 3, (Mh k).comp (GH δ0 W (Sum.inl (k,i)) c t)) +
    (Mh i).comp (GH δ0 W (Sum.inr ()) c t)
def raisingMultiplierHalf (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3) (c : RetainedCoefficient)
    (t : Tpar) : Half →L[ℝ] Half :=
  (∑ k : Fin 3, (GL δ0 W (Sum.inl (k,i)) c t).comp (Ml k)) -
    (GL δ0 W (Sum.inr ()) c t).comp (Ml i)
local notation "LP" => loweringMultiplierHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RP" => raisingMultiplierHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def loweringEHigh (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (G : Fin 3 → Pphys → Half →L[ℝ] Half) (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (CaT hreg G i t.1).comp (NH (QW δ0 W (Sum.inl j) t)) +
    (Th t.1).comp (LP δ0 W i (Sum.inl j) t) +
    (∑ m : Fin 3, ((CH i m).comp (NH (QW δ0 W (Sum.inr (j,m)) t)) +
      (AH m).comp (LP δ0 W i (Sum.inr (j,m)) t))) +
    (aH i).comp (ZH j t.1) - (ZL j t.1).comp (aH i)
def reverseERaisingHigh (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (RP δ0 W i (Sum.inl j) t).comp (Sh t.1) +
    (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t))).comp (-CAS hreg i t.1) +
    (∑ m : Fin 3, ((RP δ0 W i (Sum.inr (j,m)) t).comp (aH m) +
      (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t))).comp (CH m i))) +
    (zL j t.1).comp (AH i) - (AH i).comp (zH j t.1)
local notation "LF" => loweringEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RF" => reverseERaisingHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  reverseEHigh reverseELow retainedGeneratorHigh retainedGeneratorHalf retainedJets
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL sphereSobolevLinearCoordinateMulL sphereSobolevRotationL
  sphereSobolevShiftedDegreeL loweringHigh loweringLow raisingHigh raisingLow
  loweringMultiplierHigh raisingMultiplierHalf loweringEHigh reverseERaisingHigh

private lemma right_product_graph {E F N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (I : E →L[ℝ] F) (J : F →L[ℝ] N)
    (VH TH : E →L[ℝ] F) (VL TL : F →L[ℝ] N)
    (PH : E →L[ℝ] E) (PL : F →L[ℝ] F)
    (K : E →L[ℝ] F) (D : E →L[ℝ] E)
    (hK : ∀ u, J (K u) = VL (TH u) - TL (VH u))
    (hT : ∀ u, J (TH u) = TL (I u))
    (hD : ∀ u, I (D u) = VH (PH u) - PL (VH u)) (u : E) :
    J ((K.comp PH + TH.comp D) u) =
      VL (TH (PH u)) - TL (PL (VH u)) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    map_add, hK, hT, hD, map_sub]
  abel

private lemma left_product_graph {E F N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (J : F →L[ℝ] N) (VH TH : E →L[ℝ] F) (VL TL : F →L[ℝ] N)
    (PL : F →L[ℝ] F) (PN : N →L[ℝ] N)
    (D : F →L[ℝ] F) (K : E →L[ℝ] F)
    (hD : ∀ v, J (D v) = PN (VL v) - VL (PL v))
    (hP : ∀ v, J (PL v) = PN (J v))
    (hK : ∀ u, J (K u) = TL (VH u) - VL (TH u)) (u : E) :
    J ((D.comp TH + PL.comp K) u) =
      PN (TL (VH u)) - VL (PL (TH u)) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    map_add, hD, hP, hK, map_sub]
  abel

private lemma coordinate_native_half_comm (Q : SmoothCoefficientJets 3) (k : Fin 3) (v : Half) :
    (Ml k) (NL (smoothMultiplierLowerJets Q) v) =
      NL (smoothMultiplierLowerJets Q) ((Ml k) v) := by
  simpa only [coordinateJets_half hcalc hF hO hD τ0 k] using
    nativeHalfCoefficientMulL_lowerJets_comm_apply hcalc hF hO hD τ0 (coordinateJets k) Q v

theorem loweringMultiplierHigh_graph (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3)
    (c : RetainedCoefficient) (t : Tpar)
    (hU : ∀ V : Generator, ∀ u : Hi,
      IH (GH δ0 W V c t u) =
        generatorHigh V (NH (QW δ0 W c t) u) -
          NL (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorHigh V u)) (u : Hi) :
    IH (LP δ0 W i c t u) =
      aH i (NH (QW δ0 W c t) u) -
        NL (smoothMultiplierLowerJets (QW δ0 W c t)) (aH i u) := by
  have hM (k : Fin 3) (z : Hi) : IH ((Mh k) z) = (Ml k) (IH z) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD
      (3/2 : ℝ) (1/2 : ℝ) (by norm_num) _ z
  have hRot (k : Fin 3) (z : Hi) := hU (Sum.inl (k,i)) z
  have hDeg (z : Hi) := hU (Sum.inr ()) z
  simp only [generatorHigh] at hRot hDeg
  simp only [loweringMultiplierHigh, loweringHigh, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sum, hM, hRot, hDeg, map_sub,
    coordinate_native_half_comm hcalc hF hO hD τ0,
    Finset.sum_sub_distrib]
  abel

theorem raisingMultiplierHalf_graph (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3)
    (c : RetainedCoefficient) (t : Tpar)
    (hU : ∀ V : Generator, ∀ v : Half,
      JL (GL δ0 W V c t v) =
        generatorLow V (NL (smoothMultiplierLowerJets (QW δ0 W c t)) v) -
          NN (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorLow V v)) (v : Half) :
    JL (RP δ0 W i c t v) =
      NN (smoothMultiplierLowerJets (QW δ0 W c t)) (AL i v) -
        AL i (NL (smoothMultiplierLowerJets (QW δ0 W c t)) v) := by
  have hRot (k : Fin 3) (z : Half) := hU (Sum.inl (k,i)) z
  have hDeg (z : Half) := hU (Sum.inr ()) z
  simp only [generatorLow] at hRot hDeg
  simp only [raisingMultiplierHalf, raisingLow, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, map_neg, map_sum, hRot, hDeg,
    ← coordinate_native_half_comm hcalc hF hO hD τ0,
    Finset.sum_sub_distrib]
  abel

theorem loweringEHigh_graph_at
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (G : Fin 3 → Pphys → Half →L[ℝ] Half) (i j : Fin 3) (t : Tpar)
    (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hRad : ∀ u : Hi, JL (CaT hreg G i t.1 u) =
      aL i (Th t.1 u) - Tl t.1 (aH i u))
    (hU : ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ u : Hi,
      IH (GH δ0 W V c t u) = generatorHigh V (NH (QW δ0 W c t) u) -
        NL (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorHigh V u)) (u : Hi) :
    JL (LF hreg δ0 W G i j t u) = aL i (EH j t u) - EL j t (aH i u) := by
  have hLP (c : RetainedCoefficient) (z : Hi) :
      IH (LP δ0 W i c t z) = aH i (NH (QW δ0 W c t) z) -
        NL (smoothMultiplierLowerJets (QW δ0 W c t)) (aH i z) :=
    loweringMultiplierHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      δ0 W i c t (fun V => hU V c) z
  have hp := (W.piGerm j t ht).self_of_nhds
  have hR0 := right_product_graph IH JL (aH i) (Th t.1) (aL i) (Tl t.1)
    (NH (QW δ0 W (Sum.inl j) t)) (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t)))
    (CaT hreg G i t.1) (LP δ0 W i (Sum.inl j) t) hRad
    (fun z => v016_actual_Th_compat hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg z)
    (hLP (Sum.inl j)) u
  have hR : JL (((CaT hreg G i t.1).comp (NH (QW δ0 W (Sum.inl j) t)) +
      (Th t.1).comp (LP δ0 W i (Sum.inl j) t)) u) =
      aL i (Th t.1 (PiH j t u)) - Tl t.1 (PiL j t (aH i u)) := by
    simpa only [retainedJets, ActualPiJacobiRadialGainedRows.piJets, hp.1, hp.2.1] using hR0
  have hA (m : Fin 3) : JL (((CH i m).comp (NH (QW δ0 W (Sum.inr (j,m)) t)) +
      (AH m).comp (LP δ0 W i (Sum.inr (j,m)) t)) u) =
      aL i (AH m (NH (NJ3 j m t.1) u)) -
        AL m (NL (NJ2 j m t.1) (aH i u)) := by
    have h0 := right_product_graph IH JL (aH i) (AH m) (aL i) (AL m)
      (NH (QW δ0 W (Sum.inr (j,m)) t)) (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t)))
      (CH i m) (LP δ0 W i (Sum.inr (j,m)) t)
      (gainedHigh_graph hF hO hD i m) (v017_inclusion_raisingHigh hF hO hD m)
      (hLP (Sum.inr (j,m))) u
    have hn := (W.jacobiGerm j m t.1 ht.1).self_of_nhds
    simpa only [retainedJets, jacobiJets, hn.1, hn.2.1] using h0
  have hZero : JL (aH i (ZH j t.1 u)) = aL i (IH (ZH j t.1 u)) :=
    v017_inclusion_loweringHigh hF hO hD i _
  have hSum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl (fun m _ => hA m)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, map_add] at hR hSum
  simp only [loweringEHigh, canonicalHigh, canonicalLow, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, map_sum, hZero]
  have hMain := congrArg₂ (fun x y : Neg =>
      (x+y+aL i (IH (ZH j t.1 u))) - JL (ZL j t.1 (aH i u))) hR hSum
  exact hMain.trans (by simp only [Finset.sum_sub_distrib]; abel)

theorem reverseERaisingHigh_graph_at
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hRad : ∀ u : Hi, JL (CAS hreg i t.1 u) =
      AL i (Sh t.1 u) - Sl t.1 (AH i u))
    (hU : ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ v : Half,
      JL (GL δ0 W V c t v) = generatorLow V (NL (smoothMultiplierLowerJets (QW δ0 W c t)) v) -
        NN (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorLow V v)) (u : Hi) :
    JL (RF hreg δ0 W i j t u) = eL j t (AH i u) - AL i (eH j t u) := by
  have hRP (c : RetainedCoefficient) (z : Half) :
      JL (RP δ0 W i c t z) =
        NN (smoothMultiplierLowerJets (QW δ0 W c t)) (AL i z) -
          AL i (NL (smoothMultiplierLowerJets (QW δ0 W c t)) z) :=
    raisingMultiplierHalf_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      δ0 W i c t (fun V => hU V c) z
  have hp := (W.piGerm j t ht).self_of_nhds
  have hNegRad (z : Hi) : JL ((-CAS hreg i t.1) z) =
      Sl t.1 (AH i z) - AL i (Sh t.1 z) := by
    simpa only [ContinuousLinearMap.neg_apply, map_neg, neg_sub] using
      congrArg (fun n : Neg => -n) (hRad z)
  have hR0 := left_product_graph JL (AH i) (Sh t.1) (AL i) (Sl t.1)
    (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t)))
    (NN (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t)))
    (RP δ0 W i (Sum.inl j) t) (-CAS hreg i t.1)
    (hRP (Sum.inl j))
    (v017_native_half_negative hcalc hF hO hD τ0 (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t)))
    hNegRad u
  have hR : JL (((RP δ0 W i (Sum.inl j) t).comp (Sh t.1) +
      (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inl j) t))).comp (-CAS hreg i t.1)) u) =
      PiN j t (Sl t.1 (AH i u)) - AL i (PiL j t (Sh t.1 u)) := by
    simpa only [retainedJets, ActualPiJacobiRadialGainedRows.piJets, hp.2.1, hp.2.2] using hR0
  have hA (m : Fin 3) : JL (((RP δ0 W i (Sum.inr (j,m)) t).comp (aH m) +
      (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t))).comp (CH m i)) u) =
      NN (NJ2 j m t.1) (aL m (AH i u)) -
        AL i (NL (NJ2 j m t.1) (aH m u)) := by
    have h0 := left_product_graph JL (AH i) (aH m) (AL i) (aL m)
      (NL (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t)))
      (NN (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t)))
      (RP δ0 W i (Sum.inr (j,m)) t) (CH m i)
      (hRP (Sum.inr (j,m)))
      (v017_native_half_negative hcalc hF hO hD τ0 (smoothMultiplierLowerJets (QW δ0 W (Sum.inr (j,m)) t)))
      (gainedHigh_graph hF hO hD m i) u
    have hn := (W.jacobiGerm j m t.1 ht.1).self_of_nhds
    simpa only [retainedJets, jacobiJets, hn.2.1, hn.2.2] using h0
  have hZero : JL (AH i (zH j t.1 u)) = AL i (IH (zH j t.1 u)) :=
    v017_inclusion_raisingHigh hF hO hD i _
  have hSum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl (fun m _ => hA m)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, map_add] at hR hSum
  simp only [reverseERaisingHigh, reverseEHigh, reverseELow, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, map_sum, hZero]
  have hMain := congrArg₂ (fun x y : Neg =>
      x+y+JL (zL j t.1 (AH i u)) - AL i (IH (zH j t.1 u))) hR hSum
  exact hMain.trans (by simp only [Finset.sum_sub_distrib]; abel)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
