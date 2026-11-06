import Calderon.ActualHighAdjointSmoothMultiplierBoundaryCommutator
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.ActualHigherSFormation
import Calderon.ActualHigherSAngularAdjoint
import Calderon.ActualCommonFirstWordQuadraticAdjoint
import Calderon.ActualGeneratorEHighGainedGraph
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualPiJacobiRadialGainedRows
import Calderon.ActualAngularHighDraft
import Calderon.SphereSobolevAngularRaisingSingle
import Calderon.ActualFiniteHarmonicModelRaisingCommute

/-! Raising and coordinate regularity:
* the generic angular-S principal/error rewrite and its `9 CQ CC r ‖U‖` correction bound;
* the angular transpose at `3/2` is `raisingHigh` by definition;
* raising symmetry, proved from native singles, `harmonicDerivativeAdjoint_composition_commute`
  and partial sums (the method of native `gainedHigh_graph`);
* `C^∞` regularity of the Hi→Hi high adjoint coordinate Taylor remainder `XG` on a room. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualRaisingEHighGainedEndpoints
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection ActualGeneratorEHighGainedGraph
  SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph HarmonicDerivativeOperator
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-! ## 1. Generic algebra -/
section Algebra
variable {E F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- (R) Radial/raising cancellation, multiplier on the right of the generator. -/
theorem radialRaising_cancel (I : E →L[ℝ] F) (J : F →L[ℝ] N) (Th : E →L[ℝ] F) (Tl : F →L[ℝ] N)
    (Rh : Fin 3 → E →L[ℝ] F) (Rl : Fin 3 → F →L[ℝ] N) (Bh : E →L[ℝ] F) (Bl : F →L[ℝ] N)
    (Mh : Fin 3 → E →L[ℝ] E) (Ml : Fin 3 → F →L[ℝ] F)
    (Cr : Fin 3 → E →L[ℝ] F) (Cd : E →L[ℝ] F) (X : Fin 3 → E →L[ℝ] E) (i : Fin 3)
    (k1 : ∀ j x, J (Rh j x) = Rl j (I x)) (k1' : ∀ x, J (Bh x) = Bl (I x))
    (k2 : ∀ j x, I (X j x) = Th (Mh j x) - Ml j (Th x))
    (k3 : ∀ j x, J (Cr j x) = Rl j (Th x) - Tl (Rh j x))
    (k3' : ∀ x, J (Cd x) = Bl (Th x) - Tl (Bh x)) (u : E) :
    J (((∑ j : Fin 3, ((Rh j).comp (X j) - (Cr j).comp (Mh j))) - Bh.comp (X i) +
        Cd.comp (Mh i)) u) =
      ((-∑ j : Fin 3, (Rl j).comp (Ml j)) + Bl.comp (Ml i)) (Th u) -
        Tl (((-∑ j : Fin 3, (Rh j).comp (Mh j)) + Bh.comp (Mh i)) u) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, map_neg, map_sum, k1, k1', k2, k3, k3']
  simp only [Finset.sum_sub_distrib, map_sub]
  abel

/-- (M) Raising/multiplier high gain from generator/multiplier gains; needs `Mh P = P Mh`. -/
theorem raisingMultiplier_cancel (I : E →L[ℝ] F)
    (Rh : Fin 3 → E →L[ℝ] F) (Bh : E →L[ℝ] F) (Mh : Fin 3 → E →L[ℝ] E)
    (PH : E →L[ℝ] E) (PL : F →L[ℝ] F) (GR : Fin 3 → E →L[ℝ] E) (GB : E →L[ℝ] E) (i : Fin 3)
    (hR : ∀ j x, I (GR j x) = Rh j (PH x) - PL (Rh j x))
    (hB : ∀ x, I (GB x) = Bh (PH x) - PL (Bh x))
    (hC : ∀ j x, Mh j (PH x) = PH (Mh j x)) (u : E) :
    I (((-∑ j : Fin 3, (GR j).comp (Mh j)) + GB.comp (Mh i)) u) =
      ((-∑ j : Fin 3, (Rh j).comp (Mh j)) + Bh.comp (Mh i)) (PH u) -
        PL (((-∑ j : Fin 3, (Rh j).comp (Mh j)) + Bh.comp (Mh i)) u) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_add, map_neg, map_sum,
    hR, hB, hC]
  simp only [Finset.sum_sub_distrib]
  abel

/-- (G) Assembly of the full [A_i,E_j] graph over the canonical E words. -/
theorem raisingE_assembly (I : E →L[ℝ] F) (J : F →L[ℝ] N)
    (Th : E →L[ℝ] F) (Tl : F →L[ℝ] N) (PiH : E →L[ℝ] E) (PiL : F →L[ℝ] F)
    (AH : Fin 3 → E →L[ℝ] F) (AL : Fin 3 → F →L[ℝ] N)
    (NH : Fin 3 → E →L[ℝ] E) (NL : Fin 3 → F →L[ℝ] F) (ZH : E →L[ℝ] E) (ZL : F →L[ℝ] F)
    (K : E →L[ℝ] F) (Gp : E →L[ℝ] E) (Gn : Fin 3 → E →L[ℝ] E) (i : Fin 3)
    (hK : ∀ x, J (K x) = AL i (Th x) - Tl (AH i x))
    (hGp : ∀ x, I (Gp x) = AH i (PiH x) - PiL (AH i x))
    (hGn : ∀ m x, I (Gn m x) = AH i (NH m x) - NL m (AH i x))
    (hS : ∀ m x, AL m (AH i x) = AL i (AH m x))
    (hA : ∀ m x, J (AH m x) = AL m (I x))
    (hT : ∀ x, J (Th x) = Tl (I x)) (u : E) :
    J ((K.comp PiH + Th.comp Gp + (∑ m : Fin 3, (AH m).comp (Gn m)) +
        ((AH i).comp ZH - ZL.comp (AH i))) u) =
      AL i ((Th.comp PiH + (∑ m : Fin 3, (AH m).comp (NH m)) + I.comp ZH) u) -
        (Tl.comp PiL + (∑ m : Fin 3, (AL m).comp (NL m)) + J.comp ZL) (AH i u) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, map_sum, hK, hGp, hGn, hA, hT, hS]
  simp only [Finset.sum_sub_distrib]
  abel

/-- Algebraic first-word transport: injectivity only, no inverse norm. -/
theorem angular_first_word_transport (I : E →L[ℝ] F) (J : F →L[ℝ] N)
    (hJ : Function.Injective J)
    (AH : E →L[ℝ] F) (AL : F →L[ℝ] N) (EHj : E →L[ℝ] F) (ELj : F →L[ℝ] N) (Cij : E →L[ℝ] F)
    (hA : ∀ x, J (AH x) = AL (I x)) (hE : ∀ x, J (EHj x) = ELj (I x))
    (hC : ∀ x, J (Cij x) = AL (EHj x) - ELj (AH x))
    (u ua z : E) (hz : I z = EHj u) (ha : I ua = AH u) :
    AH z = EHj ua + Cij u := by
  apply hJ
  rw [map_add, hA, hz, hE, ha, hC]
  abel

/-- Literal angular-S rewrite; both Q orders kept, no symmetry of Q. -/
theorem angularS_rewrite {H : Type*} [AddCommGroup H] [Module ℝ H] (r : ℝ)
    (Q : Fin 3 → Fin 3 → ℝ) (AV EUA CU : Fin 3 → Fin 3 → H)
    (h : ∀ i j, AV i j = EUA j i + CU i j) :
    r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (AV i j + EUA i j)) =
      r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (EUA i j + EUA j i)) +
        r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CU i j) := by
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [h, ← smul_add]
  congr 1
  abel

/-- Correction bound `9 CQ CC r ‖U‖`; no norm of the lifts is used. -/
theorem norm_angularS_correction_le {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (r : ℝ) (hr : 0 < r) (Q : Fin 3 → Fin 3 → ℝ) (Cop : Fin 3 → Fin 3 → X →L[ℝ] H) (U : X)
    (CQ CC : ℝ) (hQ : ∀ i j, |Q i j| ≤ CQ) (hC : ∀ i j, ‖Cop i j‖ ≤ CC) :
    ‖r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Cop i j U)‖ ≤ 9 * CQ * CC * r * ‖U‖ := by
  have hCQ : 0 ≤ CQ := (abs_nonneg _).trans (hQ 0 0)
  have hterm : ∀ i j, ‖Q i j • Cop i j U‖ ≤ CQ * (CC * ‖U‖) := fun i j => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hQ i j) ((Cop i j).le_of_opNorm_le (hC i j) U) (norm_nonneg _) hCQ
  have hsum : ‖∑ i : Fin 3, ∑ j : Fin 3, Q i j • Cop i j U‖ ≤ 9 * (CQ * (CC * ‖U‖)) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, Q i j • Cop i j U‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖Q i j • Cop i j U‖ :=
        Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, CQ * (CC * ‖U‖) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = 9 * (CQ * (CC * ‖U‖)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  calc
    r * _ ≤ r * (9 * (CQ * (CC * ‖U‖))) := mul_le_mul_of_nonneg_left hsum hr.le
    _ = _ := by ring
end Algebra

/-! ## 2. Actual objects -/
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GH" => retainedGeneratorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j (1 : ℝ))
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
local notation "Rh" j:max i:max => sphereSobolevRotationL (3/2 : ℝ) j i
local notation "Rl" j:max i:max => sphereSobolevRotationL (1/2 : ℝ) j i
local notation "BH" => (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)
local notation "BL" => (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "TT" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "UAF" => ActualHigherSFormation.higherSRaisingInput hF hO hD
local notation "VFL" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-! ### 2a. Raising representation (definitional) and raising symmetry (native singles) -/

/-- The literal angular transpose at `3/2` IS `raisingHigh` (identical definition bodies). -/
lemma angularTranspose_threeHalf_eq_raisingHigh (i : Fin 3) :
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i : Hi →L[ℝ] Half) = AH i := rfl

private lemma v079_raisingHigh_single (i : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    AH i (sphereSobolevSingleL (3/2 : ℝ) k u) =
      sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k i u) := by
  have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2 : ℝ) i k u
  simpa only [raisingHigh,sphereSobolevAngularCoordinateTransposeL,sphereSobolevSingleL,
    ContinuousLinearMap.smul_apply,lp.singleContinuousLinearMap_apply,
    show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num] using h

private lemma v079_raisingLow_single (i : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    AL i (sphereSobolevSingleL (1/2 : ℝ) k u) =
      sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k i u) := by
  have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (1/2 : ℝ) i k u
  simpa only [raisingLow,sphereSobolevAngularCoordinateTransposeL,sphereSobolevSingleL,
    ContinuousLinearMap.smul_apply,lp.singleContinuousLinearMap_apply,
    show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num] using h

attribute [local irreducible] raisingHigh raisingLow sphereSobolevInclusionL
  sphereSobolevAngularCoordinateTransposeL sphereSobolevRotationL sphereSobolevShiftedDegreeL
  sphereSobolevLinearCoordinateMulL sphereSobolevSingleL sphereSobolevCoefficientL
  referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily

/-- Raising symmetry `Alo_m Ahi_i = Alo_i Ahi_m` on ALL of Hi (degree 0 included). -/
theorem raisingLow_comp_raisingHigh_symm (i m : Fin 3) (v : Hi) :
    AL m (AH i v) = AL i (AH m v) := by
  let Lm : Hi →L[ℝ] Neg := (AL m).comp (AH i)
  let Rm : Hi →L[ℝ] Neg := (AL i).comp (AH m)
  have hSingle (k : ℕ) (u : harmonicSphereSubspace k) :
      Lm (sphereSobolevSingleL (3/2 : ℝ) k u) = Rm (sphereSobolevSingleL (3/2 : ℝ) k u) := by
    simp only [Lm,Rm,ContinuousLinearMap.comp_apply,v079_raisingHigh_single,v079_raisingLow_single]
    rw [ActualFiniteHarmonicModel.harmonicDerivativeAdjoint_composition_commute hF k m i u]
  have hFinite (n : ℕ) : Lm (sphereSobolevPartialSum (3/2 : ℝ) n v) =
      Rm (sphereSobolevPartialSum (3/2 : ℝ) n v) := by
    simp only [sphereSobolevPartialSum,map_sum]
    exact Finset.sum_congr rfl (fun k _ => hSingle k (sphereSobolevCoefficientL (3/2 : ℝ) k v))
  exact tendsto_nhds_unique
    (((Lm.continuous.tendsto v).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) v)).congr'
      (Filter.Eventually.of_forall hFinite))
    ((Rm.continuous.tendsto v).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) v))

/-! ### 2b. The actual family `C_A` -/

/-- Native HIGH coordinate/Th gain (order zero, Hi → Hi). -/
def coordinateAdjointHighGain (j : Fin 3) (p : Pphys) : Hi →L[ℝ] Hi :=
  secondTaylorRemainder (fun tau : ℝ =>
    referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (coordinateJets j) (p.1,(p.2.1,tau))) p.2.2
local notation "XG" => coordinateAdjointHighGain hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0


/-- C-infinity for the actual Hi-to-Hi coordinate Taylor gain on its true high locus. -/
theorem coordinateAdjointHighGain_contDiffAt_of_high_segment (k : Fin 3) (p : Pphys)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈
      referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc) :
    ContDiffAt ℝ ∞ (XG k) p := by
  unfold coordinateAdjointHighGain
  let T : ((ℝ × R3) × ℝ) → Pphys := fun z => (z.1.1,(z.1.2,z.2))
  let σ : Pphys → (ℝ × R3) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  let U : Set ((ℝ × R3) × ℝ) := T ⁻¹' referenceGaugeNormalHighInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc
  let F : ((ℝ × R3) × ℝ) → Hi →L[ℝ] Hi := fun z =>
    referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (coordinateJets k) (T z)
  have hT : ContDiff ℝ ∞ T := contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  have hσ : ContDiff ℝ ∞ σ := (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  have hU : IsOpen U := (isOpen_referenceGaugeNormalHighInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc).preimage hT.continuous
  have hFsm : ContDiffOn ℝ ∞ F U := by
    intro z hz
    exact ((contDiffAt_referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (coordinateJets k) (T z) hz).comp
        z hT.contDiffAt).contDiffWithinAt
  have hTaylor := contDiffAt_secondTaylorRemainder_joint_of_open_segment
    F U hU hFsm (p.1,p.2.1) p.2.2 hSegment
  simpa only [F,T,σ,Function.comp_def] using
    hTaylor.comp (f := σ) p hσ.contDiffAt

/-- Fixed genuine high-invertibility room, before all g2/profiles/finite inputs. -/
theorem exists_coordinateAdjointHighGain_germs (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (hδ0 : 0 < δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ k : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ContDiffAt ℝ ∞ (XG k) p := by
  have hRoomFull := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases hRoomFull with ⟨lam,Lam,d,_hlam,hd,hdρ,hRoom⟩
  let δ := min δ0 (d/2)
  have hδ : 0 < δ := lt_min hδ0 (by positivity)
  have hδd : δ ≤ d := (min_le_right _ _).trans (by linarith)
  refine ⟨δ,hδ,min_le_left _ _,hδd.trans hdρ,?_⟩
  intro k p hp
  apply coordinateAdjointHighGain_contDiffAt_of_high_segment
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 k p
  intro θ hθ
  have hr : |θ*p.2.2| ≤ d := by
    calc
      _ = θ*|p.2.2| := by rw [abs_mul,abs_of_nonneg hθ.1]
      _ ≤ 1*|p.2.2| := mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg _)
      _ ≤ d := by simpa only [one_mul] using (abs_le.mpr hp.2.2).trans hδd
  have hz := hRoom (p.1,(p.2.1,θ*p.2.2)) ⟨hp.1,hp.2.1,abs_le.mp hr⟩
  change (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 (p.2.1,θ*p.2.2)).IsInvertible ∧
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 (p.2.1,θ*p.2.2)).IsInvertible
  exact hz.2.2.2.1


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualRaisingEHighGainedEndpoints
