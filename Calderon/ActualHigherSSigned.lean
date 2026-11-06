import Calderon.ActualHigherSFormation
import Calderon.ActualFullECanonicalEndpoints
import Calderon.SphereSobolevPairing
import Calderon.ActualWeightedHorizontalGreen
import Calderon.ActualHigherSErrorSplit

/-! Source-only author: Opusv040, repaired Opusv044, 29 October 2026. UNCOMPILED.
Before-source mathematics: INTEGRATED-PAIRING-MATHEMATICS.md §2 (same output directory).
Actual pointwise transfer identities on finite INPUTS tested against `IH (u y)`: every literal
higher-S term in which the original low quotient `LQ_i` acts on an INCLUDED vector (`E_j`,
`Ahi_j u`, `D_j u`) equals a pairing against the genuine reverse word `e_i u`.
v044 repairs: printed formation API (`higherSParam L δr Ar p q`, `higherSInput hO hD`,
`higherSReferenceInput hO hD g L hg δr Ar p hδr hAr q`, `higherSRaisingInput hF hO hD`,
`higherSLift` without positivity proofs, `HigherSRoomAt` without `hg`); pairing algebra from the
checked `halfPairing_*` lemmas; the reverse family carries BOTH its ambient germs and its
pairing from ONE `obtain` of `exists_commonRoom_actual_fullE_ordinary_endpoints`.
NOT used or claimed: `e = -E + gain`, positivity of `Q`, signed estimate, Sdag, coercivity. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSSigned
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds SphereHarmonic.DegreeGraphLifting ConformalDepth ActualFiniteHarmonicModel
  ActualHigherSFormation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-! ## 1. Pairing algebra (thin wrappers of the checked `halfPairing_*` lemmas) -/

lemma pp_inclusion_symm (x z : Half) : PP x (JL z) = PP z (JL x) :=
  halfPairing_inclusion_symm x z

lemma pp_smul_right (x : Half) (r : ℝ) (v : Neg) : PP x (r • v) = r * PP x v :=
  halfPairing_smul_right x r v

lemma pp_add_right (x : Half) (u v : Neg) : PP x (u + v) = PP x u + PP x v :=
  halfPairing_add_right x u v

lemma pp_sub_right (x : Half) (u v : Neg) : PP x (u - v) = PP x u - PP x v := by
  unfold sphereSobolevDualPairing; exact inner_sub_right x u v

lemma pp_sum_right (x : Half) (f : Fin 3 → Neg) :
    PP x (∑ i : Fin 3, f i) = ∑ i : Fin 3, PP x (f i) :=
  halfPairing_sum_right Finset.univ x f

lemma pp_zero_left (v : Neg) : PP (0 : Half) v = 0 := halfPairing_zero_left v

lemma pp_zero_right (x : Half) : PP x (0 : Neg) = 0 := by
  have h := halfPairing_smul_right x 0 0
  rwa [zero_smul, zero_mul] at h

lemma pp_smul_left (r : ℝ) (x : Half) (v : Neg) : PP (r • x) v = r * PP x v := by
  unfold sphereSobolevDualPairing; exact real_inner_smul_left x v r

private lemma pp_transfer_value (v : Hi) (w b : Half) (A : Half →L[ℝ] Neg) (z : Neg)
    (hv : IH v = w) (ht : PP b (A (IH v)) = PP (IH v) z) :
    PP b (A w) = PP w z := by
  calc
    PP b (A w) = PP b (A (IH v)) := congrArg (fun t : Half => PP b (A t)) hv.symm
    _ = PP (IH v) z := ht
    _ = PP w z := congrArg (fun t : Half => PP t z) hv

private lemma pp_zero_image_transfer (A : Hi →L[ℝ] Half) (B : Half →L[ℝ] Neg)
    (e : Hi →L[ℝ] Half) :
    PP (IH (0 : Hi)) (B (A 0)) = PP (A 0) (JL (e 0)) := by
  simp only [map_zero, pp_zero_left, pp_zero_right]

private lemma pp_zero_transfer (B : Half →L[ℝ] Neg) (e : Hi →L[ℝ] Half) :
    PP (IH (0 : Hi)) (B 0) = PP (0 : Half) (JL (e 0)) := by
  simp only [map_zero, pp_zero_left, pp_zero_right]

private lemma pp_zero_inputs (x : Hi) (w : Half) (B : Half →L[ℝ] Neg)
    (e : Hi →L[ℝ] Half) (hx : x = 0) (hw : w = 0) :
    PP (IH x) (B w) = PP w (JL (e x)) := by
  rw [hx, hw]
  exact pp_zero_transfer B e

/-! ## 2. Actual data -/
section Actual
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
local notation "MQ" => referenceHighAdjointMovingDifferenceQuotient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LQ" => referenceLowerAdjointMovingDifferenceQuotient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ahi" => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)
local notation "Alo" => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ)

lemma paramRoom_mono {δ δ' : ℝ} (h : δ ≤ δ') {t : Tpar} (ht : t ∈ ParamRoom δ) :
    t ∈ ParamRoom δ' :=
  ⟨commonRoom_mono y0 ρ h ht.1, ht.2⟩

/-- The genuine ordinary full-E reverse family, exported as an existential witness of the
PUBLIC conclusions of `exists_commonRoom_actual_fullE_ordinary_endpoints`: its ambient
`ContDiffAt` germs and its original reverse pairing come from the SAME `obtain`. -/
theorem exists_actual_reverse_family (hreg : FixedDirichletRegularity) :
    ∃ δE : ℝ, 0 < δE ∧ ∃ e : Fin 3 → Tpar → Hi →L[ℝ] Half,
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δE, ContDiffAt ℝ ∞ (e i) t) ∧
      ∀ i : Fin 3, ∀ t ∈ ParamRoom δE, ∀ u v : Hi,
        PP (EH i t u) (JL (IH v)) = PP (IH u) (JL (e i t v)) := by
  obtain ⟨δE, hδE, _hδEρ, _hΩE, _WE, hSm, _hCompat, hPairE, _hZS, _hZC, _hCaps⟩ :=
    exists_commonRoom_actual_fullE_ordinary_endpoints
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  exact ⟨δE, hδE, _, fun i t ht => (hSm i t ht).2.2.1, hPairE⟩

/-- v040 target kept: the reverse pairing alone (from the same family theorem). -/
theorem exists_actual_reverse_pairing (hreg : FixedDirichletRegularity) :
    ∃ δE : ℝ, 0 < δE ∧ ∃ e : Fin 3 → Tpar → Hi →L[ℝ] Half,
      ∀ i : Fin 3, ∀ t ∈ ParamRoom δE, ∀ u v : Hi,
        PP (EH i t u) (JL (IH v)) = PP (IH u) (JL (e i t v)) := by
  obtain ⟨δE, hδE, e, _hS, hP⟩ := exists_actual_reverse_family hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 hreg
  exact ⟨δE, hδE, e, hP⟩

/-! ### Profile section (same variable order as the formation profile section) -/
section Profile
variable (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
include hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q

local notation "RR" => referenceRadius δr Ar p L
local notation "T" => higherSParam L δr Ar p q
local notation "U" => higherSInput hO hD
local notation "UD" => higherSReferenceInput hO hD g L hg δr Ar p hδr hAr q
local notation "UA" => higherSRaisingInput hF hO hD
local notation "V" => higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p q
local notation "Room" => HigherSRoomAt hF hO hD g L y0 Φ B ε C ρ H a w hData hcalc τ0 δr Ar p q
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)
local notation "Qc" g2:max => referenceDensityPrincipalFrameCoefficient g g2 L q

/-- Finite-lift dictionary: `IH (UA_j) = Ahi_j u` (global in `z`). -/
lemma raisingInput_inclusion (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (z : R3) :
    IH (UA F0 j z) = Ahi j (U F0 z) :=
  (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (coreRaising hO hD hF j F0) z).trans
    (sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F0 z j).symm

/-- Finite-lift dictionary: `IH (UD_j) = D_j u` with the ACTUAL radius weight (global in `z`). -/
lemma referenceInput_inclusion (F0 : smoothCompactFiniteSphereCore hO hD) (j : Fin 3) (z : R3) :
    IH (UD F0 j z) = referenceHighWeightedHorizontalAction g L q RR (U F0) z j :=
  (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (coreReferenceInput hO hD g hg L q δr Ar p j hδr hAr F0) z).trans
    (referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q
      δr Ar p hδr hAr F0 z j).symm

/-- **Transfer Lemma.** At a room point, the original low quotient acting on an included vector,
tested against `IH v`, equals the included vector tested against the actual reverse word. -/
lemma lowerQuotient_transfer (hreg : FixedDirichletRegularity) (hq : q ∈ Icc (0 : ℝ) 1)
    (δ : ℝ) (y : R3) (hy : Room δ y) (e : Fin 3 → Tpar → Hi →L[ℝ] Half)
    (hPair : ∀ i : Fin 3, ∀ u v : Hi, PP (EH i (T y) u) (JL (IH v)) = PP (IH u) (JL (e i (T y) v)))
    (i : Fin 3) (wv v : Hi) :
    PP (IH v) (LQ q RR y i (IH wv)) = PP (IH wv) (JL (e i (T y) v)) := by
  rw [lowerQuotient_inclusion_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg hq δ y hy i wv]
  rw [pp_inclusion_symm (IH v) (EH i (T y) wv)]
  exact hPair i wv v

/-- The three actual signed transfer identities, for every `y ∈ R3`. -/
def HigherSSignedTransferAt (g2 : MatrixField) (e : Fin 3 → Tpar → Hi →L[ℝ] Half)
    (F0 : smoothCompactFiniteSphereCore hO hD) : Prop :=
  (∀ y : R3, ∀ i j : Fin 3,
    PP (IH (U F0 y)) (LQ q RR y i (MQ q RR y j (U F0 y))) =
      PP (MQ q RR y j (U F0 y)) (JL (e i (T y) (U F0 y)))) ∧
  (∀ y : R3, ∀ i j : Fin 3,
    PP (IH (U F0 y)) (LQ q RR y i (Ahi j (U F0 y))) =
      PP (Ahi j (U F0 y)) (JL (e i (T y) (U F0 y)))) ∧
  (∀ y : R3, ∀ i j : Fin 3,
    PP (IH (U F0 y)) (LQ q RR y i (referenceHighWeightedHorizontalAction g L q RR (U F0) y j)) =
      PP (referenceHighWeightedHorizontalAction g L q RR (U F0) y j) (JL (e i (T y) (U F0 y))))

attribute [local irreducible] referencePhysicalDensityOperator referenceDensityCovariantSecondAction
  referenceHighDensityFirstAction referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceNativeMovingAdjointParametricCorrection referenceNativeMovingAdjointHighMixedCorrection
  referenceMetricGramFrame referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  referenceRadiusHorizontalLogDerivative sphereSobolevInclusionL sphereSobolevAngularCoordinateTransposeL
  referenceRadialEndpointInvertibleLocus normalizedSecondDriftFrameJoint


attribute [local irreducible] higherSInput higherSRaisingInput higherSReferenceInput
  higherSLift HigherSRoomAt higherSParam canonicalHigh

/-- Signed identities from room + value identity + reverse pairing (all actual, discharged in
the final theorem). Off `tsupport F0` both sides vanish. -/
theorem higherSSignedTransferAt_of_room (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (hRoom : ∀ x ∈ TS F0, Room δ x)
    (hVal : ∀ j : Fin 3, ∀ x : R3, IH (V hreg δ0 W F0 j x) = MQ q RR x j (U F0 x))
    (e : Fin 3 → Tpar → Hi →L[ℝ] Half)
    (hPair : ∀ i : Fin 3, ∀ x ∈ TS F0, ∀ u v : Hi,
      PP (EH i (T x) u) (JL (IH v)) = PP (IH u) (JL (e i (T x) v)))
    (g2 : MatrixField) :
    HigherSSignedTransferAt hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q g2 e F0 := by
  have hU0 (y : R3) (hy : y ∉ TS F0) : U F0 y = 0 :=
    higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 y hy
  have hTr (y : R3) (hy : y ∈ TS F0) (i : Fin 3) (wv v : Hi) :
      PP (IH v) (LQ q RR y i (IH wv)) = PP (IH wv) (JL (e i (T y) v)) :=
    lowerQuotient_transfer hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ y (hRoom y hy) e (fun i u v => hPair i y hy u v) i wv v
  refine ⟨fun y i j => ?_, fun y i j => ?_, fun y i j => ?_⟩
  · by_cases hy : y ∈ TS F0
    · exact pp_transfer_value (V hreg δ0 W F0 j y) (MQ q RR y j (U F0 y))
        (IH (U F0 y)) (LQ q RR y i) (JL (e i (T y) (U F0 y)))
        (hVal j y) (hTr y hy i (V hreg δ0 W F0 j y) (U F0 y))
    · rw [hU0 y hy]
      exact pp_zero_image_transfer (MQ q RR y j) (LQ q RR y i) (e i (T y))
  · by_cases hy : y ∈ TS F0
    · exact pp_transfer_value (UA F0 j y) (Ahi j (U F0 y))
        (IH (U F0 y)) (LQ q RR y i) (JL (e i (T y) (U F0 y)))
        (raisingInput_inclusion hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
          δr Ar p hδr hAr q F0 j y) (hTr y hy i (UA F0 j y) (U F0 y))
    · rw [hU0 y hy]
      exact pp_zero_image_transfer (Ahi j) (LQ q RR y i) (e i (T y))
  · by_cases hy : y ∈ TS F0
    · exact pp_transfer_value (UD F0 j y)
        (referenceHighWeightedHorizontalAction g L q RR (U F0) y j)
        (IH (U F0 y)) (LQ q RR y i) (JL (e i (T y) (U F0 y)))
        (referenceInput_inclusion hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
          δr Ar p hδr hAr q F0 j y) (hTr y hy i (UD F0 j y) (U F0 y))
    · have hW0 : referenceHighWeightedHorizontalAction g L q RR (U F0) y j = 0 :=
        referenceHighWeightedHorizontalAction_eq_zero_of_eventually g L q RR (U F0) y j
          (higherSInput_eventually_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
            δr Ar p hδr hAr q F0 y hy)
      exact pp_zero_inputs (U F0 y)
        (referenceHighWeightedHorizontalAction g L q RR (U F0) y j)
        (LQ q RR y i) (e i (T y)) (hU0 y hy) hW0

/-- Typed modular consumer of the native output record. The global witness
producer below does not unfold this large record around chosen coefficients. -/
lemma higherSSignedTransferAt_of_output (hreg : FixedDirichletRegularity)
    (hq : q ∈ Icc (0 : ℝ) 1) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (hRoom : ∀ x ∈ TS F0, Room δ x)
    (e : Fin 3 → Tpar → Hi →L[ℝ] Half)
    (hPair : ∀ i : Fin 3, ∀ x ∈ TS F0, ∀ u v : Hi,
      PP (EH i (T x) u) (JL (IH v)) = PP (IH u) (JL (e i (T x) v)))
    (g2 : MatrixField)
    (hOut : HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F0) :
    HigherSSignedTransferAt hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q g2 e F0 := by
  unfold HigherSOutputConclusions at hOut
  exact higherSSignedTransferAt_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg hq δ0 W δ F0 hRoom hOut.1 e hPair g2

end Profile

attribute [local irreducible] HigherSOutputConclusions HigherSSignedTransferAt

/-! ## 3. FINAL actual theorem: room and reverse family BEFORE every profile parameter -/

/-- Room witnesses `δ0, W, δ` and the genuine reverse family `e` (germs AND pairing from one
witness) are chosen from the original geometry only. Then for EVERY radius profile, every
`q ∈ [0,1]` and every finite input whose profile map lands in `ParamRoom δ` on its support:
the formation output conclusions and the three signed transfer identities hold. -/
theorem higherS_signed_transfer_actual (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∃ W : CoeffRoom δ0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
    ∃ e : Fin 3 → Tpar → Hi →L[ℝ] Half,
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (e i) t) ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u v : Hi,
        PP (EH i t u) (JL (IH v)) = PP (IH u) (JL (e i t v))) ∧
      ∀ (δr Ar : ℝ) (hδr : 0 < δr) (hAr : 0 < Ar) (p : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
        ∀ F0 : smoothCompactFiniteSphereCore hO hD,
          (∀ x ∈ tsupport (F0 : R3 → SphereL2), higherSParam L δr Ar p q x ∈ ParamRoom δ) →
          HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
              δr Ar p hδr hAr q hreg δ0 W g2 F0 ∧
          HigherSSignedTransferAt hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
            δr Ar p q g2 e F0 := by
  let hC := higherSUniformFormationContract_proof hF hO hD g L y0 Φ B ε C ρ H a w hData hg
    hcalc τ0 hreg hKernel g2 hg2
  have hCF : HigherSUniformFormationContract hF hO hD g L y0 Φ B ε C ρ H a w hData hg
      hcalc τ0 hreg g2 := hC
  unfold HigherSUniformFormationContract at hCF
  let δ0 := Classical.choose hCF
  have hC0 := Classical.choose_spec hCF
  have hδ0 : 0 < δ0 := hC0.1
  let W := Classical.choose hC0.2
  have hCW := Classical.choose_spec hC0.2
  let δF := Classical.choose hCW
  have hCF0 := Classical.choose_spec hCW
  have hδF : 0 < δF := hCF0.1
  have hδFρ : δF ≤ ρ := hCF0.2.2.1
  have hΩF := hCF0.2.2.2.1
  have hAll := hCF0.2.2.2.2
  obtain ⟨δE, hδE, e, hSmE, hPairE⟩ := exists_actual_reverse_family hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 hreg
  let hRG := exists_finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  let lam := Classical.choose hRG
  have hRG1 := Classical.choose_spec hRG
  let Lam := Classical.choose hRG1
  have hRG2 := Classical.choose_spec hRG1
  let dG := Classical.choose hRG2
  have hFin := Classical.choose_spec hRG2
  have hdG : 0 < dG := hFin.2.1
  have hJac : ∀ z ∈ commonRoom y0 ρ dG, ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible :=
    fun z hz => (hFin.2.2.2 z hz).2.2.2.2
  let δ := min δF (min dG δE)
  have hδ : 0 < δ := lt_min hδF (lt_min hdG hδE)
  have hδF' : δ ≤ δF := min_le_left _ _
  have hδG : δ ≤ dG := (min_le_right _ _).trans (min_le_left _ _)
  have hδE' : δ ≤ δE := (min_le_right _ _).trans (min_le_right _ _)
  have hSm : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (e i) t :=
    fun i t ht => hSmE i t (paramRoom_mono y0 ρ hδE' ht)
  have hPair : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u v : Hi,
      PP (EH i t u) (JL (IH v)) = PP (IH u) (JL (e i t v)) :=
    fun i t ht u v => hPairE i t (paramRoom_mono y0 ρ hδE' ht) u v
  refine ⟨δ0, hδ0, W, δ, hδ, hδF'.trans hδFρ, e, hSm, hPair, ?_⟩
  intro δr Ar hδr hAr p q hq F0 hT
  have hTF : ∀ x ∈ tsupport (F0 : R3 → SphereL2), higherSParam L δr Ar p q x ∈ ParamRoom δF :=
    fun x hx => paramRoom_mono y0 ρ hδF' (hT x hx)
  have hOut := hAll δr Ar hδr hAr p q hq F0 hTF
  refine ⟨hOut, ?_⟩
  have hRoom : ∀ x ∈ tsupport (F0 : R3 → SphereL2),
      HigherSRoomAt hF hO hD g L y0 Φ B ε C ρ H a w hData hcalc τ0 δr Ar p q δ x :=
    fun x hx => higherSRoomAt_of_mem_paramRoom hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q δF δ dG hδF' hδG hΩF hJac x (hT x hx)
  exact higherSSignedTransferAt_of_output hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg hq δ0 W δ F0 hRoom e
    (fun i x hx u v => hPair i _ (hT x hx) u v) g2 hOut

end Actual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSSigned
