import Calderon.ActualHigherSAngularAdjoint
import Calderon.ActualHigherSSecondAdjoint
import Calderon.ActualHigherSPhysicalIntegratedConsumer
import Calderon.ActualHigherSCoefficientBounds

/-! The original S block in direct physical form. Proved here:
* §2 the original angularS block `higherSAngularHalf` against its own finite input: exact
  global pointwise identity via `raising_pairing_lowering` (outer raising) and one `Cm.pivot`
  (`EH_i UA_j`), both `Q_ij` orders literal; global bound `≤ K R ‖UF‖²`; density-integrated
  diagonal bound with integrabilities; constants `δ, Cm, CE, CrE, CL, CA` before `g2`,
  `K` after `g2` and before every profile/input/point.
* §3 secondS rows: exact pointwise E-UD pivot row and the exact integrated D-row Green identity
  (outer weighted `D` moved by `scalar_weighted_green_combined`, `v = IH VF_j`).
The final secondS integrated bound, the full S budget and the small form are not part of this
file. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalForm
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
  ActualHorizontalNormBridge ActualHigherSIntegratedPairing ActualHigherSPhysicalPairing
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-! ## 0. Generic estimates (no actual premise) -/

private lemma compact_family_bound {α E ι : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E] [Fintype ι] (K : Set α) (hK : IsCompact K)
    (f : ι → α → E) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i : ι, ∀ x ∈ K, ‖f i x‖ ≤ M := by
  classical
  choose C hC using fun i : ι => hK.exists_bound_of_continuousOn (hf i)
  have hs0 : 0 ≤ ∑ i : ι, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1+∑ i : ι, |C i|,by linarith,?_⟩
  intro i x hx
  apply (hC i x hx).trans
  calc
    C i ≤ |C i| := le_abs_self _
    _ ≤ ∑ j : ι, |C j| := Finset.single_le_sum (f := fun j : ι => |C j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ 1+∑ j : ι, |C j| := by linarith

private lemma abs_add_le' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  simpa only [Real.norm_eq_abs] using norm_add_le x y

/-- Cauchy–Schwarz with two actual operator norms and the actual CLM norm of `K`. -/
private lemma abs_inner_clm_comp_le {H1 H2 E : Type*}
    [NormedAddCommGroup H1] [NormedSpace ℝ H1] [NormedAddCommGroup H2] [NormedSpace ℝ H2]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : H2 →L[ℝ] E) (A B : H1 →L[ℝ] H2) (u v : H1) (CA CB : ℝ)
    (hA : ‖A‖ ≤ CA) (hB : ‖B‖ ≤ CB) :
    |⟪K (A u), K (B v)⟫_ℝ| ≤ ‖K‖^2 * CA * CB * (‖u‖ * ‖v‖) := by
  have hCA : 0 ≤ CA := (norm_nonneg A).trans hA
  have hCB : 0 ≤ CB := (norm_nonneg B).trans hB
  have h1 : ‖K (A u)‖ ≤ ‖K‖ * (CA * ‖u‖) :=
    (K.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg u))) (norm_nonneg K))
  have h2 : ‖K (B v)‖ ≤ ‖K‖ * (CB * ‖v‖) :=
    (K.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((B.le_opNorm v).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg v))) (norm_nonneg K))
  calc |⟪K (A u), K (B v)⟫_ℝ| ≤ ‖K (A u)‖ * ‖K (B v)‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖K‖ * (CA * ‖u‖)) * (‖K‖ * (CB * ‖v‖)) :=
        mul_le_mul h1 h2 (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (mul_nonneg hCA (norm_nonneg _)))
    _ = ‖K‖^2 * CA * CB * (‖u‖ * ‖v‖) := by ring

/-- Signed `3×3` weighted sum with a nonnegative radius factor `r` (first power). -/
private lemma abs_weighted_double_sum_le_one (r : ℝ) (hr : 0 ≤ r) (Q c : Fin 3 → Fin 3 → ℝ)
    (CQ M : ℝ) (hCQ : 0 ≤ CQ) (hQ : ∀ i j, |Q i j| ≤ CQ) (hc : ∀ i j, |c i j| ≤ M) :
    |r * ∑ i : Fin 3, ∑ j : Fin 3, Q i j * c i j| ≤ 9 * CQ * M * r := by
  have hterm : ∀ i j, |Q i j * c i j| ≤ CQ * M := fun i j => by
    rw [abs_mul]
    exact mul_le_mul (hQ i j) (hc i j) (abs_nonneg _) hCQ
  have hsum : |∑ i : Fin 3, ∑ j : Fin 3, Q i j * c i j| ≤ 9 * (CQ * M) := by
    calc |∑ i : Fin 3, ∑ j : Fin 3, Q i j * c i j|
        ≤ ∑ i : Fin 3, |∑ j : Fin 3, Q i j * c i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |Q i j * c i j| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, CQ * M :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = 9 * (CQ * M) := by simp only [Fin.sum_univ_three]; ring
  rw [abs_mul, abs_of_nonneg hr]
  calc r * |∑ i : Fin 3, ∑ j : Fin 3, Q i j * c i j| ≤ r * (9 * (CQ * M)) :=
        mul_le_mul_of_nonneg_left hsum hr
    _ = 9 * CQ * M * r := by ring

/-! ## 1. Actual setting -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "UA" => ActualHigherSFormation.higherSRaisingInput hF hO hD
local notation "AH" => (fun i : Fin 3 =>
  (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i : Hi →L[ℝ] Half))
local notation "AL" => loweringHigh hF hO hD
local notation "FA" => ActualHigherSFormation.higherSAngularHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Room membership of the profile point yields `q ∈ [0,1]` and `x ∈ closedBall y0 ρ`. -/
private lemma paramRoom_q_ball (δr Ar : ℝ) (p : ℕ) (q δ : ℝ) (x : R3)
    (ht : (Tq δr Ar p q) x ∈ ParamRoom δ) : q ∈ Icc (0 : ℝ) 1 ∧ x ∈ closedBall y0 ρ := by
  have hc : ((q,(x,referenceRadius δr Ar p L x)) : Pphys) ∈ commonRoom y0 ρ δ := ht.1
  first
    | exact ⟨hc.1, hc.2.1⟩
    | (simp only [commonRoom, Set.mem_prod] at hc; exact ⟨hc.1, hc.2.1⟩)

/-- Compact-room operator caps of `EH`/`eH`, from `Cm.germHigh`, `Cm.rev.germHigh` (before `g2`). -/
theorem exists_room_E_operator_bounds (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    ∃ CE CrE : ℝ, 1 ≤ CE ∧ 1 ≤ CrE ∧
      ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE := by
  have hK : IsCompact (ParamRoom δ) :=
    (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  obtain ⟨CE, hCE1, hCE⟩ := compact_family_bound (ParamRoom δ) hK (fun i : Fin 3 => EH i)
    (fun i t ht => (Cm.germHigh i t ht).continuousAt.continuousWithinAt)
  obtain ⟨CrE, hCrE1, hCrE⟩ := compact_family_bound (ParamRoom δ) hK (fun i : Fin 3 => eH i)
    (fun i t ht => (Cm.rev.germHigh i t ht).continuousAt.continuousWithinAt)
  exact ⟨CE, CrE, hCE1, hCrE1, fun i t ht => ⟨hCE i t ht, hCrE i t ht⟩⟩

/-- Actual fixed raising/lowering CLM norms (no room, no `g2`, no profile). -/
lemma exists_angular_clm_bounds :
    ∃ CL CA : ℝ, 0 ≤ CL ∧ 0 ≤ CA ∧ ∀ i : Fin 3, ‖AL i‖ ≤ CL ∧ ‖AH i‖ ≤ CA :=
  ⟨∑ k : Fin 3, ‖AL k‖, ∑ k : Fin 3, ‖AH k‖,
    Finset.sum_nonneg (fun k _ => ContinuousLinearMap.opNorm_nonneg (AL k)), Finset.sum_nonneg (fun k _ => ContinuousLinearMap.opNorm_nonneg (AH k)),
    fun i => ⟨Finset.single_le_sum (f := fun k : Fin 3 => ‖AL k‖) (fun k _ => ContinuousLinearMap.opNorm_nonneg (AL k))
      (Finset.mem_univ i),
      Finset.single_le_sum (f := fun k : Fin 3 => ‖AH k‖) (fun k _ => ContinuousLinearMap.opNorm_nonneg (AH k))
      (Finset.mem_univ i)⟩⟩

/-! ## 2. Original angularS: direct physical form -/

/-- One angular row: outer raising by `raising_pairing_lowering`, `EH_i UA_j` by one `Cm.pivot`. -/
theorem angular_row (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (t : Tpar) (ht : t ∈ ParamRoom δ) (i j : Fin 3)
    (u vf ua : Hi) (hvf : IH vf = EH j t u) (hua : IH ua = AH j u) :
    ⟪KL (IH u), KL (AH i vf + EH i t ua)⟫_ℝ =
      ⟪KL (AL i u), KL (EH j t u)⟫_ℝ + ⟪KL (AH j u), KL (eH i t u)⟫_ℝ := by
  have hP := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
  have h1 : ⟪KL (IH u), KL (AH i vf)⟫_ℝ = ⟪KL (AL i u), KL (EH j t u)⟫_ℝ :=
    calc ⟪KL (IH u), KL (AH i vf)⟫_ℝ = PP (IH u) (JL (AH i vf)) := (hP _ _).symm
      _ = PP (AL i u) (JL (IH vf)) :=
          ActualHigherSAngularAdjoint.raising_pairing_lowering hF hO hD i u vf
      _ = PP (AL i u) (JL (EH j t u)) :=
          congrArg (fun z : Half => PP (AL i u) (JL z)) hvf
      _ = ⟪KL (AL i u), KL (EH j t u)⟫_ℝ := hP _ _
  have h2 : ⟪KL (IH u), KL (EH i t ua)⟫_ℝ = ⟪KL (AH j u), KL (eH i t u)⟫_ℝ :=
    calc ⟪KL (IH u), KL (EH i t ua)⟫_ℝ = ⟪KL (EH i t ua), KL (IH u)⟫_ℝ := real_inner_comm _ _
      _ = PP (EH i t ua) (JL (IH u)) := (hP _ _).symm
      _ = PP (IH ua) (JL (eH i t u)) := Cm.pivot i t ht ua u
      _ = PP (AH j u) (JL (eH i t u)) :=
          congrArg (fun z : Half => PP z (JL (eH i t u))) hua
      _ = ⟪KL (AH j u), KL (eH i t u)⟫_ℝ := hP _ _
  calc
    _ = ⟪KL (IH u), KL (AH i vf)⟫_ℝ + ⟪KL (IH u), KL (EH i t ua)⟫_ℝ := by
      simp only [map_add,inner_add_right]
    _ = _ := congrArg₂ (fun a b : ℝ => a+b) h1 h2

/-- Exact physical angular density, ORIGINAL `Q_ij` order:
`R Σ_ij Q_ij (<KL(lowering_i U), KL(EH_j U)> + <KL(A_j U), KL(eH_i U)>)`. -/
def angularGram (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  referenceRadius δr Ar p L x * ∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
      (⟪KL (AL i (Uin F0 x)), KL (EH j ((Tq δr Ar p q) x) (Uin F0 x))⟫_ℝ +
        ⟪KL (AH j (Uin F0 x)), KL (eH i ((Tq δr Ar p q) x) (Uin F0 x))⟫_ℝ)
local notation "AG" => angularGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- GLOBAL exact pointwise identity for the literal angularS against its own input. -/
theorem pointwise_angular_identity (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ = AG g2 δr Ar p q F0 x := by
  have hFx : F0.val x = KL (IH (Uin F0 x)) :=
    (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD F0 x).symm
  have hrow : ∀ i j : Fin 3,
      ⟪KL (IH (Uin F0 x)), KL (AH i (VF δr Ar p q hreg δ0 W F0 j x) +
          EH i ((Tq δr Ar p q) x) (UA F0 j x))⟫_ℝ =
        ⟪KL (AL i (Uin F0 x)), KL (EH j ((Tq δr Ar p q) x) (Uin F0 x))⟫_ℝ +
          ⟪KL (AH j (Uin F0 x)), KL (eH i ((Tq δr Ar p q) x) (Uin F0 x))⟫_ℝ := by
    intro i j
    by_cases hx : x ∈ TS F0
    · exact angular_row g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
        _ (hTF x hx) i j (Uin F0 x) (VF δr Ar p q hreg δ0 W F0 j x) (UA F0 j x)
        (ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion g L y0 Φ B ε C ρ H a w hData hg
          hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hTF j x)
        (ActualHigherSAngularAdjoint.raisingInput_inclusion hF hO hD F0 j x)
    · have hV := ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
        hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W F0 j x hx
      have hU := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
        hData hg hcalc τ0 δr Ar p hδr hAr q F0 x hx
      have hA := ActualHigherSFormation.higherSRaisingInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
        hData hg hcalc τ0 δr Ar p hδr hAr q F0 j x hx
      simp only [hV, hU, hA, map_zero, add_zero, inner_zero_left, inner_zero_right]
  have hFwd : FA δr Ar p q hreg δ0 W g2 F0 x = referenceRadius δr Ar p L x •
      (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
        (AH i (VF δr Ar p q hreg δ0 W F0 j x) + EH i ((Tq δr Ar p q) x) (UA F0 j x))) := by
    unfold ActualHigherSFormation.higherSAngularHalf
    rfl
  rw [hFx, hFwd]
  unfold angularGram
  simp only [map_smul, map_sum, real_inner_smul_right, inner_sum, hrow]

/-- GLOBAL pointwise bound `≤ K R ‖UF‖²` (internal adapter; constants discharged in §2 final). -/
theorem pointwise_angular_bound_of_bounds (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ CL CA : ℝ) (hCQ0 : 0 ≤ CQ)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hA : ∀ i : Fin 3, ‖AL i‖ ≤ CL ∧ ‖AH i‖ ≤ CA)
    (hQ : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
      |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ) (x : R3) :
    |⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
      9 * CQ * (‖KL‖^2 * CL * CE + ‖KL‖^2 * CA * CrE) * referenceRadius δr Ar p L x *
        (‖Uin F0 x‖ * ‖Uin F0 x‖) := by
  rw [pointwise_angular_identity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
    g2 δr Ar p hδr hAr q F0 hTF x]
  unfold angularGram
  by_cases hx : x ∈ TS F0
  · have ht := hTF x hx
    obtain ⟨hq, hxb⟩ := paramRoom_q_ball L y0 ρ δr Ar p q δ x ht
    have hc : ∀ i j : Fin 3,
        |⟪KL (AL i (Uin F0 x)), KL (EH j ((Tq δr Ar p q) x) (Uin F0 x))⟫_ℝ +
          ⟪KL (AH j (Uin F0 x)), KL (eH i ((Tq δr Ar p q) x) (Uin F0 x))⟫_ℝ| ≤
          ‖KL‖^2 * CL * CE * (‖Uin F0 x‖ * ‖Uin F0 x‖) +
            ‖KL‖^2 * CA * CrE * (‖Uin F0 x‖ * ‖Uin F0 x‖) := fun i j =>
      (abs_add_le' _ _).trans (add_le_add
        (abs_inner_clm_comp_le KL (AL i) (EH j ((Tq δr Ar p q) x)) (Uin F0 x) (Uin F0 x)
          CL CE (hA i).1 (hE j _ ht).1)
        (abs_inner_clm_comp_le KL (AH j) (eH i ((Tq δr Ar p q) x)) (Uin F0 x) (Uin F0 x)
          CA CrE (hA j).2 (hE i _ ht).2))
    have hR : 0 ≤ referenceRadius δr Ar p L x := (referenceRadius_pos δr Ar p L x hδr hAr).le
    have h := abs_weighted_double_sum_le_one (referenceRadius δr Ar p L x) hR
      (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
      (fun i j => ⟪KL (AL i (Uin F0 x)), KL (EH j ((Tq δr Ar p q) x) (Uin F0 x))⟫_ℝ +
          ⟪KL (AH j (Uin F0 x)), KL (eH i ((Tq δr Ar p q) x) (Uin F0 x))⟫_ℝ)
      CQ (‖KL‖^2 * CL * CE * (‖Uin F0 x‖ * ‖Uin F0 x‖) +
            ‖KL‖^2 * CA * CrE * (‖Uin F0 x‖ * ‖Uin F0 x‖)) hCQ0
      (fun i j => hQ q hq x hxb i j) hc
    exact h.trans_eq (by ring)
  · have hU := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
      hData hg hcalc τ0 δr Ar p hδr hAr q F0 x hx
    simp [hU]

/-- Density-integrated diagonal angular bound with both actual integrabilities. -/
theorem integrated_angular_bound_of_bounds (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ CL CA : ℝ) (hCQ0 : 0 ≤ CQ)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hA : ∀ i : Fin 3, ‖AL i‖ ≤ CL ∧ ‖AH i‖ ≤ CA)
    (hQ : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
      |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ) :
    Integrable (fun x => referenceDensityFamily g L (q,x) *
      ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x) *
      (referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖))) ∧
    |∫ x, referenceDensityFamily g L (q,x) * ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
      (9 * CQ * (‖KL‖^2 * CL * CE + ‖KL‖^2 * CA * CrE)) *
        ∫ x, referenceDensityFamily g L (q,x) *
          (referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖)) := by
  have hbd := pointwise_angular_bound_of_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 hTF CE CrE CQ CL CA hCQ0 hE hA hQ
  have hInt := (ActualHigherSAngularAdjoint.integrated_angular_physical_adjoint g L y0 Φ B ε C ρ
    H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 F0 hTF hTF).1
  have hρ : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hR : Continuous (referenceRadius δr Ar p L) :=
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr).continuous
  have hUF : Continuous (Uin F0) := (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0).continuous
  have hU0 : ∀ z ∉ TS F0, Uin F0 z = 0 := fun z hz =>
    ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 z hz
  have hWi : Integrable (fun x => referenceDensityFamily g L (q,x) *
      (referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖))) :=
    (hρ.mul (hR.mul (hUF.norm.mul hUF.norm))).integrable_of_hasCompactSupport
      (ActualCommonFirstWordQuadraticAdjoint.hasCompactSupport_of_eq_zero_off hO hD F0 _
        (fun z hz => by simp [hU0 z hz]))
  have hpt : ∀ x : R3, ‖referenceDensityFamily g L (q,x) *
      ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ‖ ≤
      (9 * CQ * (‖KL‖^2 * CL * CE + ‖KL‖^2 * CA * CrE)) * (referenceDensityFamily g L (q,x) *
        (referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖))) := by
    intro x
    have hμ := referenceDensityFamily_pos g hg L (q,x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hμ]
    calc referenceDensityFamily g L (q,x) * |⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ|
        ≤ referenceDensityFamily g L (q,x) *
            (9 * CQ * (‖KL‖^2 * CL * CE + ‖KL‖^2 * CA * CrE) * referenceRadius δr Ar p L x *
              (‖Uin F0 x‖ * ‖Uin F0 x‖)) := mul_le_mul_of_nonneg_left (hbd x) hμ.le
      _ = _ := by ring
  have h := norm_integral_le_of_norm_le
    (hWi.const_mul (9 * CQ * (‖KL‖^2 * CL * CE + ‖KL‖^2 * CA * CrE))) (ae_of_all _ hpt)
  rw [integral_const_mul, Real.norm_eq_abs] at h
  exact ⟨hInt, hWi, h⟩

/- Bounded proof boundaries for room/cap selection and fixed-metric specialization. -/
private structure AngularRoomBounds (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) where
  δ : ℝ
  room : CRoom hreg δ0 W δ
  CE : ℝ
  CrE : ℝ
  CL : ℝ
  CA : ℝ
  CEone : 1 ≤ CE
  CrEone : 1 ≤ CrE
  CLnonneg : 0 ≤ CL
  CAnonneg : 0 ≤ CA
  Ecap : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE
  Acap : ∀ i : Fin 3, ‖AL i‖ ≤ CL ∧ ‖AH i‖ ≤ CA

private theorem exists_angular_room_bounds (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    Nonempty (AngularRoomBounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W) := by
  obtain ⟨δ,Cm⟩ := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  obtain ⟨CE,CrE,hCE,hCrE,hE⟩ := exists_room_E_operator_bounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
  obtain ⟨CL,CA,hCL,hCA,hA⟩ := exists_angular_clm_bounds hF hO hD
  exact ⟨{
    δ := δ
    room := Cm
    CE := CE
    CrE := CrE
    CL := CL
    CA := CA
    CEone := hCE
    CrEone := hCrE
    CLnonneg := hCL
    CAnonneg := hCA
    Ecap := hE
    Acap := hA
  }⟩

private def OriginalAngularFormContract (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (g2 : MatrixField) (K : ℝ) : Prop :=
        ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar, ∀ q : ℝ,
        ∀ F0 : smoothCompactFiniteSphereCore hO hD,
          (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
          (∀ x : R3, |⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
            K * referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖)) ∧
          Integrable (fun x => referenceDensityFamily g L (q,x) *
            ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ) ∧
          Integrable (fun x => referenceDensityFamily g L (q,x) *
            (referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖))) ∧
          |∫ x, referenceDensityFamily g L (q,x) *
              ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
            K * ∫ x, referenceDensityFamily g L (q,x) *
              (referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖))

private theorem exists_angular_form_given_caps (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (CE CrE CL CA : ℝ) (hCE : 1 ≤ CE) (hCrE : 1 ≤ CrE) (hCL : 0 ≤ CL) (hCA : 0 ≤ CA)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hA : ∀ i : Fin 3, ‖AL i‖ ≤ CL ∧ ‖AH i‖ ≤ CA)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ K : ℝ, 0 ≤ K ∧ OriginalAngularFormContract
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ g2 K := by
  obtain ⟨CQ, hCQ, hQF⟩ := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound
    (g := g) (L := L) (y0 := y0) (ρ := ρ) (hg := hg) g2 hg2
  have hQ : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
      |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ :=
    fun q hq x hx i j => (hQF q hq x hx i j).1
  have hCQ0 : 0 ≤ CQ := zero_le_one.trans hCQ
  have hCE0 : 0 ≤ CE := zero_le_one.trans hCE
  have hCrE0 : 0 ≤ CrE := zero_le_one.trans hCrE
  have hK0 : 0 ≤ 9 * CQ * (‖KL‖^2 * CL * CE + ‖KL‖^2 * CA * CrE) :=
    mul_nonneg (mul_nonneg (by norm_num) hCQ0)
      (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hCL) hCE0)
        (mul_nonneg (mul_nonneg (sq_nonneg _) hCA) hCrE0))
  refine ⟨9 * CQ * (‖KL‖^2 * CL * CE + ‖KL‖^2 * CA * CrE), hK0,
    fun δr Ar p hδr hAr q F0 hTF => ?_⟩
  have hbd := pointwise_angular_bound_of_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 hTF CE CrE CQ CL CA hCQ0 hE hA hQ
  have hI := integrated_angular_bound_of_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 hTF CE CrE CQ CL CA hCQ0 hE hA hQ
  exact ⟨hbd, hI.1, hI.2.1, hI.2.2⟩


/-- FINAL original angularS form on ANY retained `W`: `δ, Cm, CE, CrE, CL, CA` before `g2`;
`K` after a fixed admissible `g2` and BEFORE every profile, input and point. -/
theorem exists_retained_original_angular_form (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Cm : CRoom hreg δ0 W δ, ∃ CE CrE CL CA : ℝ,
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE) ∧
      (∀ i : Fin 3, ‖AL i‖ ≤ CL ∧ ‖AH i‖ ≤ CA) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ∃ K : ℝ, 0 ≤ K ∧
        ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar, ∀ q : ℝ,
        ∀ F0 : smoothCompactFiniteSphereCore hO hD,
          (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
          (∀ x : R3, |⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
            K * referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖)) ∧
          Integrable (fun x => referenceDensityFamily g L (q,x) *
            ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ) ∧
          Integrable (fun x => referenceDensityFamily g L (q,x) *
            (referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖))) ∧
          |∫ x, referenceDensityFamily g L (q,x) *
              ⟪F0.val x, KL (FA δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
            K * ∫ x, referenceDensityFamily g L (q,x) *
              (referenceRadius δr Ar p L x * (‖Uin F0 x‖ * ‖Uin F0 x‖)) := by
  obtain ⟨r⟩ := exists_angular_room_bounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨r.δ,r.room.rev.pos,r.room,r.CE,r.CrE,r.CL,r.CA,r.Ecap,r.Acap,?_⟩
  intro g2 hg2
  exact exists_angular_form_given_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W r.δ r.room
    r.CE r.CrE r.CL r.CA r.CEone r.CrEone r.CLnonneg r.CAnonneg r.Ecap r.Acap g2 hg2

/-! ## 3. Original secondS: exact row identities BEFORE estimating -/

/-- E-UD row: one `Cm.pivot`; `E` is moved onto the input `U`, never onto `UD`. -/
theorem second_EUD_row (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (t : Tpar) (ht : t ∈ ParamRoom δ) (i : Fin 3)
    (u ud : Hi) (d : Half) (hd : IH ud = d) :
    ⟪KL (IH u), KL (EH i t ud)⟫_ℝ = ⟪KL d, KL (eH i t u)⟫_ℝ := by
  have hP := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
  calc ⟪KL (IH u), KL (EH i t ud)⟫_ℝ = ⟪KL (EH i t ud), KL (IH u)⟫_ℝ := real_inner_comm _ _
    _ = PP (EH i t ud) (JL (IH u)) := (hP _ _).symm
    _ = PP (IH ud) (JL (eH i t u)) := Cm.pivot i t ht ud u
    _ = PP d (JL (eH i t u)) := by rw [hd]
    _ = ⟪KL d, KL (eH i t u)⟫_ℝ := hP _ _

/-- GLOBAL pointwise E-UD row of the literal secondS: `<F, KL(EH_i UD_j)> = <KL(D_j U), KL(eH_i U)>`. -/
theorem pointwise_second_EUD_row (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (i j : Fin 3) (x : R3) :
    ⟪F0.val x, KL (EH i ((Tq δr Ar p q) x)
        (ActualHigherSFormation.higherSReferenceInput hO hD g L hg δr Ar p hδr hAr q F0 j x))⟫_ℝ =
      ⟪KL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x j),
        KL (eH i ((Tq δr Ar p q) x) (Uin F0 x))⟫_ℝ := by
  have hFx : F0.val x = KL (IH (Uin F0 x)) :=
    (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD F0 x).symm
  rw [hFx]
  by_cases hx : x ∈ TS F0
  · exact second_EUD_row g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
      _ (hTF x hx) i (Uin F0 x)
      (ActualHigherSFormation.higherSReferenceInput hO hD g L hg δr Ar p hδr hAr q F0 j x) _
      (ActualHigherSSecondAdjoint.referenceInput_inclusion hO hD g hg L q δr Ar p hδr hAr F0 j x)
  · have hU := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
      hData hg hcalc τ0 δr Ar p hδr hAr q F0 x hx
    simp only [hU, map_zero, inner_zero_left, inner_zero_right]

/-- Exact D-row Green identity of the literal secondS, any smooth scalar weight `a'`
(the row uses `a' = R² Q_ij`). Outer weighted `D_i` is moved onto `U`; `v = IH VF_j` stays in
Half, so no `Hi` norm of `VF_j` and no derivative of `E` appears. -/
theorem green_second_D_row (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (a' : R3 → ℝ) (ha : ContDiff ℝ ∞ a') (i j : Fin 3) :
    (∫ y, referenceDensityFamily g L (q,y) * a' y *
        PP (IH (Uin F0 y)) (JL (referenceHighWeightedHorizontalAction g L q
          (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i))) =
      -(∫ y, referenceDensityFamily g L (q,y) * a' y *
          PP (IH (VF δr Ar p q hreg δ0 W F0 j y)) (JL (referenceHighWeightedHorizontalAction g L q
            (referenceRadius δr Ar p L) (Uin F0) y i))) +
        2 * (∫ y, referenceDensityFamily g L (q,y) *
            referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) y i * a' y *
              PP (IH (VF δr Ar p q hreg δ0 W F0 j y))
                (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (Uin F0 y)))) -
        (∫ y, (a' y * referenceWeightedFrameDivergence g L q i y +
            referenceDensityFamily g L (q,y) * fderiv ℝ a' y (referenceMetricGramFrame g L (q,y) i)) *
          PP (IH (Uin F0 y)) (JL (IH (VF δr Ar p q hreg δ0 W F0 j y)))) := by
  have hV := ActualCommonFirstWordQuadraticAdjoint.contDiff_fwdLift g L y0 Φ B ε C ρ H a w hData
    hg hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hTF j
  have hRR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hpt : ∀ y : R3, JL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
      (VF δr Ar p q hreg δ0 W F0 j) y i) =
      referenceLowerWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
        (fun z => IH (VF δr Ar p q hreg δ0 W F0 j z)) y i := fun y =>
    ActualHigherSFormation.referenceWeightedHorizontalAction_inclusion g L q
      (referenceRadius δr Ar p L) (VF δr Ar p q hreg δ0 W F0 j) y i
      ((hV.differentiable (by simp)) y)
  have hvc : HasCompactSupport (fun z => IH (VF δr Ar p q hreg δ0 W F0 j z)) :=
    ActualCommonFirstWordQuadraticAdjoint.hasCompactSupport_of_eq_zero_off hO hD F0 _
      (fun z hz => by
        simp only [ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
          hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W F0 j z hz, map_zero])
  simp only [hpt]
  exact ActualHigherSPhysicalIntegratedConsumer.scalar_weighted_green_combined g L q
    (referenceRadius δr Ar p L) hg hRR (fun y => (referenceRadius_pos δr Ar p L y hδr hAr).ne')
    (Uin F0) (fun z => IH (VF δr Ar p q hreg δ0 W F0 j z)) a'
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0) ((IH).contDiff.comp hV) hvc ha i

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalForm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalForm.exists_retained_original_angular_form
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalForm.green_second_D_row
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualOriginalSDirectPhysicalForm.pointwise_second_EUD_row
