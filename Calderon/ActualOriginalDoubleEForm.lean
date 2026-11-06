import Calderon.ActualCommonFirstWordQuadraticAdjoint
import Calderon.ActualHigherSCoefficientBounds

/-! On the caller's retained `W` and one common room `Cm`: the exact pointwise Gram identity of the
ORIGINAL forward double field `higherSDoubleHalf` against a finite test (one `Cm.pivot`), its
transfer to the native reversed-order `revDoubleHalf`, compact-room operator bounds for `EH`/`eH`
(before `g2`), the actual `K = 9 CQ ‖KL‖² CE CrE` (after `g2`, before every profile/input), the
global pointwise bound `|form| ≤ K R³ ‖UF‖ ‖UG‖`, and the density-weighted integrated identities
and bounds, including the diagonal `F0 = G0`. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.OriginalDoubleEForm
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
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

/-- Finite family bound on a compact set (local copy of the native private helper). -/
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

/-- Cauchy-Schwarz plus the two actual operator norms and the actual CLM norm of `K`. -/
lemma abs_inner_clm_comp_le {H1 H2 E : Type*}
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

/-- Signed `3×3` weighted sum with a nonnegative radius factor `r^3`. -/
lemma abs_weighted_double_sum_le (r : ℝ) (hr : 0 ≤ r) (Q c : Fin 3 → Fin 3 → ℝ)
    (CQ M : ℝ) (hCQ : 0 ≤ CQ) (hQ : ∀ i j, |Q i j| ≤ CQ) (hc : ∀ i j, |c i j| ≤ M) :
    |r^3 * ∑ i : Fin 3, ∑ j : Fin 3, Q i j * c i j| ≤ 9 * CQ * M * r^3 := by
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
  have hr3 : 0 ≤ r^3 := pow_nonneg hr 3
  rw [abs_mul, abs_of_nonneg hr3]
  calc r^3 * |∑ i : Fin 3, ∑ j : Fin 3, Q i j * c i j| ≤ r^3 * (9 * (CQ * M)) :=
        mul_le_mul_of_nonneg_left hsum hr3
    _ = 9 * CQ * M * r^3 := by ring

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
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RD" => ActualCommonFirstWordQuadraticAdjoint.revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The exact signed double-E Gram density, ORIGINAL `Q_ij` order:
`R^3 Σ_ij Q_ij <KL(eH_i(Ty) UF), KL(EH_j(Ty) UG)>`. -/
def doubleEGram (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  (referenceRadius δr Ar p L x)^3 * ∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j *
      ⟪KL (eH i ((Tq δr Ar p q) x) (Uin F0 x)), KL (EH j ((Tq δr Ar p q) x) (Uin G0 x))⟫_ℝ
local notation "GR" => doubleEGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Room membership of the profile point yields `q ∈ [0,1]` and `x ∈ closedBall y0 ρ`. -/
lemma paramRoom_q_ball (δr Ar : ℝ) (p : ℕ) (q δ : ℝ) (x : R3)
    (ht : (Tq δr Ar p q) x ∈ ParamRoom δ) : q ∈ Icc (0 : ℝ) 1 ∧ x ∈ closedBall y0 ρ := by
  have hc : ((q,(x,referenceRadius δr Ar p L x)) : Pphys) ∈ commonRoom y0 ρ δ := ht.1
  first
    | exact ⟨hc.1, hc.2.1⟩
    | (simp only [commonRoom, Set.mem_prod] at hc; exact ⟨hc.1, hc.2.1⟩)

/-! ## 2. One-pivot Gram row and the exact pointwise Gram identity -/

/-- One `Cm.pivot`: `<KL(I u), KL(EH_i v)> = <KL(eH_i u), KL(EH_j w)>` when `I v = EH_j w`. -/
theorem gram_row (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (t : Tpar) (ht : t ∈ ParamRoom δ) (i j : Fin 3)
    (u v w' : Hi) (hw : IH v = EH j t w') :
    ⟪KL (IH u), KL (EH i t v)⟫_ℝ = ⟪KL (eH i t u), KL (EH j t w')⟫_ℝ := by
  have hP := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
  calc ⟪KL (IH u), KL (EH i t v)⟫_ℝ = ⟪KL (EH i t v), KL (IH u)⟫_ℝ := real_inner_comm _ _
    _ = PP (EH i t v) (JL (IH u)) := (hP _ _).symm
    _ = PP (IH v) (JL (eH i t u)) := Cm.pivot i t ht v u
    _ = PP (EH j t w') (JL (eH i t u)) := by rw [hw]
    _ = ⟪KL (EH j t w'), KL (eH i t u)⟫_ℝ := hP _ _
    _ = ⟪KL (eH i t u), KL (EH j t w')⟫_ℝ := real_inner_comm _ _

/-- GLOBAL exact pointwise Gram identity for the literal forward field; only `G0`'s own
support-room membership is used. -/
theorem pointwise_gram_identity (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ = GR g2 δr Ar p q F0 G0 x := by
  have hFx : F0.val x = KL (IH (Uin F0 x)) :=
    (ActualHigherSPhysicalPairing.halfToSphereL2_finiteCoreLift hO hD F0 x).symm
  have hrow : ∀ i j : Fin 3,
      ⟪KL (IH (Uin F0 x)), KL (EH i ((Tq δr Ar p q) x) (VF δr Ar p q hreg δ0 W G0 j x))⟫_ℝ =
        ⟪KL (eH i ((Tq δr Ar p q) x) (Uin F0 x)),
          KL (EH j ((Tq δr Ar p q) x) (Uin G0 x))⟫_ℝ := by
    intro i j
    by_cases hxG : x ∈ TS G0
    · exact gram_row g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
        _ (hTG x hxG) i j (Uin F0 x) (VF δr Ar p q hreg δ0 W G0 j x) (Uin G0 x)
        (ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion g L y0 Φ B ε C ρ H a w hData hg
          hcalc hF hO hD τ0 hreg δ0 W δ Cm δr Ar p hδr hAr q G0 hTG j x)
    · have hV := ActualHigherSFormation.higherSLift_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
        hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W G0 j x hxG
      have hU := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
        hData hg hcalc τ0 δr Ar p hδr hAr q G0 x hxG
      simp only [hV, hU, map_zero, inner_zero_right]
  rw [hFx, ActualCommonFirstWordQuadraticAdjoint.fwdDouble_eq g L y0 Φ B ε C ρ H a w hData hg
    hcalc hF hO hD τ0 hreg δ0 W g2 δr Ar p q G0 x]
  unfold doubleEGram
  simp only [map_smul, map_sum, real_inner_smul_right, inner_sum, hrow]

/-! ## 3. Operator bounds on the compact room, BEFORE `g2` -/

/-- Genuine opNorm bounds of `EH_i` and `eH_i` on `ParamRoom δ`, from `Cm.germHigh` and
`Cm.rev.germHigh` by compactness. Depends only on `Cm`. -/
theorem exists_double_E_operator_bounds (hreg : FixedDirichletRegularity) (δ0 : ℝ)
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

/-! ## 4. Global pointwise bound (internal adapter; constants discharged in §6) -/

theorem pointwise_bound_of_bounds (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 G0 : smoothCompactFiniteSphereCore hO hD)
    (hTG : ∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (CE CrE CQ : ℝ) (hCQ0 : 0 ≤ CQ)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hQ : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
      |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ) (x : R3) :
    |⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ| ≤
      9 * CQ * ‖KL‖^2 * CE * CrE * (referenceRadius δr Ar p L x)^3 *
        (‖Uin F0 x‖ * ‖Uin G0 x‖) := by
  rw [pointwise_gram_identity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
    g2 δr Ar p hδr hAr q F0 G0 hTG x]
  unfold doubleEGram
  by_cases hxG : x ∈ TS G0
  · have ht := hTG x hxG
    obtain ⟨hq, hx⟩ := paramRoom_q_ball L y0 ρ δr Ar p q δ x ht
    have hc : ∀ i j : Fin 3,
        |⟪KL (eH i ((Tq δr Ar p q) x) (Uin F0 x)), KL (EH j ((Tq δr Ar p q) x) (Uin G0 x))⟫_ℝ| ≤
          ‖KL‖^2 * CrE * CE * (‖Uin F0 x‖ * ‖Uin G0 x‖) := fun i j =>
      abs_inner_clm_comp_le KL (eH i ((Tq δr Ar p q) x)) (EH j ((Tq δr Ar p q) x))
        (Uin F0 x) (Uin G0 x) CrE CE (hE i _ ht).2 (hE j _ ht).1
    have hR : 0 ≤ referenceRadius δr Ar p L x := (referenceRadius_pos δr Ar p L x hδr hAr).le
    have h := abs_weighted_double_sum_le (referenceRadius δr Ar p L x) hR
      (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
      (fun i j => ⟪KL (eH i ((Tq δr Ar p q) x) (Uin F0 x)),
        KL (EH j ((Tq δr Ar p q) x) (Uin G0 x))⟫_ℝ)
      CQ (‖KL‖^2 * CrE * CE * (‖Uin F0 x‖ * ‖Uin G0 x‖)) hCQ0
      (fun i j => hQ q hq x hx i j) hc
    exact h.trans_eq (by ring)
  · have hU := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w
      hData hg hcalc τ0 δr Ar p hδr hAr q G0 x hxG
    simp [hU]

/-! ## 5. The original double-E two-input form contract -/

/-- Exact forward/reverse two-input identities, pointwise bounds and density-weighted
integrated identities/bounds with ONE constant `K`. -/
def OriginalDoubleEFormContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (g2 : MatrixField) (K : ℝ) : Prop :=
  ∀ δr Ar : ℝ, ∀ p : ℕ, 0 < δr → 0 < Ar → ∀ q : ℝ,
  ∀ F0 G0 : smoothCompactFiniteSphereCore hO hD,
    (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
    (∀ x ∈ TS G0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x : R3, ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ = GR g2 δr Ar p q F0 G0 x) ∧
      (∀ x : R3, ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ =
        ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ) ∧
      (∀ x : R3, ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ = GR g2 δr Ar p q F0 G0 x) ∧
      (∀ x : R3, |⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ| ≤
        K * (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖)) ∧
      (∀ x : R3, |⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ| ≤
        K * (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖)) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) * GR g2 δr Ar p q F0 G0 x) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) *
        (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖)) ∧
      (∫ x, referenceDensityFamily g L (q,x) *
          ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) =
        ∫ x, referenceDensityFamily g L (q,x) * GR g2 δr Ar p q F0 G0 x ∧
      (∫ x, referenceDensityFamily g L (q,x) *
          ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) =
        ∫ x, referenceDensityFamily g L (q,x) *
          ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ ∧
      |∫ x, referenceDensityFamily g L (q,x) *
          ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ| ≤
        K * ∫ x, referenceDensityFamily g L (q,x) *
          (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖) ∧
      |∫ x, referenceDensityFamily g L (q,x) *
          ⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ| ≤
        K * ∫ x, referenceDensityFamily g L (q,x) *
          (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖)

/-- Internal adapter: the contract from explicit operator and frame bounds. -/
theorem originalDoubleEFormContract_of_bounds (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (CE CrE CQ : ℝ) (hCQ0 : 0 ≤ CQ)
    (hE : ∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE)
    (hQ : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
      |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ) :
    OriginalDoubleEFormContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ g2
      (9 * CQ * ‖KL‖^2 * CE * CrE) := by
  intro δr Ar p hδr hAr q F0 G0 hTF hTG
  have hgram := pointwise_gram_identity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 G0 hTG
  have hadj := ActualCommonFirstWordQuadraticAdjoint.pointwise_physical_adjoint g L y0 Φ B ε C ρ
    H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 G0 hTF hTG
  have hInt := ActualCommonFirstWordQuadraticAdjoint.integrated_physical_adjoint g L y0 Φ B ε C ρ
    H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q F0 G0 hTF hTG
  have hbd := pointwise_bound_of_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 G0 hTG CE CrE CQ hCQ0 hE hQ
  have hbdR : ∀ x : R3, |⟪KL (RD hreg δ0 W g2 δr Ar p q F0 x), G0.val x⟫_ℝ| ≤
      9 * CQ * ‖KL‖^2 * CE * CrE * (referenceRadius δr Ar p L x)^3 *
        (‖Uin F0 x‖ * ‖Uin G0 x‖) := fun x => by
    rw [← hadj x]
    exact hbd x
  -- the right-hand weight is continuous with compact support (native lifts, smooth weights)
  have hρ : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hR : Continuous (referenceRadius δr Ar p L) :=
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr).continuous
  have hUF : Continuous (Uin F0) := (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0).continuous
  have hUG : Continuous (Uin G0) := (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) G0).continuous
  have hG0 : ∀ z ∉ TS G0, Uin G0 z = 0 := fun z hz =>
    ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q G0 z hz
  have hWc : Continuous (fun x => referenceDensityFamily g L (q,x) *
      (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖)) :=
    (hρ.mul (hR.pow 3)).mul (hUF.norm.mul hUG.norm)
  have hWi : Integrable (fun x => referenceDensityFamily g L (q,x) *
      (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖)) :=
    hWc.integrable_of_hasCompactSupport
      (ActualCommonFirstWordQuadraticAdjoint.hasCompactSupport_of_eq_zero_off hO hD G0 _
        (fun z hz => by simp [hG0 z hz]))
  -- exact signed Gram density, integrability and integral
  have hfun : (fun x => referenceDensityFamily g L (q,x) *
        ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ) =
      (fun x => referenceDensityFamily g L (q,x) * GR g2 δr Ar p q F0 G0 x) :=
    funext (fun x => by rw [hgram x])
  have hGi : Integrable (fun x => referenceDensityFamily g L (q,x) * GR g2 δr Ar p q F0 G0 x) := by
    rw [← hfun]
    exact hInt.1
  -- density-weighted bound
  have hpt : ∀ x : R3, ‖referenceDensityFamily g L (q,x) *
      ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ‖ ≤
      (9 * CQ * ‖KL‖^2 * CE * CrE) * (referenceDensityFamily g L (q,x) *
        (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖)) := by
    intro x
    have hμ := referenceDensityFamily_pos g hg L (q,x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hμ]
    calc referenceDensityFamily g L (q,x) * |⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ|
        ≤ referenceDensityFamily g L (q,x) * (9 * CQ * ‖KL‖^2 * CE * CrE *
            (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖)) :=
          mul_le_mul_of_nonneg_left (hbd x) hμ.le
      _ = _ := by ring
  have hIB : |∫ x, referenceDensityFamily g L (q,x) *
        ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 G0 x)⟫_ℝ| ≤
      (9 * CQ * ‖KL‖^2 * CE * CrE) * ∫ x, referenceDensityFamily g L (q,x) *
        (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin G0 x‖) := by
    have h := norm_integral_le_of_norm_le (hWi.const_mul (9 * CQ * ‖KL‖^2 * CE * CrE))
      (ae_of_all _ hpt)
    rw [integral_const_mul, Real.norm_eq_abs] at h
    exact h
  refine ⟨hgram, hadj, fun x => (hadj x).symm.trans (hgram x), hbd, hbdR,
    hInt.1, hInt.2.1, hGi, hWi, by rw [hfun], hInt.2.2, hIB, ?_⟩
  rw [← hInt.2.2]
  exact hIB

/-! ## 6. Actual final theorems: every constant discharged, ordered δ < CE,CrE < g2 < K < profiles -/

/-- ANY retained `W`: `δ > 0`, the common room and the operator caps come BEFORE every `g2`;
`K` comes after a fixed admissible `g2` and BEFORE every profile, cutoff, input and point. -/
theorem exists_retained_original_double_E_form (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Cm : CRoom hreg δ0 W δ, ∃ CE CrE : ℝ, 1 ≤ CE ∧ 1 ≤ CrE ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ∃ CQ : ℝ, 1 ≤ CQ ∧
        (∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
          |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ) ∧
        ∃ K : ℝ, 0 ≤ K ∧ K = 9 * CQ * ‖KL‖^2 * CE * CrE ∧
          OriginalDoubleEFormContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            hreg δ0 W δ g2 K := by
  obtain ⟨δ, Cm⟩ := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  obtain ⟨CE, CrE, hCE, hCrE, hE⟩ := exists_double_E_operator_bounds g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
  refine ⟨δ, Cm.rev.pos, Cm, CE, CrE, hCE, hCrE, hE, fun g2 hg2 => ?_⟩
  obtain ⟨CQ, hCQ, hQF⟩ := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound
    (g := g) (L := L) (y0 := y0) (ρ := ρ) (hg := hg) g2 hg2
  have hQ : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
      |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ :=
    fun q hq x hx i j => (hQF q hq x hx i j).1
  have hCQ0 : 0 ≤ CQ := zero_le_one.trans hCQ
  have hK0 : 0 ≤ 9 * CQ * ‖KL‖^2 * CE * CrE := by
    have h1 : 0 ≤ CE := zero_le_one.trans hCE
    have h2 : 0 ≤ CrE := zero_le_one.trans hCrE
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCQ0)
      (sq_nonneg _)) h1) h2
  exact ⟨CQ, hCQ, hQ, 9 * CQ * ‖KL‖^2 * CE * CrE, hK0, rfl,
    originalDoubleEFormContract_of_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 hg2 CE CrE CQ hCQ0 hE hQ⟩

/-- Diagonal specialization `F0 = G0` with the exact `R^3` bound and the signed Gram identity. -/
theorem diagonal_of_contract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (g2 : MatrixField) (K : ℝ)
    (hC : OriginalDoubleEFormContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ g2 K)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    (∀ x : R3, ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ = GR g2 δr Ar p q F0 F0 x) ∧
    (∀ x : R3, |⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
      K * (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin F0 x‖)) ∧
    (∫ x, referenceDensityFamily g L (q,x) *
        ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (q,x) * GR g2 δr Ar p q F0 F0 x ∧
    |∫ x, referenceDensityFamily g L (q,x) *
        ⟪F0.val x, KL (FD δr Ar p q hreg δ0 W g2 F0 x)⟫_ℝ| ≤
      K * ∫ x, referenceDensityFamily g L (q,x) *
        (referenceRadius δr Ar p L x)^3 * (‖Uin F0 x‖ * ‖Uin F0 x‖) := by
  obtain ⟨h1, -, -, h4, -, -, -, -, -, h10, -, h12, -⟩ := hC δr Ar p hδr hAr q F0 F0 hTF hTF
  exact ⟨h1, h4, h10, h12⟩

/-- Ordinary actual packet: `δ0, W` selected exactly ONCE by the native producer. -/
theorem exists_actual_original_double_E_form (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ ρ ∧ ∃ W : CoeffRoom δ0,
      ∃ δ : ℝ, 0 < δ ∧ ∃ Cm : CRoom hreg δ0 W δ, ∃ CE CrE : ℝ, 1 ≤ CE ∧ 1 ≤ CrE ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ‖EH i t‖ ≤ CE ∧ ‖eH i t‖ ≤ CrE) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → ∃ CQ : ℝ, 1 ≤ CQ ∧
        (∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
          |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ CQ) ∧
        ∃ K : ℝ, 0 ≤ K ∧ K = 9 * CQ * ‖KL‖^2 * CE * CrE ∧
          OriginalDoubleEFormContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            hreg δ0 W δ g2 K := by
  obtain ⟨δ0, hδ0, hδ0ρ, _hRoom, W, _⟩ :=
    exists_commonRoom_actual_fullE_ordinary_endpoints g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg
  exact ⟨δ0, hδ0, hδ0ρ, W, exists_retained_original_double_E_form g L y0 Φ B ε C ρ H a w hData
    hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.OriginalDoubleEForm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.OriginalDoubleEForm.exists_actual_original_double_E_form
