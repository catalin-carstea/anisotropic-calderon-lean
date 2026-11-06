import Calderon.ActualHigherSIntegratedPairing
import Calderon.ActualHigherSPhysicalPairing

/-! Consumes only `scalar_weighted_green`, `HigherSIntegratedIdentity` and
`higherS_integrated_pairing_actual` from `ActualHigherSIntegratedPairing`, and
`ActualHigherSPhysicalPairing`. (1) integrability of the divergence and coefficient-derivative
integrands; (2) combined scalar Green `−∫(a·div_i + μ·X_i(a))·P`; (3) combined integrated identity;
(4) final actual producer: the SAME `δ0, W, δ, e` of `higherS_integrated_pairing_actual` carry output,
transfer, identity, combined identity and physical SphereL2 pairing. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSPhysicalIntegratedConsumer
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds SphereHarmonic.DegreeGraphLifting ConformalDepth ActualFiniteHarmonicModel
  PrincipalCommutator ActualHigherSFormation ActualHigherSSigned ActualHigherSIntegratedPairing
  ActualHigherSPhysicalPairing
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-! ## 1. Generic integrability and combination -/

/-- `c · P(α, J v)` is integrable for continuous `c, α` and continuous compactly supported `v`. -/
lemma integrable_mul_pp_right (c : R3 → ℝ) (α v : R3 → Half)
    (hc : Continuous c) (hα : Continuous α) (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (fun y => c y * PP (α y) (JL (v y))) := by
  have hcont : Continuous (fun y => c y * PP (α y) (JL (v y))) :=
    hc.mul (continuous_halfPairing hα ((JL).continuous.comp hv))
  refine hcont.integrable_of_hasCompactSupport (hvc.mono ?_)
  intro y hy
  rw [Function.mem_support] at hy ⊢
  intro h0
  apply hy
  show c y * PP (α y) (JL (v y)) = 0
  rw [h0, map_zero]
  unfold sphereSobolevDualPairing
  rw [inner_zero_right, mul_zero]

/-- Exact scalar combination of the divergence and coefficient-derivative integrals. -/
lemma combine_two_integrals (A Cc : ℝ) (D X Fc : R3 → ℝ) (hD : Integrable D) (hX : Integrable X)
    (hFc : ∀ y, Fc y = D y + X y) :
    -A - (∫ y, D y) + 2 * Cc - (∫ y, X y) = -A + 2 * Cc - ∫ y, Fc y := by
  have h1 : (∫ y, Fc y) = (∫ y, D y) + ∫ y, X y := by
    rw [← integral_add hD hX]
    exact integral_congr_ae (Filter.Eventually.of_forall hFc)
  rw [h1]
  ring

private lemma eight_first_congr {a b c d e f g h k : ℝ} (hAB : a=b) :
    a+c+d-e+f+g+h+k = b+c+d-e+f+g+h+k := by
  rw [hAB]

section Generic
variable (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)

/-- **Combined scalar weighted Green**, from `scalar_weighted_green`.
`X_i(a)` (all derivatives of `a`) is kept; physical degree unchanged; no output cut. -/
theorem scalar_weighted_green_combined (hg : IsAdmissibleMetric g) (hR : ContDiff ℝ ∞ R)
    (hr : ∀ y, R y ≠ 0) (u : R3 → Hi) (v : R3 → Half) (a : R3 → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    (∫ y, referenceDensityFamily g L (q,y) * a y *
        PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R v y i)) =
      -(∫ y, referenceDensityFamily g L (q,y) * a y *
          PP (v y) (JL (referenceHighWeightedHorizontalAction g L q R u y i))) +
        2 * (∫ y, referenceDensityFamily g L (q,y) *
            referenceRadiusHorizontalLogDerivative g L q R y i * a y *
              PP (v y) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y)))) -
        (∫ y, (a y * referenceWeightedFrameDivergence g L q i y +
            referenceDensityFamily g L (q,y) * fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i)) *
          PP (IH (u y)) (JL (v y))) := by
  have hG := scalar_weighted_green g L q R hg hR hr u v a hu hv hvc ha i
  have hmu : Continuous (fun y : R3 => referenceDensityFamily g L (q,y)) :=
    (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)
  have hXc : Continuous (fun y : R3 => referenceMetricGramFrame g L (q,y) i) :=
    (contDiff_referenceMetricGramFrame_slice g hg L q i).continuous
  have hda : Continuous (fun y => fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i)) :=
    (ha.continuous_fderiv (by simp)).clm_apply hXc
  have hα : Continuous (fun y => IH (u y)) := (IH).continuous.comp hu.continuous
  have hD : Integrable (fun y => referenceWeightedFrameDivergence g L q i y * a y *
      PP (IH (u y)) (JL (v y))) :=
    integrable_mul_pp_right (fun y => referenceWeightedFrameDivergence g L q i y * a y)
      (fun y => IH (u y)) v
      ((continuous_referenceWeightedFrameDivergence g hg L q i).mul ha.continuous)
      hα hv.continuous hvc
  have hX : Integrable (fun y => referenceDensityFamily g L (q,y) *
      fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) * PP (IH (u y)) (JL (v y))) :=
    integrable_mul_pp_right
      (fun y => referenceDensityFamily g L (q,y) * fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i))
      (fun y => IH (u y)) v (hmu.mul hda) hα hv.continuous hvc
  rw [hG]
  exact combine_two_integrals _ _ _ _ _ hD hX (fun y => by ring)

end Generic

/-! ## 2. Actual combined integrated identity -/
section Actual
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
local notation "Ahi" => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)
local notation "NEG" => nativeHigherSNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

section Profile
variable (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
local notation "RR" => referenceRadius δr Ar p L
local notation "T" => higherSParam L δr Ar p q
local notation "U" => higherSInput hO hD
local notation "V" => higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p q
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)
local notation "MUy" y:max => referenceDensityFamily g L (q,y)
local notation "Qc" g2:max y:max i:max j:max => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
local notation "FL" y:max i:max => referenceRadiusHorizontalLogDerivative g L q RR y i
local notation "GM" y:max i:max j:max k:max =>
  referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j
local notation "BB" g2:max y:max i:max => normalizedSecondDriftFrameJoint g g2 L i (q,y)
local notation "DW" u:max y:max j:max => referenceHighWeightedHorizontalAction g L q RR u y j

/-- `HigherSIntegratedIdentity` with the Second block's divergence and coefficient-derivative
integrals combined into ONE integral `−∫(a_ij·div_i + μ·X_i(a_ij))·P`, `a_ij = RR² Q_ij`. -/
def HigherSIntegratedIdentityCombined (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (e : Fin 3 → Tpar → Hi →L[ℝ] Half)
    (F0 : smoothCompactFiniteSphereCore hO hD) : Prop :=
  (∫ y, MUy y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y)) =
    (∑ i : Fin 3, ∑ j : Fin 3,
      (-(∫ y, MUy y * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (DW (U F0) y i))) +
        2 * (∫ y, MUy y * FL y i * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (U F0 y)))) -
        (∫ y, ((RR y ^ 2 * Qc g2 y i j) * referenceWeightedFrameDivergence g L q i y +
            MUy y * fderiv ℝ (fun z => RR z ^ 2 * Qc g2 z i j) y
              (referenceMetricGramFrame g L (q,y) i)) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))))) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∫ y, MUy y * (RR y ^ 2 * Qc g2 y i j) *
        PP (DW (U F0) y j) (JL (e i (T y) (U F0 y)))) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∫ y, MUy y * (RR y ^ 2 * Qc g2 y i j * FL y i) *
        PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) -
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ y, MUy y * (RR y ^ 2 * Qc g2 y i j * GM y i j k) *
        PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 k y)))) +
    (∑ i : Fin 3, ∫ y, MUy y * (RR y ^ 2 * BB g2 y i) *
        PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 i y)))) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∫ y, MUy y * (RR y * Qc g2 y i j) *
        PP (IH (V hreg δ0 W F0 j y)) (JL (loweringHigh hF hO hD i (U F0 y)))) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∫ y, MUy y * (RR y * Qc g2 y i j) *
        PP (Ahi j (U F0 y)) (JL (e i (T y) (U F0 y)))) +
    (∑ i : Fin 3, ∑ j : Fin 3, ∫ y, MUy y * (RR y ^ 3 * Qc g2 y i j) *
        PP (IH (V hreg δ0 W F0 j y)) (JL (e i (T y) (U F0 y))))

include hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q

attribute [local irreducible] higherSInput higherSLift higherSParam sphereSobolevDualPairing
  referenceRadius referenceDensityPrincipalFrameCoefficient referenceHighWeightedHorizontalAction
  sphereSobolevInclusionL

/-- Combined identity from `HigherSIntegratedIdentity` and the formation `V` facts (integrability proved). -/
theorem higherSIntegratedIdentityCombined_of_identity (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (e : Fin 3 → Tpar → Hi →L[ℝ] Half) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hVcd : ∀ j : Fin 3, ContDiff ℝ ∞ (V hreg δ0 W F0 j) ∧ ∀ z ∉ TS F0, V hreg δ0 W F0 j z = 0)
    (hId : HigherSIntegratedIdentity hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q hreg δ0 W g2 e F0) :
    HigherSIntegratedIdentityCombined hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q hreg δ0 W g2 e F0 := by
  have hRR : ContDiff ℝ ∞ RR :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hK : IsCompact (TS F0) := F0.property.2.1
  have hU : ContDiff ℝ ∞ (U F0) := by
    simpa only [higherSInput] using contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hmu : Continuous (fun y : R3 => referenceDensityFamily g L (q,y)) :=
    (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)
  have hqy : ContDiff ℝ ∞ (fun y : R3 => (q,y)) := contDiff_const.prodMk contDiff_id
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun z => RR z ^ 2 * Qc g2 z i j) :=
    (hRR.pow 2).mul ((contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
      (f := fun y : R3 => (q,y)) hqy)
  have hα : Continuous (fun y => IH (U F0 y)) := (IH).continuous.comp hU.continuous
  have hv (j : Fin 3) : Continuous (fun y => IH (V hreg δ0 W F0 j y)) :=
    (IH).continuous.comp (hVcd j).1.continuous
  have hvc (j : Fin 3) : HasCompactSupport (fun y => IH (V hreg δ0 W F0 j y)) :=
    HasCompactSupport.intro hK (fun z hz => by
      show IH (V hreg δ0 W F0 j z) = 0
      rw [(hVcd j).2 z hz, map_zero])
  have hDint (i j : Fin 3) : Integrable (fun y => referenceWeightedFrameDivergence g L q i y *
      (RR y ^ 2 * Qc g2 y i j) * PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) :=
    integrable_mul_pp_right
      (fun y => referenceWeightedFrameDivergence g L q i y * (RR y ^ 2 * Qc g2 y i j))
      (fun y => IH (U F0 y)) (fun y => IH (V hreg δ0 W F0 j y))
      ((continuous_referenceWeightedFrameDivergence g hg L q i).mul (ha i j).continuous)
      hα (hv j) (hvc j)
  have hXint (i j : Fin 3) : Integrable (fun y => MUy y *
      fderiv ℝ (fun z => RR z ^ 2 * Qc g2 z i j) y (referenceMetricGramFrame g L (q,y) i) *
      PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) :=
    integrable_mul_pp_right
      (fun y => MUy y *
        fderiv ℝ (fun z => RR z ^ 2 * Qc g2 z i j) y (referenceMetricGramFrame g L (q,y) i))
      (fun y => IH (U F0 y)) (fun y => IH (V hreg δ0 W F0 j y))
      (hmu.mul (((ha i j).continuous_fderiv (by simp)).clm_apply
        (contDiff_referenceMetricGramFrame_slice g hg L q i).continuous))
      hα (hv j) (hvc j)
  have hS1 :
      (∑ i : Fin 3, ∑ j : Fin 3,
        (-(∫ y, MUy y * (RR y ^ 2 * Qc g2 y i j) *
            PP (IH (V hreg δ0 W F0 j y)) (JL (DW (U F0) y i))) -
          (∫ y, referenceWeightedFrameDivergence g L q i y * (RR y ^ 2 * Qc g2 y i j) *
            PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) +
          2 * (∫ y, MUy y * FL y i * (RR y ^ 2 * Qc g2 y i j) *
            PP (IH (V hreg δ0 W F0 j y)) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (U F0 y)))) -
          (∫ y, MUy y * fderiv ℝ (fun z => RR z ^ 2 * Qc g2 z i j) y
              (referenceMetricGramFrame g L (q,y) i) *
            PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))))) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        (-(∫ y, MUy y * (RR y ^ 2 * Qc g2 y i j) *
            PP (IH (V hreg δ0 W F0 j y)) (JL (DW (U F0) y i))) +
          2 * (∫ y, MUy y * FL y i * (RR y ^ 2 * Qc g2 y i j) *
            PP (IH (V hreg δ0 W F0 j y)) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (U F0 y)))) -
          (∫ y, ((RR y ^ 2 * Qc g2 y i j) * referenceWeightedFrameDivergence g L q i y +
              MUy y * fderiv ℝ (fun z => RR z ^ 2 * Qc g2 z i j) y
                (referenceMetricGramFrame g L (q,y) i)) *
            PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))))) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      combine_two_integrals _ _ _ _ _ (hDint i j) (hXint i j) (fun y => by ring)
  unfold HigherSIntegratedIdentity at hId
  unfold HigherSIntegratedIdentityCombined
  exact hId.trans (eight_first_congr hS1)

private lemma higherSIntegratedIdentityCombined_of_output (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (e : Fin 3 → Tpar → Hi →L[ℝ] Half) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hOut : HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F0)
    (hId : HigherSIntegratedIdentity hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q hreg δ0 W g2 e F0) :
    HigherSIntegratedIdentityCombined hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q hreg δ0 W g2 e F0 := by
  unfold HigherSOutputConclusions at hOut
  exact higherSIntegratedIdentityCombined_of_identity hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W g2 hg2 e F0 hOut.2.1 hId

end Profile

attribute [local irreducible] HigherSOutputConclusions HigherSSignedTransferAt
  HigherSIntegratedIdentity HigherSIntegratedIdentityCombined HigherSPhysicalPairingConclusions

/-! ## 3. FINAL actual producer: one witness set, both output and identity, physical link -/

/-- The witnesses `δ0, W, δ, e` of `higherS_integrated_pairing_actual` (chosen ONCE, before every profile) carry, for each profile and
membership-only input: output conclusions, transfer, the full integrated identity, the combined
identity and the physical SphereL2 pairing conclusions (physical = dual integral, integrability
proved). Composing the physical equality with the identity gives the physical integrated formula. -/
theorem higherS_physical_integrated_actual (hreg : FixedDirichletRegularity)
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
              δr Ar p q g2 e F0 ∧
          HigherSIntegratedIdentity hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
              δr Ar p q hreg δ0 W g2 e F0 ∧
          HigherSIntegratedIdentityCombined hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
              δr Ar p q hreg δ0 W g2 e F0 ∧
          HigherSPhysicalPairingConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
              δr Ar p hδr hAr q hreg δ0 W g2 F0 := by
  obtain ⟨δ0, hδ0, W, δ, hδ, hδρ, e, hSm, hPair, hAll⟩ :=
    higherS_integrated_pairing_actual hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      hreg hKernel g2 hg2
  refine ⟨δ0, hδ0, W, δ, hδ, hδρ, e, hSm, hPair, ?_⟩
  intro δr Ar hδr hAr p q hq F0 hT
  obtain ⟨hOut, hTr, hId⟩ := hAll δr Ar hδr hAr p q hq F0 hT
  have hPhys := higherSPhysicalPairingConclusions_of_output hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W g2 F0 hOut
  have hComb := higherSIntegratedIdentityCombined_of_output hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W g2 hg2 e F0 hOut hId
  exact ⟨hOut, hTr, hId, hComb, hPhys⟩

end Actual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSPhysicalIntegratedConsumer
