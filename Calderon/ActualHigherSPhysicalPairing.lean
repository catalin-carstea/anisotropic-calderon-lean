import Calderon.ActualHigherSFormation
import Calderon.ActualDensityPrincipalFrameEllipticity
import Calderon.ActualWeightedHorizontalGreen

/-! (1) Universal `P(a, J b) = ⟪K a, K b⟫` from the native
zero-order identity and the linear isometry `sphereSobolevZeroEquiv`; (2) exact finite-core decoding
`K (IH (u y)) = F0 y`; (3) generic graph bridge and weighted integrability/equality for every
continuous weight; (4) actual formation consumer and uniform producer with the original
before-profile witnesses of `higherSUniformFormationContract_proof`; (5) `C^∞` actual weighted frame
divergence. All degrees are kept (including 0). -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSPhysicalPairing
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds SphereHarmonic.DegreeGraphLifting ConformalDepth ActualFiniteHarmonicModel
  ActualHigherSFormation WeightedFrameGreen
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I0" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-! ## 1–3. Universal Half/L2 identity, finite-core decoding, weighted bridge -/
section Pairing
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "ZE" => sphereSobolevZeroEquiv hO hD

/-- `Z (K a) = I0 a`: `K = Z.symm ∘ I0` by its printed definition. -/
theorem zeroEquiv_halfToSphereL2 (b : Half) : ZE (KL b) = I0 b := by
  first
    | exact (sphereSobolevZeroEquiv hO hD).apply_symm_apply (I0 b)
    | (simp only [sphereSobolevHalfToSphereL2L, ContinuousLinearMap.coe_comp',
        Function.comp_apply]
       exact (sphereSobolevZeroEquiv hO hD).apply_symm_apply (I0 b))

/-- **Universal identity** `P(a, J b) = ⟪K a, K b⟫_{SphereL2}` on all of `Half`. -/
theorem halfPairing_eq_inner_sphereL2 (b c : Half) : PP b (JL c) = ⟪KL b, KL c⟫_ℝ := by
  calc PP b (JL c) = ⟪I0 b, I0 c⟫_ℝ := halfPairing_inclusion_eq_inner_zero b c
    _ = ⟪ZE (KL b), ZE (KL c)⟫_ℝ := by
        rw [zeroEquiv_halfToSphereL2 hO hD b, zeroEquiv_halfToSphereL2 hO hD c]
    _ = ⟪KL b, KL c⟫_ℝ := LinearIsometryEquiv.inner_map_map (sphereSobolevZeroEquiv hO hD) _ _

/-- **Exact finite-core decoding** `K (IH (u y)) = F0 y`, `u = finiteCoreSobolevLift (3/2) F0`. -/
theorem halfToSphereL2_finiteCoreLift (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) :
    KL (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y)) = F0.val y := by
  apply (sphereSobolevZeroEquiv hO hD).injective
  rw [zeroEquiv_halfToSphereL2 hO hD]
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_inclusion, sphereSobolevCoefficientL_inclusion,
    sphereSobolevCoefficientL_finiteCoreSobolevLift, sphereSobolevCoefficientL_zeroEquiv]

theorem finiteCore_halfPairing_eq_inner (F0 : smoothCompactFiniteSphereCore hO hD)
    (b : Half) (y : R3) :
    PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y)) (JL b) = ⟪F0.val y, KL b⟫_ℝ := by
  rw [halfPairing_eq_inner_sphereL2 hO hD, halfToSphereL2_finiteCoreLift hO hD F0 y]

/-- Generic algebraic bridge from a negative graph `J (S y) = N y`. -/
theorem physical_pairing_of_graph (F0 : smoothCompactFiniteSphereCore hO hD)
    (S : R3 → Half) (N : R3 → Neg) (hGraph : ∀ y, JL (S y) = N y) (y : R3) :
    PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y)) (N y) = ⟪F0.val y, KL (S y)⟫_ℝ := by
  rw [← hGraph y]
  exact finiteCore_halfPairing_eq_inner hO hD F0 (S y) y

/-- Weighted bridge for every continuous weight: both integrands integrable (proved, not assumed),
integrals equal. -/
theorem weighted_physical_pairing_integral (F0 : smoothCompactFiniteSphereCore hO hD)
    (S : R3 → Half) (N : R3 → Neg) (mu : R3 → ℝ) (hmu : Continuous mu) (hS : Continuous S)
    (hGraph : ∀ y, JL (S y) = N y) :
    Integrable (fun y => mu y * ⟪F0.val y, KL (S y)⟫_ℝ) ∧
    Integrable (fun y => mu y * PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y)) (N y)) ∧
    (∫ y, mu y * PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y)) (N y)) =
      ∫ y, mu y * ⟪F0.val y, KL (S y)⟫_ℝ := by
  have hpt : (fun y => mu y * PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) F0 y)) (N y)) =
      fun y => mu y * ⟪F0.val y, KL (S y)⟫_ℝ := by
    funext y
    rw [physical_pairing_of_graph hO hD F0 S N hGraph y]
  have hF : Continuous (fun y => F0.val y) := F0.property.1.continuous
  have hcont : Continuous (fun y => mu y * ⟪F0.val y, KL (S y)⟫_ℝ) :=
    hmu.mul (hF.inner ((KL).continuous.comp hS))
  have hInt : Integrable (fun y => mu y * ⟪F0.val y, KL (S y)⟫_ℝ) := by
    refine hcont.integrable_of_hasCompactSupport (F0.property.2.1.mono ?_)
    intro y hy
    rw [Function.mem_support] at hy ⊢
    intro h0
    apply hy
    show mu y * ⟪F0.val y, KL (S y)⟫_ℝ = 0
    rw [h0, inner_zero_left, mul_zero]
  refine ⟨hInt, ?_, ?_⟩
  · rw [hpt]; exact hInt
  · rw [hpt]

end Pairing

/-! ## 5. Actual weighted frame divergence is `C^∞` -/

theorem contDiff_referenceWeightedFrameDivergence (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => referenceWeightedFrameDivergence g L q i y) := by
  have hrho : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (q,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hX : ContDiff ℝ ∞ (fun y : R3 => referenceMetricGramFrame g L (q,y) i) :=
    contDiff_referenceMetricGramFrame_slice g hg L q i
  have hTerm : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : R3 =>
      fderiv ℝ (fun z : R3 => referenceDensityFamily g L (q,z) *
        referenceMetricGramFrame g L (q,z) i j) y (coordinateDirection j)) := by
    intro j
    have hcomp : ContDiff ℝ ∞ (fun z : R3 => referenceMetricGramFrame g L (q,z) i j) := by
      first
        | exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hX
        | exact (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := j)).comp hX
        | exact (contDiff_piLp (𝕜 := ℝ) 2).1 hX j
    have hprod : ContDiff ℝ ∞ (fun z : R3 => referenceDensityFamily g L (q,z) *
        referenceMetricGramFrame g L (q,z) i j) := hrho.mul hcomp
    exact (contDiff_infty_iff_fderiv.1 hprod).2.clm_apply contDiff_const
  have hEq : (fun y => referenceWeightedFrameDivergence g L q i y) = fun y =>
      ∑ j : Fin 3, fderiv ℝ (fun z : R3 => referenceDensityFamily g L (q,z) *
        referenceMetricGramFrame g L (q,z) i j) y (coordinateDirection j) := rfl
  rw [hEq]
  exact ContDiff.sum (fun j _ => hTerm j)

theorem continuous_referenceWeightedFrameDivergence (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i : Fin 3) :
    Continuous (fun y => referenceWeightedFrameDivergence g L q i y) :=
  (contDiff_referenceWeightedFrameDivergence g hg L q i).continuous

/-! ## 4. Actual formation consumer and uniform producer -/
section Literal
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "NEG" => nativeHigherSNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

section Profile
variable (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
local notation "RR" => referenceRadius δr Ar p L
local notation "U" => higherSInput hO hD
local notation "SHalf" =>
  nativeHigherSHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q
local notation "SOut" =>
  nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q
local notation "MUy" y:max => referenceDensityFamily g L (q,y)

/-- Physical pairing conclusions for one profile and one finite input (all degrees). -/
def HigherSPhysicalPairingConclusions (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) : Prop :=
  (∀ y : R3, SOut hreg δ0 W g2 F0 y =
    sphereSobolevHalfToSphereL2L hO hD (SHalf hreg δ0 W g2 F0 y)) ∧
  (∀ y : R3, sphereSobolevHalfToSphereL2L hO hD (IH (U F0 y)) = F0.val y) ∧
  (∀ y : R3, PP (IH (U F0 y)) (NEG g2 q RR (U F0) y) = ⟪F0.val y, SOut hreg δ0 W g2 F0 y⟫_ℝ) ∧
  (∀ mu : R3 → ℝ, Continuous mu →
    Integrable (fun y => mu y * ⟪F0.val y, SOut hreg δ0 W g2 F0 y⟫_ℝ) ∧
    Integrable (fun y => mu y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y)) ∧
    (∫ y, mu y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y)) =
      ∫ y, mu y * ⟪F0.val y, SOut hreg δ0 W g2 F0 y⟫_ℝ) ∧
  Integrable (fun y => MUy y * ⟪F0.val y, SOut hreg δ0 W g2 F0 y⟫_ℝ) ∧
  Integrable (fun y => MUy y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y)) ∧
  (∫ y, MUy y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y)) =
    ∫ y, MUy y * ⟪F0.val y, SOut hreg δ0 W g2 F0 y⟫_ℝ

include hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p hδr hAr q

/-- Consumer of the proved per-profile output conclusions (no new graph premise). -/
theorem higherSPhysicalPairingConclusions_of_output (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hOut : HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F0) :
    HigherSPhysicalPairingConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F0 := by
  unfold HigherSOutputConclusions at hOut
  have hS : Continuous (SHalf hreg δ0 W g2 F0) := hOut.2.2.1.continuous
  have hGraph : ∀ y : R3, JL (SHalf hreg δ0 W g2 F0 y) = NEG g2 q RR (U F0) y := hOut.2.2.2.1
  have hmu : Continuous (fun y : R3 => referenceDensityFamily g L (q,y)) :=
    (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)
  have hAll : ∀ mu : R3 → ℝ, Continuous mu →
      Integrable (fun y => mu y * ⟪F0.val y, SOut hreg δ0 W g2 F0 y⟫_ℝ) ∧
      Integrable (fun y => mu y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y)) ∧
      (∫ y, mu y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y)) =
        ∫ y, mu y * ⟪F0.val y, SOut hreg δ0 W g2 F0 y⟫_ℝ :=
    fun mu hmu' => weighted_physical_pairing_integral hO hD F0 (SHalf hreg δ0 W g2 F0)
      (NEG g2 q RR (U F0)) mu hmu' hS hGraph
  have hPt : ∀ y : R3,
      PP (IH (U F0 y)) (NEG g2 q RR (U F0) y) = ⟪F0.val y, SOut hreg δ0 W g2 F0 y⟫_ℝ :=
    fun y => physical_pairing_of_graph hO hD F0 (SHalf hreg δ0 W g2 F0)
      (NEG g2 q RR (U F0)) hGraph y
  have hDec : ∀ y : R3, sphereSobolevHalfToSphereL2L hO hD (IH (U F0 y)) = F0.val y :=
    fun y => halfToSphereL2_finiteCoreLift hO hD F0 y
  unfold HigherSPhysicalPairingConclusions
  exact ⟨fun y => rfl, hDec, hPt, hAll, hAll _ hmu⟩

end Profile

/-- **Actual uniform producer.** Original witnesses `δ0, W, δ` from
`higherSUniformFormationContract_proof`, chosen BEFORE every profile, `q` and finite input; the only
input premise is ParamRoom membership on `tsupport F0`. Both output and physical conclusions at the
same witnesses. -/
theorem higherS_physical_pairing_actual (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∃ W : CoeffRoom δ0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
    commonRoom y0 ρ δ ⊆ Ω ∧
    ∀ (δr Ar : ℝ) (hδr : 0 < δr) (hAr : 0 < Ar) (p : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ F0 : smoothCompactFiniteSphereCore hO hD,
        (∀ x ∈ tsupport (F0 : R3 → SphereL2), higherSParam L δr Ar p q x ∈ ParamRoom δ) →
        HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
            δr Ar p hδr hAr q hreg δ0 W g2 F0 ∧
        HigherSPhysicalPairingConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
            δr Ar p hδr hAr q hreg δ0 W g2 F0 := by
  have hC := higherSUniformFormationContract_proof hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc
    τ0 hreg hKernel g2 hg2
  unfold HigherSUniformFormationContract at hC
  obtain ⟨δ0, hδ0, W, δ, hδ, hδδ0, hδρ, hΩ, hAll⟩ := hC
  refine ⟨δ0, hδ0, W, δ, hδ, hδδ0, hδρ, hΩ, ?_⟩
  intro δr Ar hδr hAr p q hq F0 hMem
  have hOut := hAll δr Ar hδr hAr p q hq F0 hMem
  exact ⟨hOut, higherSPhysicalPairingConclusions_of_output hF hO hD g L y0 Φ B ε C ρ H a w hData
    hg hcalc τ0 δr Ar p hδr hAr q hreg δ0 W g2 F0 hOut⟩

end Literal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSPhysicalPairing
