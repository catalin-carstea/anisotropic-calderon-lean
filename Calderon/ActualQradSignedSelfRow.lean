import Calderon.ActualQradFiniteInputSignedSelfRow
import Calderon.QradFourIndexNormIdentity
import Calderon.ActualAdjacentGainedBracket
import Calderon.ActualRadialCoefficientPivots
import Calderon.ActualQradFiniteFirstOutputLifts
import Calderon.ActualAdjacentGainedFiniteFamilyCaps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual physical Qrad signed self-row (author-only candidate, v008).
Complete expansion: output/MATHEMATICS.md, written before these declarations.
Uses ONLY the Root producers: first-output lifts, CL bracket, radial coefficient pivots,
finite-family adjacent caps, plus the checked QradFourIndexNormIdentity/WeakForm.
No compiler was run; no acceptance is claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL harmonicSphereSubspace
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialAdjointSharpSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutator
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow

attribute [local instance] adjacentGainThreeHalfComplete adjacentGainHalfComplete adjacentGainNegativeHalfComplete adjacentGainHighHighComplete adjacentGainHighHalfComplete adjacentGainHalfHalfComplete adjacentGainHalfNegComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))))

local notation "Ihi" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "Jlo" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "Z0" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "NMH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NML" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NMN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "RAH" => referenceAdjointThreeHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "RAL" => referenceAdjointHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "CH" => referenceAdjacentGainedCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "CL" => referenceAdjacentGainedCommutatorLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

attribute [local irreducible] commonSupportCoefficientFamily

/-! ### §6 Integrability on a compact parameter set BEFORE integration, then the integrated bound. -/

include hg in
theorem exists_reference_commonRadius_qrad_signed_selfRow_integrated
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ (m : Fin 3 → T × R3 → ℝ) (hm : ∀ i, ContDiff ℝ ∞ (m i))
        (Km : Set R3) (hKm : IsCompact Km)
        (hmz : ∀ i t x, x ∉ Km → m i (t,x) = 0) (Kt : Set T), IsCompact Kt →
        ∀ MQ : ℝ, 0 ≤ MQ →
        ∃ Cst : ℝ, 0 ≤ Cst ∧
          ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
            [T2Space X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (K : Set X), IsCompact K →
          ∀ (P : X → Pphys) (tt : X → T) (Qx : X → Fin 3 → Fin 3 → ℝ) (u : X → Hi),
            ContinuousOn P K → ContinuousOn tt K → (∀ i j, ContinuousOn (fun x => Qx x i j) K) →
            ContinuousOn u K →
            (∀ x ∈ K, P x ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) ∧ tt x ∈ Kt ∧
              ∀ i j, |Qx x i j| ≤ MQ) →
            let W : X → ℝ := fun x => qradSignedWeakSelfExpression
              (fun i => (secondTaylorRemainder (fun s : ℝ => RAH ((P x).1,((P x).2.1,s))) (P x).2.2).comp
                (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x))))
              (fun i => (NML (smoothMultiplierLowerJets
                (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x)))).comp
                (Sh (P x).1 (P x).2.1 (P x).2.2))
              (fun i => (NMN (smoothMultiplierLowerJets
                (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x)))).comp
                (Sl (P x).1 (P x).2.1 (P x).2.2))
              (fun i k => CH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x))
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) (tt x))
                (P x).1 (P x).2.1 (P x).2.2)
              (fun i k => CL (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x))
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) (tt x))
                (P x).1 (P x).2.1 (P x).2.2)
              (Qx x) (P x).2.2 (u x)
            IntegrableOn W K μ ∧
            IntegrableOn (fun x => Cst * (P x).2.2^6 * ‖u x‖^2) K μ ∧
            |∫ x in K, W x ∂μ| ≤ ∫ x in K, Cst * (P x).2.2^6 * ‖u x‖^2 ∂μ ∧
            ∀ (β : X → ℝ) (θ : ℝ), θ ≤ 1 → (∀ x ∈ K, 1 ≤ β x ∧ |(P x).2.2| * β x^2 ≤ θ) →
              IntegrableOn (fun x => β x * ‖u x‖^2) K μ →
              |∫ x in K, W x ∂μ| ≤ Cst * θ * ∫ x in K, β x * ‖u x‖^2 ∂μ := by
  have hRootSelected1 := exists_reference_commonRadius_adjacentGainedCommutator_finite_family_caps_and_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel T
  rcases hRootSelected1 with ⟨dF,hdF,hdFρ,hFam⟩
  have hRootSelected2 := exists_reference_commonRadius_radialCoefficient_diagonal_caps
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg T
  rcases hRootSelected2 with ⟨dC,hdC,_,hCap⟩
  refine ⟨min dF dC, lt_min hdF hdC, (min_le_left _ _).trans hdFρ, ?_⟩
  intro m hm Km hKm hmz Kt hKt MQ hMQ
  have hRootSelected3 := hFam m hm Km hKm hmz Kt hKt
  rcases hRootSelected3 with ⟨MF,hMF,hFamC⟩
  have hRootSelected4 := hCap m hm Km hKm hmz Kt hKt
  rcases hRootSelected4 with ⟨MD,hMD,hCapC⟩
  obtain ⟨Mall,hMallDef⟩ : ∃ M : ℝ, M = max (max MD MF) MQ := ⟨_,rfl⟩
  have hMDle : MD ≤ Mall := by rw [hMallDef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hMFle : MF ≤ Mall := by rw [hMallDef]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hMQle : MQ ≤ Mall := by rw [hMallDef]; exact le_max_right _ _
  have hMall : 0 ≤ Mall := hMQ.trans hMQle
  have hCst : (0 : ℝ) ≤ 324*Mall^5 := mul_nonneg (by norm_num) (pow_nonneg hMall 5)
  refine ⟨324*Mall^5, hCst, ?_⟩
  intro X _ _ _ _ μ _ K hK P tt Qx u hPc httc hQxc huc hIn
  intro W
  have hBoxC : ∀ x ∈ K, P x ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dC) dC) := fun x hx =>
    ⟨(hIn x hx).1.1,(hIn x hx).1.2.1,
      (neg_le_neg (min_le_right dF dC)).trans (hIn x hx).1.2.2.1,
      (hIn x hx).1.2.2.2.trans (min_le_right dF dC)⟩
  have hBoxF : ∀ x ∈ K, P x ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dF) dF) := fun x hx =>
    ⟨(hIn x hx).1.1,(hIn x hx).1.2.1,
      (neg_le_neg (min_le_left dF dC)).trans (hIn x hx).1.2.2.1,
      (hIn x hx).1.2.2.2.trans (min_le_left dF dC)⟩
  have hPt : ∀ x ∈ K, ContinuousWithinAt (fun x => (P x, tt x)) K x := fun x hx =>
    (hPc x hx).prodMk (httc x hx)
  have hPtt : ∀ x ∈ K, ContinuousWithinAt (fun x => (P x, (tt x, tt x))) K x := fun x hx =>
    (hPc x hx).prodMk ((httc x hx).prodMk (httc x hx))
  -- continuity of every actual operator along the section (coefficients frozen, diagonal t)
  have cRH : ∀ i : Fin 3, ContinuousOn (fun x =>
      (secondTaylorRemainder (fun s : ℝ => RAH ((P x).1,((P x).2.1,s))) (P x).2.2).comp
        (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x)))) K :=
    fun i x hx => ((hCapC i (P x) (hBoxC x hx) (tt x) ((hIn x hx).2.1)).1.continuousAt).comp_continuousWithinAt (f := fun x : X => (P x, tt x)) (x := x)
      (hPt x hx)
  have cLH : ∀ i : Fin 3, ContinuousOn (fun x =>
      (NML (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x)))).comp
        (Sh (P x).1 (P x).2.1 (P x).2.2)) K :=
    fun i x hx => ((hCapC i (P x) (hBoxC x hx) (tt x) ((hIn x hx).2.1)).2.1.continuousAt).comp_continuousWithinAt (f := fun x : X => (P x, tt x)) (x := x)
      (hPt x hx)
  have cLL : ∀ i : Fin 3, ContinuousOn (fun x =>
      (NMN (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x)))).comp
        (Sl (P x).1 (P x).2.1 (P x).2.2)) K :=
    fun i x hx => ((hCapC i (P x) (hBoxC x hx) (tt x) ((hIn x hx).2.1)).2.2.2.1.continuousAt).comp_continuousWithinAt (f := fun x : X => (P x, tt x)) (x := x)
      (hPt x hx)
  have cCH : ∀ i k : Fin 3, ContinuousOn (fun x =>
      CH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x))
        (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) (tt x))
        (P x).1 (P x).2.1 (P x).2.2) K :=
    fun i k x hx => ((hFamC i k (P x) (hBoxF x hx) (tt x) ((hIn x hx).2.1) (tt x)
      ((hIn x hx).2.1)).1.continuousAt).comp_continuousWithinAt (f := fun x : X => (P x,(tt x,tt x))) (x := x) (hPtt x hx)
  have cCL : ∀ i k : Fin 3, ContinuousOn (fun x =>
      CL (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x))
        (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) (tt x))
        (P x).1 (P x).2.1 (P x).2.2) K :=
    fun i k x hx => ((hFamC i k (P x) (hBoxF x hx) (tt x) ((hIn x hx).2.1) (tt x)
      ((hIn x hx).2.1)).2.1.continuousAt).comp_continuousWithinAt (f := fun x : X => (P x,(tt x,tt x))) (x := x) (hPtt x hx)
  have hrc : ContinuousOn (fun x => (P x).2.2) K :=
    (continuous_snd.comp continuous_snd).comp_continuousOn hPc
  -- integrability FIRST, from continuity on the compact set
  have hWc : ContinuousOn W K :=
    continuousOn_qradSignedWeakSelfExpression _ _ _ _ _ Qx (fun x => (P x).2.2) u
      cRH cLH cLL cCH cCL hQxc hrc huc
  have hWi : IntegrableOn W K μ := hWc.integrableOn_compact hK
  have hDc : ContinuousOn (fun x => 324*Mall^5 * (P x).2.2^6 * ‖u x‖^2) K :=
    (continuousOn_const.mul (hrc.pow 6)).mul (huc.norm.pow 2)
  have hDi : IntegrableOn (fun x => 324*Mall^5 * (P x).2.2^6 * ‖u x‖^2) K μ :=
    hDc.integrableOn_compact hK
  -- pointwise checked 324 bound (valid for every Hi vector, gains only, independent of n)
  have hPw : ∀ x ∈ K, |W x| ≤ 324*Mall^5 * (P x).2.2^6 * ‖u x‖^2 := by
    intro x hx
    have hc := fun i => hCapC i (P x) (hBoxC x hx) (tt x) (hIn x hx).2.1
    have hf := fun i k => hFamC i k (P x) (hBoxF x hx) (tt x) ((hIn x hx).2.1) (tt x) (hIn x hx).2.1
    exact abs_qradSignedWeakSelfExpression_le _ _ _ _ _ (Qx x) Mall hMall
      (fun i => (hc i).2.2.2.2.1.trans hMDle) (fun i => (hc i).2.2.2.2.2.1.trans hMDle)
      (fun i => (hc i).2.2.2.2.2.2.2.trans hMDle)
      (fun i k => (hf i k).2.2.1.trans hMFle) (fun i k => (hf i k).2.2.2.1.trans hMFle)
      (fun i j => ((hIn x hx).2.2 i j).trans hMQle) ((P x).2.2) (u x)
  have hInt : |∫ x in K, W x ∂μ| ≤ ∫ x in K, 324*Mall^5 * (P x).2.2^6 * ‖u x‖^2 ∂μ :=
    calc
      |∫ x in K, W x ∂μ| ≤ ∫ x in K, |W x| ∂μ := abs_integral_le_integral_abs
      _ ≤ _ := setIntegral_mono_on (Integrable.abs hWi) hDi hK.measurableSet hPw
  refine ⟨hWi,hDi,hInt,?_⟩
  intro β θ hθ hβ hβi
  have hPro : ∀ x ∈ K, 324*Mall^5 * (P x).2.2^6 * ‖u x‖^2 ≤
      324*Mall^5 * θ * (β x * ‖u x‖^2) := by
    intro x hx
    have h6 : |(P x).2.2|^6 ≤ θ * β x :=
      radial_pow_six_le_theta_mul_beta |(P x).2.2| (β x) θ (abs_nonneg _) (hβ x hx).1 (hβ x hx).2 hθ
    have hEven : Even (6 : ℕ) := ⟨3, rfl⟩
    rw [hEven.pow_abs] at h6
    have hN : 0 ≤ ‖u x‖^2 := by positivity
    calc
      324*Mall^5 * (P x).2.2^6 * ‖u x‖^2 ≤ 324*Mall^5 * (θ * β x) * ‖u x‖^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h6 hCst) hN
      _ = 324*Mall^5 * θ * (β x * ‖u x‖^2) := by ring
  calc
    |∫ x in K, W x ∂μ| ≤ ∫ x in K, 324*Mall^5 * (P x).2.2^6 * ‖u x‖^2 ∂μ := hInt
    _ ≤ ∫ x in K, 324*Mall^5 * θ * (β x * ‖u x‖^2) ∂μ :=
      setIntegral_mono_on hDi (Integrable.const_mul hβi (324*Mall^5 * θ)) hK.measurableSet hPro
    _ = 324*Mall^5 * θ * ∫ x in K, β x * ‖u x‖^2 ∂μ := integral_const_mul _ _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
