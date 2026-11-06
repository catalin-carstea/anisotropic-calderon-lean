import Calderon.ActualHigherSFormation
import Calderon.ActualWeightedHorizontalGreen
import Calderon.ActualAngularCoordinateTransposePairing
import Calderon.ActualHigherSSigned

/-! Source-only author: Opusv044, 29 October 2026. UNCOMPILED.
Before-source mathematics: INTEGRATED-PAIRING-MATHEMATICS.md §§3–5 (same output directory).
(1) generic lower weighted product rule `Dlow_i(a v) = a Dlow_i v + X_i(a) • J v`;
(2) scalar weighted Green from the native `actual_weighted_horizontal_green` (coefficient
derivative `X_i(a)` kept, density divergence with its native sign);
(3) exact pointwise expansion of `μ P(Iu, nativeHigherSNegative)` using the genuine transfers and
the native angular transpose; (4) the integrated Second/Angular/Double identity with
`a_ij = r^2 Q_ij`, `X_i(r^2 Q_ij)` literal; (5) final theorem with all witnesses before profiles and
the membership-only input premise. No `e=-E+gain`, no estimate, no SphereL2 norm conversion. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSIntegratedPairing
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds SphereHarmonic.DegreeGraphLifting ConformalDepth ActualFiniteHarmonicModel
  PrincipalCommutator ActualHigherSFormation ActualHigherSSigned
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "DL" => (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-! ## 1. Generic integration helpers -/

lemma integrable_of_vanish (h : R3 → ℝ) (hc : Continuous h) (K : Set R3) (hK : IsCompact K)
    (h0 : ∀ y ∉ K, h y = 0) : Integrable h :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hK h0)

lemma integrable_pp (K : Set R3) (hK : IsCompact K) (c : R3 → ℝ) (α : R3 → Half) (β : R3 → Neg)
    (hc : Continuous c) (hα : Continuous α) (hβ : Continuous β)
    (h0 : ∀ y ∉ K, α y = 0 ∨ β y = 0) : Integrable (fun y => c y * PP (α y) (β y)) :=
  integrable_of_vanish _ (hc.mul (continuous_halfPairing hα hβ)) K hK (fun y hy => by
    rcases h0 y hy with h | h
    · rw [h, pp_zero_left, mul_zero]
    · rw [h, pp_zero_right, mul_zero])

lemma integrable_sum2 (F : Fin 3 → Fin 3 → R3 → ℝ) (hF : ∀ i j, Integrable (F i j)) :
    Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, F i j y) :=
  integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hF i j))

lemma integrable_sum3 (F : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ) (hF : ∀ i j k, Integrable (F i j k)) :
    Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, F i j k y) :=
  integrable_finset_sum _ (fun i _ => integrable_sum2 (F i) (hF i))

lemma integral_sum1 (F : Fin 3 → R3 → ℝ) (hF : ∀ i, Integrable (F i)) :
    ∫ y, ∑ i : Fin 3, F i y = ∑ i : Fin 3, ∫ y, F i y :=
  integral_finset_sum _ (fun i _ => hF i)

lemma integral_sum2 (F : Fin 3 → Fin 3 → R3 → ℝ) (hF : ∀ i j, Integrable (F i j)) :
    ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, F i j y = ∑ i : Fin 3, ∑ j : Fin 3, ∫ y, F i j y := by
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hF i j))]
  exact Finset.sum_congr rfl (fun i _ => integral_finset_sum _ (fun j _ => hF i j))

lemma integral_sum3 (F : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ) (hF : ∀ i j k, Integrable (F i j k)) :
    ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, F i j k y =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ y, F i j k y := by
  rw [integral_finset_sum _ (fun i _ => integrable_sum2 (F i) (hF i))]
  exact Finset.sum_congr rfl (fun i _ => integral_sum2 (F i) (hF i))

lemma integral_eight (A B C D E F G H : R3 → ℝ) (hA : Integrable A) (hB : Integrable B)
    (hC : Integrable C) (hD : Integrable D) (hE : Integrable E) (hF : Integrable F)
    (hG : Integrable G) (hH : Integrable H) :
    ∫ y, (A y + B y + C y - D y + E y + F y + G y + H y) =
      (∫ y, A y) + (∫ y, B y) + (∫ y, C y) - (∫ y, D y) + (∫ y, E y) + (∫ y, F y) +
        (∫ y, G y) + (∫ y, H y) := by
  have h1 : Integrable (fun y => A y + B y) := hA.add hB
  have h2 : Integrable (fun y => A y + B y + C y) := h1.add hC
  have h3 : Integrable (fun y => A y + B y + C y - D y) := h2.sub hD
  have h4 : Integrable (fun y => A y + B y + C y - D y + E y) := h3.add hE
  have h5 : Integrable (fun y => A y + B y + C y - D y + E y + F y) := h4.add hF
  have h6 : Integrable (fun y => A y + B y + C y - D y + E y + F y + G y) := h5.add hG
  rw [integral_add h6 hH, integral_add h5 hG, integral_add h4 hF, integral_add h3 hE,
    integral_sub h2 hD, integral_add h1 hC, integral_add hA hB]

/-- Scalar bookkeeping is isolated from the analytic operator definitions. -/
private lemma scalar_eight_congr
    {a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : ℝ}
    (h1 : a1=b1) (h2 : a2=b2) (h3 : a3=b3) (h4 : a4=b4)
    (h5 : a5=b5) (h6 : a6=b6) (h7 : a7=b7) (h8 : a8=b8) :
    a1+a2+a3-a4+a5+a6+a7+a8 = b1+b2+b3-b4+b5+b6+b7+b8 := by
  rw [h1,h2,h3,h4,h5,h6,h7,h8]

private lemma integral_eight_sums
    (A B C F G H : Fin 3 → Fin 3 → R3 → ℝ)
    (D : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ) (E : Fin 3 → R3 → ℝ)
    (hA : ∀ i j, Integrable (A i j)) (hB : ∀ i j, Integrable (B i j))
    (hC : ∀ i j, Integrable (C i j)) (hD : ∀ i j k, Integrable (D i j k))
    (hE : ∀ i, Integrable (E i)) (hF : ∀ i j, Integrable (F i j))
    (hG : ∀ i j, Integrable (G i j)) (hH : ∀ i j, Integrable (H i j)) :
    (∫ y, ((∑ i, ∑ j, A i j y) + (∑ i, ∑ j, B i j y) +
      (∑ i, ∑ j, C i j y) - (∑ i, ∑ j, ∑ k, D i j k y) +
      (∑ i, E i y) + (∑ i, ∑ j, F i j y) + (∑ i, ∑ j, G i j y) +
      (∑ i, ∑ j, H i j y))) =
    (∑ i, ∑ j, ∫ y, A i j y) + (∑ i, ∑ j, ∫ y, B i j y) +
      (∑ i, ∑ j, ∫ y, C i j y) - (∑ i, ∑ j, ∑ k, ∫ y, D i j k y) +
      (∑ i, ∫ y, E i y) + (∑ i, ∑ j, ∫ y, F i j y) +
      (∑ i, ∑ j, ∫ y, G i j y) + (∑ i, ∑ j, ∫ y, H i j y) := by
  exact (integral_eight _ _ _ _ _ _ _ _
    (integrable_sum2 A hA) (integrable_sum2 B hB) (integrable_sum2 C hC)
    (integrable_sum3 D hD) (integrable_finset_sum _ (fun i _ => hE i))
    (integrable_sum2 F hF) (integrable_sum2 G hG) (integrable_sum2 H hH)).trans
    (scalar_eight_congr (integral_sum2 A hA) (integral_sum2 B hB)
      (integral_sum2 C hC) (integral_sum3 D hD) (integral_sum1 E hE)
      (integral_sum2 F hF) (integral_sum2 G hG) (integral_sum2 H hH))

/-! ## 2. Lower weighted action: expansion, continuity, support, product rule -/
private def weightedActionValue (J A B : Half →L[ℝ] Neg) (f : ℝ) (dv v : Half) : Neg :=
  J dv + A v + f • B v

private lemma weightedActionValue_zero (J A B : Half →L[ℝ] Neg) (f : ℝ) :
    weightedActionValue J A B f 0 0 = 0 := by
  simp only [weightedActionValue, map_zero, smul_zero, add_zero]

private lemma weightedActionValue_smul (J A B : Half →L[ℝ] Neg)
    (f c d : ℝ) (dv v : Half) :
    weightedActionValue J A B f (c • dv + d • v) (c • v) =
      c • weightedActionValue J A B f dv v + d • J v := by
  simp only [weightedActionValue, map_add, map_smul, smul_add]
  module

private lemma weightedPairing_scalar_expand (c a d : ℝ) (x : Half) (D z : Neg) :
    c * PP x (a • D + d • z) = c * a * PP x D + c * d * PP x z := by
  rw [pp_add_right, pp_smul_right, pp_smul_right]
  ring

private lemma weightedPairing_smul_left (c a : ℝ) (x : Half) (z : Neg) :
    c * PP (a • x) z = c * a * PP x z := by
  rw [pp_smul_left]
  ring

private lemma weightedPairing_smul_right (c a : ℝ) (x v : Half) :
    c * PP x (JL (a • v)) = c * a * PP x (JL v) := by
  rw [map_smul, pp_smul_right]
  ring

section Generic
variable (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)

/-- The checked definitional expansion (as `e1` in the native Green proof). -/
lemma lowerWeighted_eq (v : R3 → Half) (y : R3) (i : Fin 3) :
    referenceLowerWeightedHorizontalAction g L q R v y i =
      JL (fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i)) +
        referenceLowerHorizontalAngularL g L q y i (v y) +
          referenceRadiusHorizontalLogDerivative g L q R y i • DL (v y) := rfl

attribute [local irreducible] referencePhysicalDensityOperator referenceDensityCovariantSecondAction
  referenceHighDensityFirstAction referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceNativeMovingAdjointParametricCorrection referenceNativeMovingAdjointHighMixedCorrection
  referenceMetricGramFrame referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  referenceRadiusHorizontalLogDerivative sphereSobolevInclusionL sphereSobolevAngularCoordinateTransposeL
  referenceRadialEndpointInvertibleLocus normalizedSecondDriftFrameJoint


attribute [local irreducible] referenceLowerHorizontalAngularL sphereSobolevShiftedDegreeL

lemma contDiff_logDerivative_slice (hg : IsAdmissibleMetric g) (hR : ContDiff ℝ ∞ R)
    (hr : ∀ y, R y ≠ 0) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => referenceRadiusHorizontalLogDerivative g L q R y i) :=
  contDiff_iff_contDiffAt.2 fun y =>
    (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i
      hR.contDiffAt (hr y)).comp y (contDiffAt_const.prodMk contDiffAt_id)

lemma continuous_density_slice (hg : IsAdmissibleMetric g) :
    Continuous (fun y : R3 => referenceDensityFamily g L (q,y)) :=
  (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)

lemma continuous_lowerWeighted (hg : IsAdmissibleMetric g) (hR : ContDiff ℝ ∞ R)
    (hr : ∀ y, R y ≠ 0) (v : R3 → Half) (hv : ContDiff ℝ ∞ v) (i : Fin 3) :
    Continuous (fun y => referenceLowerWeightedHorizontalAction g L q R v y i) := by
  have hX := contDiff_referenceMetricGramFrame_slice g hg L q i
  have hA := contDiff_referenceLowerHorizontalAngularL g hg L q i
  have hf := contDiff_logDerivative_slice g L q R hg hR hr i
  have he : (fun y => referenceLowerWeightedHorizontalAction g L q R v y i) =
      fun y => JL (fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i)) +
        referenceLowerHorizontalAngularL g L q y i (v y) +
          referenceRadiusHorizontalLogDerivative g L q R y i • DL (v y) :=
    funext fun y => lowerWeighted_eq g L q R v y i
  rw [he]
  exact (((JL).continuous.comp ((hv.continuous_fderiv (by simp)).clm_apply hX.continuous)).add
    (hA.continuous.clm_apply hv.continuous)).add
      (hf.continuous.smul ((DL).continuous.comp hv.continuous))

lemma lowerWeighted_eq_zero_of_notMem (v : R3 → Half) (y : R3) (i : Fin 3)
    (hy : y ∉ tsupport v) : referenceLowerWeightedHorizontalAction g L q R v y i = 0 := by
  have hev : v =ᶠ[𝓝 y] fun _ => (0 : Half) := by
    filter_upwards [(isClosed_tsupport v).isOpen_compl.mem_nhds hy] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  have hz : v y = 0 := hev.self_of_nhds
  have hd : fderiv ℝ v y = 0 := hev.fderiv_eq.trans (fderiv_const_apply _)
  have hdv : fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i) = 0 :=
    (congrArg (fun K : R3 →L[ℝ] Half => K (referenceMetricGramFrame g L (q,y) i)) hd).trans rfl
  calc
    referenceLowerWeightedHorizontalAction g L q R v y i =
        weightedActionValue JL (referenceLowerHorizontalAngularL g L q y i) DL
          (referenceRadiusHorizontalLogDerivative g L q R y i)
          (fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i)) (v y) :=
      lowerWeighted_eq g L q R v y i
    _ = weightedActionValue JL (referenceLowerHorizontalAngularL g L q y i) DL
          (referenceRadiusHorizontalLogDerivative g L q R y i) 0 0 :=
      congrArg₂ (weightedActionValue JL (referenceLowerHorizontalAngularL g L q y i) DL
        (referenceRadiusHorizontalLogDerivative g L q R y i)) hdv hz
    _ = 0 := weightedActionValue_zero _ _ _ _

/-- **Lower weighted product rule** (genuine Fréchet product rule; angular and degree terms are
linear). The coefficient derivative `X_i(a) = fderiv a y (X_i y)` is kept. -/
lemma lowerWeighted_smul (a : R3 → ℝ) (v : R3 → Half) (y : R3) (i : Fin 3)
    (ha : DifferentiableAt ℝ a y) (hv : DifferentiableAt ℝ v y) :
    referenceLowerWeightedHorizontalAction g L q R (a • v) y i =
      a y • referenceLowerWeightedHorizontalAction g L q R v y i +
        fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) • JL (v y) := by
  have hd : fderiv ℝ (a • v) y = a y • fderiv ℝ v y + (fderiv ℝ a y).smulRight (v y) :=
    (ha.hasFDerivAt.smul hv.hasFDerivAt).fderiv
  have hdv : fderiv ℝ (a • v) y (referenceMetricGramFrame g L (q,y) i) =
      a y • fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i) +
        fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) • v y := by
    have h := congrArg (fun K : R3 →L[ℝ] Half => K (referenceMetricGramFrame g L (q,y) i)) hd
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply] using h
  have hvv : (a • v) y = a y • v y := rfl
  have hbase : referenceLowerWeightedHorizontalAction g L q R v y i =
      weightedActionValue JL (referenceLowerHorizontalAngularL g L q y i) DL
        (referenceRadiusHorizontalLogDerivative g L q R y i)
        (fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i)) (v y) :=
    lowerWeighted_eq g L q R v y i
  calc
    referenceLowerWeightedHorizontalAction g L q R (a • v) y i =
        weightedActionValue JL (referenceLowerHorizontalAngularL g L q y i) DL
          (referenceRadiusHorizontalLogDerivative g L q R y i)
          (fderiv ℝ (a • v) y (referenceMetricGramFrame g L (q,y) i)) ((a • v) y) :=
      lowerWeighted_eq g L q R (a • v) y i
    _ = weightedActionValue JL (referenceLowerHorizontalAngularL g L q y i) DL
          (referenceRadiusHorizontalLogDerivative g L q R y i)
          (a y • fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i) +
            fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) • v y) (a y • v y) :=
      congrArg₂ (weightedActionValue JL (referenceLowerHorizontalAngularL g L q y i) DL
        (referenceRadiusHorizontalLogDerivative g L q R y i)) hdv hvv
    _ = a y • weightedActionValue JL (referenceLowerHorizontalAngularL g L q y i) DL
          (referenceRadiusHorizontalLogDerivative g L q R y i)
          (fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i)) (v y) +
        fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) • JL (v y) :=
      weightedActionValue_smul _ _ _ _ _ _ _ _
    _ = _ := congrArg (fun z : Neg => a y • z +
      fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) • JL (v y)) hbase.symm

/-- **Scalar weighted Green** (native Green applied to `a • v`, product rule subtracted). -/
theorem scalar_weighted_green (hg : IsAdmissibleMetric g) (hR : ContDiff ℝ ∞ R)
    (hr : ∀ y, R y ≠ 0) (u : R3 → Hi) (v : R3 → Half) (a : R3 → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    (∫ y, referenceDensityFamily g L (q,y) * a y *
        PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R v y i)) =
      -(∫ y, referenceDensityFamily g L (q,y) * a y *
          PP (v y) (JL (referenceHighWeightedHorizontalAction g L q R u y i))) -
        (∫ y, referenceWeightedFrameDivergence g L q i y * a y * PP (IH (u y)) (JL (v y))) +
          2 * (∫ y, referenceDensityFamily g L (q,y) *
            referenceRadiusHorizontalLogDerivative g L q R y i * a y *
              PP (v y) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y)))) -
        (∫ y, referenceDensityFamily g L (q,y) *
          fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) * PP (IH (u y)) (JL (v y))) := by
  have hav : ContDiff ℝ ∞ (a • v) := ha.smul hv
  have havc : HasCompactSupport (a • v) := hvc.smul_left
  have hG := actual_weighted_horizontal_green g hg L q R hR hr u (a • v) hu hav havc i
  have hμ := continuous_density_slice g L q hg
  have hX := contDiff_referenceMetricGramFrame_slice g hg L q i
  have hXa : Continuous (fun y => fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i)) :=
    (ha.continuous_fderiv (by simp)).clm_apply hX.continuous
  have hIu : Continuous (fun y => IH (u y)) := (IH).continuous.comp hu.continuous
  have hK : IsCompact (tsupport v) := hvc
  have hv0 (y : R3) (hy : y ∉ tsupport v) : v y = 0 := image_eq_zero_of_notMem_tsupport hy
  have i1 : Integrable (fun y => referenceDensityFamily g L (q,y) * a y *
      PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R v y i)) :=
    integrable_of_vanish _ ((hμ.mul ha.continuous).mul (continuous_halfPairing hIu
      (continuous_lowerWeighted g L q R hg hR hr v hv i))) _ hK (fun y hy => by
        rw [lowerWeighted_eq_zero_of_notMem g L q R v y i hy, pp_zero_right, mul_zero])
  have i2 : Integrable (fun y => referenceDensityFamily g L (q,y) *
      fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) * PP (IH (u y)) (JL (v y))) :=
    integrable_of_vanish _ ((hμ.mul hXa).mul (continuous_halfPairing hIu
      ((JL).continuous.comp hv.continuous))) _ hK (fun y hy => by
        rw [hv0 y hy, map_zero, pp_zero_right, mul_zero])
  have p1 (y : R3) : referenceDensityFamily g L (q,y) *
      PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R (a • v) y i) =
      referenceDensityFamily g L (q,y) * a y *
          PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R v y i) +
        referenceDensityFamily g L (q,y) *
          fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) * PP (IH (u y)) (JL (v y)) := by
    have hAct := lowerWeighted_smul g L q R a v y i
      (ha.differentiable (by simp) y) (hv.differentiable (by simp) y)
    exact (congrArg (fun z : Neg => referenceDensityFamily g L (q,y) * PP (IH (u y)) z) hAct).trans
      (weightedPairing_scalar_expand (referenceDensityFamily g L (q,y)) (a y)
        (fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i)) (IH (u y))
        (referenceLowerWeightedHorizontalAction g L q R v y i) (JL (v y)))
  have hL : (∫ y, referenceDensityFamily g L (q,y) *
      PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R (a • v) y i)) =
      (∫ y, referenceDensityFamily g L (q,y) * a y *
          PP (IH (u y)) (referenceLowerWeightedHorizontalAction g L q R v y i)) +
        ∫ y, referenceDensityFamily g L (q,y) *
          fderiv ℝ a y (referenceMetricGramFrame g L (q,y) i) * PP (IH (u y)) (JL (v y)) := by
    rw [← integral_add i1 i2]
    congr 1; funext y; exact p1 y
  have h2 : (∫ y, referenceDensityFamily g L (q,y) *
      PP ((a • v) y) (JL (referenceHighWeightedHorizontalAction g L q R u y i))) =
      ∫ y, referenceDensityFamily g L (q,y) * a y *
        PP (v y) (JL (referenceHighWeightedHorizontalAction g L q R u y i)) := by
    congr 1
    funext y
    exact weightedPairing_smul_left (referenceDensityFamily g L (q,y)) (a y) (v y)
      (JL (referenceHighWeightedHorizontalAction g L q R u y i))
  have h3 : (∫ y, referenceWeightedFrameDivergence g L q i y * PP (IH (u y)) (JL ((a • v) y))) =
      ∫ y, referenceWeightedFrameDivergence g L q i y * a y * PP (IH (u y)) (JL (v y)) := by
    congr 1
    funext y
    exact weightedPairing_smul_right (referenceWeightedFrameDivergence g L q i y) (a y)
      (IH (u y)) (v y)
  have h4 : (∫ y, referenceDensityFamily g L (q,y) *
      referenceRadiusHorizontalLogDerivative g L q R y i *
        PP ((a • v) y) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y)))) =
      ∫ y, referenceDensityFamily g L (q,y) *
        referenceRadiusHorizontalLogDerivative g L q R y i * a y *
          PP (v y) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y))) := by
    congr 1
    funext y
    exact weightedPairing_smul_left
      (referenceDensityFamily g L (q,y) * referenceRadiusHorizontalLogDerivative g L q R y i)
      (a y) (v y) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y)))
  have hR := congrArg₂ (fun x y : ℝ => x + 2 * y)
    (congrArg₂ (fun x y : ℝ => -x-y) h2 h3) h4
  exact eq_sub_of_add_eq (hL.symm.trans (hG.trans hR))
end Generic

/-! ## 3. Actual data -/
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

attribute [local irreducible] higherSInput higherSLift higherSRaisingInput higherSReferenceInput higherSParam
  sphereSobolevDualPairing loweringHigh loweringLow referenceRadius

/-- **The complete integrated higher-S identity** (actual density, physical degree `k` incl. 0,
coefficient derivative `X_i(r^2 Q_ij)` literal). Second: four Green integrals per `(i,j)` plus
the transferred `LQ` term, `f`, `Γ` and `b` terms; Angular: native transpose + transferred `LQ`;
Double: transferred `LQ`. -/
def HigherSIntegratedIdentity (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (e : Fin 3 → Tpar → Hi →L[ℝ] Half)
    (F0 : smoothCompactFiniteSphereCore hO hD) : Prop :=
  (∫ y, MUy y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y)) =
    (∑ i : Fin 3, ∑ j : Fin 3,
      (-(∫ y, MUy y * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (DW (U F0) y i))) -
        (∫ y, referenceWeightedFrameDivergence g L q i y * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) +
        2 * (∫ y, MUy y * FL y i * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (U F0 y)))) -
        (∫ y, MUy y * fderiv ℝ (fun z => RR z ^ 2 * Qc g2 z i j) y
            (referenceMetricGramFrame g L (q,y) i) *
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

private lemma higherSSecondNegative_eq_literal (g2 : MatrixField)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : nativeHigherSSecondNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    g2 q RR (U F0) y =
    RR y ^ 2 • (∑ i : Fin 3, ∑ j : Fin 3, Qc g2 y i j •
      (referenceLowerWeightedHorizontalAction g L q RR (fun x => MQ q RR x j (U F0 x)) y i +
        LQ q RR y i (DW (U F0) y j) + FL y i • JL (MQ q RR y j (U F0 y)) -
          ∑ k : Fin 3, GM y i j k • JL (MQ q RR y k (U F0 y)))) +
    RR y ^ 2 • (∑ i : Fin 3, BB g2 y i • JL (MQ q RR y i (U F0 y))) := by
  unfold nativeHigherSSecondNegative
  rfl

private lemma higherSAngularNegative_eq_literal (g2 : MatrixField)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : nativeHigherSAngularNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    g2 q RR (U F0) y = RR y • ∑ i : Fin 3, ∑ j : Fin 3,
      Qc g2 y i j • (Alo i (MQ q RR y j (U F0 y)) + LQ q RR y i (Ahi j (U F0 y))) := by
  unfold nativeHigherSAngularNegative
  dsimp only

private lemma higherSDoubleNegative_eq_literal (g2 : MatrixField)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) : nativeHigherSDoubleNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    g2 q RR (U F0) y = RR y ^ 3 • ∑ i : Fin 3, ∑ j : Fin 3,
      Qc g2 y i j • LQ q RR y i (MQ q RR y j (U F0 y)) := by
  unfold nativeHigherSDoubleNegative
  rfl

attribute [local irreducible] nativeHigherSSecondNegative nativeHigherSAngularNegative
  nativeHigherSDoubleNegative

/-- Exact pointwise expansion of `μ P(Iu, NEG)` at EVERY `y` (transfers + native transpose). -/
theorem higherS_pointwise_expansion (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (e : Fin 3 → Tpar → Hi →L[ℝ] Half)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hVal : ∀ j : Fin 3, ∀ x : R3, IH (V hreg δ0 W F0 j x) = MQ q RR x j (U F0 x))
    (hTr : HigherSSignedTransferAt hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q g2 e F0) (y : R3) :
    MUy y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y) =
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (U F0 y)) (referenceLowerWeightedHorizontalAction g L q RR
            (fun x => IH (V hreg δ0 W F0 j x)) y i)) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y ^ 2 * Qc g2 y i j) *
          PP (DW (U F0) y j) (JL (e i (T y) (U F0 y)))) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y ^ 2 * Qc g2 y i j * FL y i) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) -
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, MUy y * (RR y ^ 2 * Qc g2 y i j * GM y i j k) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 k y)))) +
      (∑ i : Fin 3, MUy y * (RR y ^ 2 * BB g2 y i) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 i y)))) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (loweringHigh hF hO hD i (U F0 y)))) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y * Qc g2 y i j) *
          PP (Ahi j (U F0 y)) (JL (e i (T y) (U F0 y)))) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y ^ 3 * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (e i (T y) (U F0 y)))) := by
  obtain ⟨t1, t2, t3⟩ := hTr
  have hSec := higherSSecondNegative_eq_literal hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q g2 F0 y
  have hAng := higherSAngularNegative_eq_literal hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q g2 F0 y
  have hDbl := higherSDoubleNegative_eq_literal hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q g2 F0 y
  have hNeg : NEG g2 q RR (U F0) y =
      nativeHigherSSecondNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        g2 q RR (U F0) y +
      nativeHigherSAngularNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        g2 q RR (U F0) y +
      nativeHigherSDoubleNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        g2 q RR (U F0) y := by
    unfold nativeHigherSNegative
    rfl
  have hLit := hNeg.trans (congrArg₂ (fun x y : Neg => x+y)
    (congrArg₂ (fun x y : Neg => x+y) hSec hAng) hDbl)
  refine (congrArg (fun z : Neg => MUy y * PP (IH (U F0 y)) z) hLit).trans ?_
  simp only [pp_add_right, pp_sub_right, pp_smul_right, pp_sum_right, t1 y, t2 y, t3 y,
    actual_angular_coordinate_transpose_pairing hF hO hD]
  simp only [← hVal]
  simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc, add_assoc]

/-- Integrated identity from the actual formation/reverse facts (all discharged in §4). -/
theorem higherSIntegratedIdentity_of_facts (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (e : Fin 3 → Tpar → Hi →L[ℝ] Half) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hVal : ∀ j : Fin 3, ∀ x : R3, IH (V hreg δ0 W F0 j x) = MQ q RR x j (U F0 x))
    (hVcd : ∀ j : Fin 3, ContDiff ℝ ∞ (V hreg δ0 W F0 j) ∧ ∀ z ∉ TS F0, V hreg δ0 W F0 j z = 0)
    (hSm : ∀ i : Fin 3, ∀ x ∈ TS F0, ContDiffAt ℝ ∞ (e i) (T x))
    (hTr : HigherSSignedTransferAt hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q g2 e F0) :
    HigherSIntegratedIdentity hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 δr Ar p q
      hreg δ0 W g2 e F0 := by
  have hRR : ContDiff ℝ ∞ RR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hr : ∀ y, RR y ≠ 0 := fun y => ne_of_gt (referenceRadius_pos δr Ar p L y hδr hAr)
  have hRc : Continuous RR := hRR.continuous
  have hK : IsCompact (TS F0) := F0.property.2.1
  have hU : ContDiff ℝ ∞ (U F0) := by
    simpa only [higherSInput] using contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hU0 := higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q F0
  have hμ := continuous_density_slice g L q hg
  have hqy : ContDiff ℝ ∞ (fun y : R3 => (q,y)) := contDiff_const.prodMk contDiff_id
  have hQ (i j : Fin 3) : ContDiff ℝ ∞ (fun y => Qc g2 y i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
      (f := fun y : R3 => (q,y)) hqy
  have hb (i : Fin 3) : ContDiff ℝ ∞ (fun y => BB g2 y i) :=
    (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).comp
      (f := fun y : R3 => (q,y)) hqy
  have hΓ (i j k : Fin 3) : ContDiff ℝ ∞ (fun y => GM y i j k) :=
    contDiff_referenceGramConnectionSlice g hg L q i j k
  have hf (i : Fin 3) : ContDiff ℝ ∞ (fun y => FL y i) :=
    contDiff_logDerivative_slice g L q RR hg hRR hr i
  have hIu : Continuous (fun y => IH (U F0 y)) := (IH).continuous.comp hU.continuous
  have hIVd (j : Fin 3) : ContDiff ℝ ∞ (fun x => IH (V hreg δ0 W F0 j x)) :=
    (IH).contDiff.comp (hVcd j).1
  have hIV0 (j : Fin 3) (z : R3) (hz : z ∉ TS F0) : IH (V hreg δ0 W F0 j z) = 0 := by
    rw [(hVcd j).2 z hz, map_zero]
  have hIVc (j : Fin 3) : HasCompactSupport (fun x => IH (V hreg δ0 W F0 j x)) :=
    HasCompactSupport.intro hK (hIV0 j)
  have hDW (j : Fin 3) : Continuous (fun y => DW (U F0) y j) :=
    (contDiff_iff_contDiffAt.2 (fun y =>
      contDiffAt_referenceHighWeightedHorizontalAction g hg L q RR (U F0) y j
        hRR.contDiffAt (hr y) hU.contDiffAt)).continuous
  have hDW0 (j : Fin 3) (z : R3) (hz : z ∉ TS F0) : DW (U F0) z j = 0 :=
    referenceHighWeightedHorizontalAction_eq_zero_of_eventually g L q RR (U F0) z j
      (higherSInput_eventually_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        δr Ar p hδr hAr q F0 z hz)
  have hev (i : Fin 3) : Continuous (fun y => JL (e i (T y) (U F0 y))) :=
    (JL).continuous.comp (contDiff_family_apply hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc
      τ0 δr Ar p hδr hAr q (e i) F0 (hSm i) (U F0) hU hU0).continuous
  have hlow (i : Fin 3) : Continuous (fun y => JL (loweringHigh hF hO hD i (U F0 y))) :=
    (JL).continuous.comp ((loweringHigh hF hO hD i).continuous.comp hU.continuous)
  have hAh (j : Fin 3) : Continuous (fun y => Ahi j (U F0 y)) :=
    (Ahi j).continuous.comp hU.continuous
  have hJIV (j : Fin 3) : Continuous (fun y => JL (IH (V hreg δ0 W F0 j y))) :=
    (JL).continuous.comp (hIVd j).continuous
  have hIUz (z : R3) (hz : z ∉ TS F0) : IH (U F0 z) = 0 := by rw [hU0 z hz, map_zero]
  have hAhz (j : Fin 3) (z : R3) (hz : z ∉ TS F0) : Ahi j (U F0 z) = 0 := by
    rw [hU0 z hz, map_zero]
  -- per-term integrability
  have i1 (i j : Fin 3) : Integrable (fun y => MUy y * (RR y ^ 2 * Qc g2 y i j) *
      PP (IH (U F0 y)) (referenceLowerWeightedHorizontalAction g L q RR
        (fun x => IH (V hreg δ0 W F0 j x)) y i)) :=
    integrable_pp (TS F0) hK _ _ _ (hμ.mul ((hRc.pow 2).mul (hQ i j).continuous)) hIu
      (continuous_lowerWeighted g L q RR hg hRR hr _ (hIVd j) i)
      (fun z hz => Or.inl (hIUz z hz))
  have i2 (i j : Fin 3) : Integrable (fun y => MUy y * (RR y ^ 2 * Qc g2 y i j) *
      PP (DW (U F0) y j) (JL (e i (T y) (U F0 y)))) :=
    integrable_pp (TS F0) hK _ _ _ (hμ.mul ((hRc.pow 2).mul (hQ i j).continuous)) (hDW j) (hev i)
      (fun z hz => Or.inl (hDW0 j z hz))
  have i3 (i j : Fin 3) : Integrable (fun y => MUy y * (RR y ^ 2 * Qc g2 y i j * FL y i) *
      PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) :=
    integrable_pp (TS F0) hK _ _ _
      (hμ.mul (((hRc.pow 2).mul (hQ i j).continuous).mul (hf i).continuous)) hIu (hJIV j)
      (fun z hz => Or.inl (hIUz z hz))
  have i4 (i j k : Fin 3) : Integrable (fun y => MUy y * (RR y ^ 2 * Qc g2 y i j * GM y i j k) *
      PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 k y)))) :=
    integrable_pp (TS F0) hK _ _ _
      (hμ.mul (((hRc.pow 2).mul (hQ i j).continuous).mul (hΓ i j k).continuous)) hIu (hJIV k)
      (fun z hz => Or.inl (hIUz z hz))
  have i5 (i : Fin 3) : Integrable (fun y => MUy y * (RR y ^ 2 * BB g2 y i) *
      PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 i y)))) :=
    integrable_pp (TS F0) hK _ _ _ (hμ.mul ((hRc.pow 2).mul (hb i).continuous)) hIu (hJIV i)
      (fun z hz => Or.inl (hIUz z hz))
  have i6 (i j : Fin 3) : Integrable (fun y => MUy y * (RR y * Qc g2 y i j) *
      PP (IH (V hreg δ0 W F0 j y)) (JL (loweringHigh hF hO hD i (U F0 y)))) :=
    integrable_pp (TS F0) hK _ _ _ (hμ.mul (hRc.mul (hQ i j).continuous)) (hIVd j).continuous
      (hlow i) (fun z hz => Or.inl (hIV0 j z hz))
  have i7 (i j : Fin 3) : Integrable (fun y => MUy y * (RR y * Qc g2 y i j) *
      PP (Ahi j (U F0 y)) (JL (e i (T y) (U F0 y)))) :=
    integrable_pp (TS F0) hK _ _ _ (hμ.mul (hRc.mul (hQ i j).continuous)) (hAh j) (hev i)
      (fun z hz => Or.inl (hAhz j z hz))
  have i8 (i j : Fin 3) : Integrable (fun y => MUy y * (RR y ^ 3 * Qc g2 y i j) *
      PP (IH (V hreg δ0 W F0 j y)) (JL (e i (T y) (U F0 y)))) :=
    integrable_pp (TS F0) hK _ _ _ (hμ.mul ((hRc.pow 3).mul (hQ i j).continuous))
      (hIVd j).continuous (hev i) (fun z hz => Or.inl (hIV0 j z hz))
  -- scalar Green for every (i,j), a = r^2 Q_ij, v = I V_j
  have hGr (i j : Fin 3) :
      (∫ y, MUy y * (RR y ^ 2 * Qc g2 y i j) *
        PP (IH (U F0 y)) (referenceLowerWeightedHorizontalAction g L q RR
          (fun x => IH (V hreg δ0 W F0 j x)) y i)) =
      -(∫ y, MUy y * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (DW (U F0) y i))) -
        (∫ y, referenceWeightedFrameDivergence g L q i y * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) +
        2 * (∫ y, MUy y * FL y i * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (U F0 y)))) -
        (∫ y, MUy y * fderiv ℝ (fun z => RR z ^ 2 * Qc g2 z i j) y
            (referenceMetricGramFrame g L (q,y) i) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) :=
    scalar_weighted_green g L q RR hg hRR hr (U F0) (fun x => IH (V hreg δ0 W F0 j x))
      (fun z => RR z ^ 2 * Qc g2 z i j) hU (hIVd j) (hIVc j) ((hRR.pow 2).mul (hQ i j)) i
  -- integrate the pointwise expansion
  have hInt : (∫ y, MUy y * PP (IH (U F0 y)) (NEG g2 q RR (U F0) y)) =
      ∫ y, ((∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y ^ 2 * Qc g2 y i j) *
          PP (IH (U F0 y)) (referenceLowerWeightedHorizontalAction g L q RR
            (fun x => IH (V hreg δ0 W F0 j x)) y i)) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y ^ 2 * Qc g2 y i j) *
          PP (DW (U F0) y j) (JL (e i (T y) (U F0 y)))) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y ^ 2 * Qc g2 y i j * FL y i) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 j y)))) -
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, MUy y * (RR y ^ 2 * Qc g2 y i j * GM y i j k) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 k y)))) +
      (∑ i : Fin 3, MUy y * (RR y ^ 2 * BB g2 y i) *
          PP (IH (U F0 y)) (JL (IH (V hreg δ0 W F0 i y)))) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (loweringHigh hF hO hD i (U F0 y)))) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y * Qc g2 y i j) *
          PP (Ahi j (U F0 y)) (JL (e i (T y) (U F0 y)))) +
      (∑ i : Fin 3, ∑ j : Fin 3, MUy y * (RR y ^ 3 * Qc g2 y i j) *
          PP (IH (V hreg δ0 W F0 j y)) (JL (e i (T y) (U F0 y))))) := by
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y =>
      higherS_pointwise_expansion hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        δr Ar p hδr hAr q hreg δ0 W g2 e F0 hVal hTr y))
  unfold HigherSIntegratedIdentity
  have hSum := integral_eight_sums _ _ _ _ _ _ _ _ i1 i2 i3 i4 i5 i6 i7 i8
  have hGreenSum := Finset.sum_congr (show (Finset.univ : Finset (Fin 3)) = Finset.univ from rfl)
    (fun i _ => Finset.sum_congr (show (Finset.univ : Finset (Fin 3)) = Finset.univ from rfl) (fun j _ => hGr i j))
  exact hInt.trans (hSum.trans (scalar_eight_congr hGreenSum rfl rfl rfl rfl rfl rfl rfl))

/-- Consume the exact existing formation packet without unfolding it in a
context containing the globally chosen witnesses. -/
private lemma higherSIntegratedIdentity_of_output (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (e : Fin 3 → Tpar → Hi →L[ℝ] Half) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hSm : ∀ i : Fin 3, ∀ x ∈ TS F0, ContDiffAt ℝ ∞ (e i) (T x))
    (hOut : HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F0)
    (hTr : HigherSSignedTransferAt hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q g2 e F0) :
    HigherSIntegratedIdentity hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p q hreg δ0 W g2 e F0 := by
  unfold HigherSOutputConclusions at hOut
  exact higherSIntegratedIdentity_of_facts hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W g2 hg2 e F0 hOut.1 hOut.2.1 hSm hTr

end Profile

attribute [local irreducible] HigherSOutputConclusions HigherSSignedTransferAt HigherSIntegratedIdentity

/-! ## 4. FINAL actual theorem: witnesses before profiles, membership-only input premise -/

theorem higherS_integrated_pairing_actual (hreg : FixedDirichletRegularity)
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
              δr Ar p q hreg δ0 W g2 e F0 := by
  obtain ⟨δ0, hδ0, W, δ, hδ, hδρ, e, hSm, hPair, hAll⟩ :=
    higherS_signed_transfer_actual hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      hreg hKernel g2 hg2
  refine ⟨δ0, hδ0, W, δ, hδ, hδρ, e, hSm, hPair, ?_⟩
  intro δr Ar hδr hAr p q hq F0 hT
  obtain ⟨hOut, hTr⟩ := hAll δr Ar hδr hAr p q hq F0 hT
  refine ⟨hOut, hTr, ?_⟩
  exact higherSIntegratedIdentity_of_output hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W g2 hg2 e F0
    (fun i x hx => hSm i _ (hT x hx)) hOut hTr

end Actual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSIntegratedPairing
