import Calderon.ActualDensityPrincipalFrameCoefficientBound
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.SphereSobolevPairingInclusion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Ellipticity of the principal coefficient `Q = Cᵀ N C` (`referenceDensityPrincipalFrameCoefficient`,
with coframe `referenceCoFrameEntry` and the normalized matrix): positive definiteness,
a compact uniform scalar lower bound whose constant precedes every profile/cutoff/input,
the arbitrary real Hilbert vector version, the zero-order Half/Neg dual-pairing version
(all harmonic degrees, including degree 0) and weighted integral consequences carrying
`referenceDensityFamily`. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace Matrix
universe u
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open NormalizedPrincipalMetric ActualHorizontalNormBridge ReferenceDensityBounds
  SmoothMetricFrame ConformalDepth MetricOperator MetricVolume RadiusProfile SphereHarmonic

/-! ### 1. Actual coframe injectivity and positive definiteness of actual `Q` -/

/-- The actual coframe is injective: `Σ_j C_kj v_j = 0` for all `k` forces `v = 0`.
Proof from metric orthonormality of the actual Gram frame and its coordinate expansion. -/
lemma referenceCoFrame_injective (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (y : R3) (v : Fin 3 → ℝ)
    (hv : ∀ k : Fin 3, ∑ j : Fin 3, referenceCoFrameEntry g L k j (q,y) * v j = 0) :
    v = 0 := by
  let M := metricOperatorField (referenceMetric (dilatedMetric g q) L) y
  let f := referenceMetricGramFrame g L (q,y)
  let u : R3 := ∑ j : Fin 3, v j • f j
  have hOrth : ∀ i j : Fin 3, ⟪M (f i), f j⟫_ℝ = if i = j then 1 else 0 := fun i j =>
    referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (q,y) i j
  have hCo : ∀ k : Fin 3, ⟪M (coordinateDirection k), u⟫_ℝ = 0 := by
    intro k
    refine Eq.trans ?_ (hv k)
    simp only [u, inner_sum, real_inner_smul_right]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_comm]
    rfl
  funext i
  have hZero : ⟪M (f i), u⟫_ℝ = 0 := by
    have hExp := referenceGramFrame_eq_sum_coordinateDirection g L q y i
    change ⟪M (referenceMetricGramFrame g L (q,y) i), u⟫_ℝ = 0
    rw [hExp, map_sum, sum_inner]
    exact Finset.sum_eq_zero (fun k _ => by rw [map_smul, real_inner_smul_left, hCo k, mul_zero])
  have hEval : ⟪M (f i), u⟫_ℝ = v i := by
    simp [u, inner_sum, real_inner_smul_right, hOrth]
  show v i = 0
  rw [← hEval, hZero]

/-- Exact algebraic contraction `ξᵀ Q ξ = (Cξ)ᵀ N (Cξ)` for the actual `Q`. -/
lemma referenceDensityPrincipalFrameCoefficient_quadratic
    (g g2 : MatrixField) (L q : ℝ) (y : R3) (ξ : Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ξ i * ξ j =
      ∑ k : Fin 3, ∑ l : Fin 3, referenceNormalizedPrincipalMatrix g g2 L q y k l *
        (∑ i : Fin 3, referenceCoFrameEntry g L k i (q,y) * ξ i) *
          (∑ j : Fin 3, referenceCoFrameEntry g L l j (q,y) * ξ j) := by
  simp only [referenceDensityPrincipalFrameCoefficient, Fin.sum_univ_three]
  ring

/-- Strict positivity of the actual quadratic form at every `q`, `y` and every `ξ ≠ 0`. -/
theorem referenceDensityPrincipalFrameCoefficient_quadratic_pos
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (y : R3) (ξ : Fin 3 → ℝ) (hξ : ξ ≠ 0) :
    0 < ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ξ i * ξ j := by
  let N := referenceNormalizedPrincipalMatrix g g2 L q y
  let w : Fin 3 → ℝ := fun k => ∑ i : Fin 3, referenceCoFrameEntry g L k i (q,y) * ξ i
  have hN : N.PosDef := normalizedPrincipalMatrix_posDef _ _
    (dilatedReferenceMetric_posDef g hg q L y) (dilatedMetric_posDef g2 hg2 q y)
  have hw : w ≠ 0 := by
    intro h0
    exact hξ (referenceCoFrame_injective g hg L q y ξ (fun k => congrFun h0 k))
  have hpos : 0 < star w ⬝ᵥ (N *ᵥ w) := hN.dotProduct_mulVec_pos hw
  have hEq : star w ⬝ᵥ (N *ᵥ w) = ∑ k : Fin 3, ∑ l : Fin 3, N k l * w k * w l := by
    simp only [Pi.star_apply, star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  rw [hEq] at hpos
  rw [referenceDensityPrincipalFrameCoefficient_quadratic]
  exact hpos

/-- Actual `Q` is positive definite (not merely semidefinite). -/
theorem referenceDensityPrincipalFrameCoefficient_posDef
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (y : R3) :
    Matrix.PosDef (Matrix.of (fun i j : Fin 3 =>
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j)) := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨(referenceDensityPrincipalFrameCoefficient_posSemidef g g2 hg hg2 L q y).isHermitian, ?_⟩
  intro ξ hξ
  have h := referenceDensityPrincipalFrameCoefficient_quadratic_pos g g2 hg hg2 L q y ξ hξ
  convert h using 1
  simp only [Pi.star_apply, star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply,
    Fin.sum_univ_three]
  ring

/-! ### 2. Uniform compact scalar lower bound (constant before every profile/cutoff/input) -/

/-- One `lam > 0` for all `q ∈ [0,1]`, all `y` in an arbitrary compact `K` (possibly empty)
and all `ξ : Fin 3 → ℝ`, with the Euclidean `Σ ξ_i²`. -/
theorem exists_referenceDensityPrincipalFrameCoefficient_lower
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ K, ∀ ξ : Fin 3 → ℝ,
      lam * ∑ i : Fin 3, ξ i ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ξ i * ξ j := by
  let F : (ℝ × R3) × R3 → ℝ := fun z => ∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L z.1.1 z.1.2 i j * z.2 i * z.2 j
  have hF : Continuous F := by
    refine continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ => ?_))
    have hQ : Continuous (fun z : (ℝ × R3) × R3 =>
        referenceDensityPrincipalFrameCoefficient g g2 L z.1.1 z.1.2 i j) :=
      (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).continuous.comp
        continuous_fst
    have hi : Continuous (fun z : (ℝ × R3) × R3 => z.2 i) :=
      (PiLp.continuous_apply 2 _ i).comp continuous_snd
    have hj : Continuous (fun z : (ℝ × R3) × R3 => z.2 j) :=
      (PiLp.continuous_apply 2 _ j).comp continuous_snd
    exact (hQ.mul hi).mul hj
  have hS := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod hK).prod (isCompact_sphere (0 : R3) 1)
  obtain ⟨lam, hlam, hmin⟩ := hS.exists_forall_le' hF.continuousOn (a := (0 : ℝ)) (by
    intro z hz
    have hnorm : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    have hv : (z.2 : Fin 3 → ℝ) ≠ 0 := by
      intro hv
      have he : z.2 = 0 := by ext i; exact congrFun hv i
      simp [he] at hnorm
    exact referenceDensityPrincipalFrameCoefficient_quadratic_pos g g2 hg hg2 L z.1.1 z.1.2 _ hv)
  refine ⟨lam, hlam, ?_⟩
  intro q hq y hy ξ
  by_cases hξ : ξ = 0
  · subst hξ
    simp
  let v : R3 := WithLp.toLp 2 ξ
  have hvξ : ∀ i : Fin 3, v i = ξ i := fun i => rfl
  have hnormsq : ‖v‖ ^ 2 = ∑ i : Fin 3, ξ i ^ 2 := EuclideanSpace.real_norm_sq_eq v
  have hv0 : v ≠ 0 := by
    intro h0
    apply hξ
    funext i
    have h1 : v i = (0 : R3) i := by rw [h0]
    first
    | exact h1
    | simpa [v] using h1
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have hs : (‖v‖⁻¹ • v : R3) ∈ Metric.sphere (0 : R3) 1 := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hb := hmin ((q,y), ‖v‖⁻¹ • v) ⟨⟨hq, hy⟩, hs⟩
  have hscale : F ((q,y), ‖v‖⁻¹ • v) = ‖v‖⁻¹ ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ξ i * ξ j := by
    simp only [F, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    try simp only [hvξ]
    ring
  rw [hscale] at hb
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖v‖)
  have he : ‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ξ i * ξ j) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ξ i * ξ j := by
    field_simp [hn]
  rw [he, hnormsq] at hm
  rw [mul_comm lam]
  exact hm

/-- Exact closed-ball specialization: no smallness or profile premise. -/
theorem exists_referenceDensityPrincipalFrameCoefficient_lower_closedBall
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (y0 : R3) (ρ : ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall y0 ρ,
      ∀ ξ : Fin 3 → ℝ, lam * ∑ i : Fin 3, ξ i ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ξ i * ξ j :=
  exists_referenceDensityPrincipalFrameCoefficient_lower g g2 hg hg2 L
    (Metric.closedBall y0 ρ) (isCompact_closedBall y0 ρ)

/-! ### 3. Arbitrary real Hilbert vectors (no completeness/finite-dimensionality of `H`) -/

/-- Generic: a scalar lower bound for a real `3×3` coefficient array gives the same bound on
`Fin 3 → H` for any real inner product space `H`, through an orthonormal basis of the finite
span of the three vectors (Parseval in that span only). -/
theorem real_inner_fin3_lower {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : Fin 3 → Fin 3 → ℝ) (lam : ℝ)
    (ha : ∀ ξ : Fin 3 → ℝ, lam * ∑ i : Fin 3, ξ i ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, a i j * ξ i * ξ j)
    (x : Fin 3 → H) :
    lam * ∑ i : Fin 3, ‖x i‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, a i j * ⟪x j, x i⟫_ℝ := by
  let V : Submodule ℝ H := Submodule.span ℝ (Set.range x)
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range x)
  let b := stdOrthonormalBasis ℝ V
  let y : Fin 3 → V := fun i => ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩
  let c := fun (m : Fin (Module.finrank ℝ V)) (i : Fin 3) => ⟪b m, y i⟫_ℝ
  have hInner : ∀ i j : Fin 3, ⟪x j, x i⟫_ℝ = ∑ m, c m i * c m j := by
    intro i j
    calc ⟪x j, x i⟫_ℝ = ⟪y j, y i⟫_ℝ := rfl
      _ = ∑ m, ⟪y j, b m⟫_ℝ * ⟪b m, y i⟫_ℝ := (b.sum_inner_mul_inner (y j) (y i)).symm
      _ = ∑ m, c m i * c m j := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        simp only [c]
        rw [real_inner_comm (b m) (y j)]
        ring
  have hNorm : ∀ i : Fin 3, ‖x i‖ ^ 2 = ∑ m, c m i ^ 2 := by
    intro i
    rw [← real_inner_self_eq_norm_sq (x i), hInner i i]
    simp only [pow_two]
  have hScalar : ∀ m, lam * ∑ i : Fin 3, c m i ^ 2 ≤
      ∑ i : Fin 3, ∑ j : Fin 3, a i j * c m i * c m j := fun m => ha (c m)
  have hTerm : ∀ i j : Fin 3, a i j * ⟪x j, x i⟫_ℝ = ∑ m, a i j * c m i * c m j := by
    intro i j
    rw [hInner i j, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  calc lam * ∑ i : Fin 3, ‖x i‖ ^ 2 = lam * ∑ i : Fin 3, ∑ m, c m i ^ 2 := by
        simp only [hNorm]
    _ = lam * ∑ m, ∑ i : Fin 3, c m i ^ 2 := by rw [Finset.sum_comm]
    _ = ∑ m, lam * ∑ i : Fin 3, c m i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ m, ∑ i : Fin 3, ∑ j : Fin 3, a i j * c m i * c m j :=
        Finset.sum_le_sum (fun m _ => hScalar m)
    _ = ∑ i : Fin 3, ∑ m, ∑ j : Fin 3, a i j * c m i * c m j := Finset.sum_comm
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ m, a i j * c m i * c m j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, a i j * ⟪x j, x i⟫_ℝ := by
        simp only [hTerm]

/-! ### 4. Exact native Half/Neg dual pairing, zero order, all degrees including degree 0 -/

local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I0" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)

/-- `P(a, J b) = ⟪I₀ a, I₀ b⟫` on the order-zero space, from the supplied (opposite-sided)
native identity and real pairing symmetry. Every harmonic degree is kept. -/
theorem halfPairing_inclusion_eq_inner_zero (a b : SphereSobolev (1/2 : ℝ)) :
    PP a (JL b) = ⟪I0 a, I0 b⟫_ℝ := by
  have hSymm : PP a (JL b) = PP b (JL a) := by
    rw [sphereSobolevDualPairing_eq_tsum, sphereSobolevDualPairing_eq_tsum]
    apply tsum_congr
    intro k
    rw [sphereSobolevCoefficientL_inclusion, sphereSobolevCoefficientL_inclusion]
    exact real_inner_comm _ _
  have hFlip : PP b (JL a) = sphereSobolevDualPairing (-(1/2 : ℝ)) (JL a) b := by
    unfold sphereSobolevDualPairing
    exact real_inner_comm _ _
  have hNative := sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) a b
  exact hSymm.trans (hFlip.trans hNative)

/-- Generic zero-order Half/Neg pairing inequality for a coefficient array with a scalar bound. -/
theorem halfPairing_fin3_lower (a : Fin 3 → Fin 3 → ℝ) (lam : ℝ)
    (ha : ∀ ξ : Fin 3 → ℝ, lam * ∑ i : Fin 3, ξ i ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, a i j * ξ i * ξ j)
    (x : Fin 3 → SphereSobolev (1/2 : ℝ)) :
    lam * ∑ i : Fin 3, PP (x i) (JL (x i)) ≤
      ∑ i : Fin 3, ∑ j : Fin 3, a i j * PP (x j) (JL (x i)) := by
  have h := real_inner_fin3_lower a lam ha (fun i => I0 (x i))
  simp only [halfPairing_inclusion_eq_inner_zero, real_inner_self_eq_norm_sq]
  exact h

/-! ### Uniform package for the actual `Q`: one constant for scalar, Hilbert and pairing forms -/

theorem exists_referenceDensityPrincipalFrameCoefficient_uniform_package
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ K, ∀ ξ : Fin 3 → ℝ,
        lam * ∑ i : Fin 3, ξ i ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ξ i * ξ j) ∧
      (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ K, ∀ (H : Type u) [NormedAddCommGroup H]
        [InnerProductSpace ℝ H] (x : Fin 3 → H),
        lam * ∑ i : Fin 3, ‖x i‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ⟪x j, x i⟫_ℝ) ∧
      (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ K, ∀ x : Fin 3 → SphereSobolev (1/2 : ℝ),
        lam * ∑ i : Fin 3, PP (x i) (JL (x i)) ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          referenceDensityPrincipalFrameCoefficient g g2 L q y i j * PP (x j) (JL (x i))) := by
  obtain ⟨lam, hlam, hlow⟩ :=
    exists_referenceDensityPrincipalFrameCoefficient_lower g g2 hg hg2 L K hK
  refine ⟨lam, hlam, hlow, ?_, ?_⟩
  · intro q hq y hy H _ _ x
    exact real_inner_fin3_lower
      (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) lam (hlow q hq y hy) x
  · intro q hq y hy x
    exact halfPairing_fin3_lower
      (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) lam (hlow q hq y hy) x

/-! ### 5. Weighted integral consumers -/

/-- Generic weighted set integral: pointwise `lam * E ≤ T` on `K` with `w ≥ 0` on `K`, and the
genuine integrability of both weighted integrands. -/
theorem weighted_setIntegral_lower_of_pointwise {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K : Set α) (hK : MeasurableSet K) (lam : ℝ) (w E T : α → ℝ)
    (hw : ∀ p ∈ K, 0 ≤ w p) (hpt : ∀ p ∈ K, lam * E p ≤ T p)
    (hE : IntegrableOn (fun p => w p * E p) K μ) (hT : IntegrableOn (fun p => w p * T p) K μ) :
    lam * ∫ p in K, w p * E p ∂μ ≤ ∫ p in K, w p * T p ∂μ := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on (Integrable.const_mul hE lam) hT hK ?_
  intro p hp
  calc lam * (w p * E p) = w p * (lam * E p) := by ring
    _ ≤ w p * T p := mul_le_mul_of_nonneg_left (hpt p hp) (hw p hp)

lemma continuous_referenceDensityPrincipalFrameCoefficient_slice
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (i j : Fin 3) :
    Continuous (fun y : R3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) := by
  have hs : ContDiff ℝ ∞ (fun y : R3 => (q,y)) := contDiff_const.prodMk contDiff_id
  have h := (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp
    (f := fun y : R3 => (q,y)) hs
  exact h.continuous

lemma continuous_referenceDensityFamily_slice (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) : Continuous (fun y : R3 => referenceDensityFamily g L (q,y)) :=
  (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)

/-- Actual closed-ball Hilbert-valued weighted consumer with the actual density
`referenceDensityFamily g L (q,·)` times an arbitrary continuous nonnegative weight `φ`.
Integrability is discharged from continuity on the compact ball. -/
theorem exists_referenceDensity_weighted_hilbert_lower
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (y0 : R3) (ρ : ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ (H : Type u) [NormedAddCommGroup H]
      [InnerProductSpace ℝ H] (φ : R3 → ℝ), Continuous φ →
      (∀ y ∈ Metric.closedBall y0 ρ, 0 ≤ φ y) →
      ∀ x : R3 → Fin 3 → H, (∀ i : Fin 3, Continuous (fun y => x y i)) →
      lam * ∫ y in Metric.closedBall y0 ρ,
          (referenceDensityFamily g L (q,y) * φ y) * ∑ i : Fin 3, ‖x y i‖ ^ 2 ≤
        ∫ y in Metric.closedBall y0 ρ, (referenceDensityFamily g L (q,y) * φ y) *
          ∑ i : Fin 3, ∑ j : Fin 3,
            referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ⟪x y j, x y i⟫_ℝ := by
  obtain ⟨lam, hlam, hlow⟩ :=
    exists_referenceDensityPrincipalFrameCoefficient_lower_closedBall g g2 hg hg2 L y0 ρ
  refine ⟨lam, hlam, ?_⟩
  intro q hq H _ _ φ hφ hφnn x hx
  have hKc : IsCompact (Metric.closedBall y0 ρ) := isCompact_closedBall y0 ρ
  have hW : Continuous (fun y : R3 => referenceDensityFamily g L (q,y) * φ y) :=
    (continuous_referenceDensityFamily_slice g hg L q).mul hφ
  have hEc : Continuous (fun y : R3 => ∑ i : Fin 3, ‖x y i‖ ^ 2) :=
    continuous_finset_sum _ (fun i _ => (hx i).norm.pow 2)
  have hTc : Continuous (fun y : R3 => ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ⟪x y j, x y i⟫_ℝ) :=
    continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
      (continuous_referenceDensityPrincipalFrameCoefficient_slice g g2 hg hg2 L q i j).mul
        ((hx j).inner (hx i))))
  exact weighted_setIntegral_lower_of_pointwise volume (Metric.closedBall y0 ρ)
    measurableSet_closedBall lam
    (fun y => referenceDensityFamily g L (q,y) * φ y)
    (fun y => ∑ i : Fin 3, ‖x y i‖ ^ 2)
    (fun y => ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j * ⟪x y j, x y i⟫_ℝ)
    (fun y hy => mul_nonneg (referenceDensityFamily_pos g hg L (q,y)).le (hφnn y hy))
    (fun y hy => real_inner_fin3_lower
      (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) lam
      (hlow q hq y hy) (x y))
    ((hW.mul hEc).continuousOn.integrableOn_compact hKc)
    ((hW.mul hTc).continuousOn.integrableOn_compact hKc)

lemma continuous_halfPairing_inclusion {a b : R3 → SphereSobolev (1/2 : ℝ)}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun y => PP (a y) (JL (b y))) := by
  unfold sphereSobolevDualPairing
  exact ha.inner ((JL).continuous.comp hb)

/-- Actual closed-ball weighted zero-order Half/Neg pairing consumer, same `lam`, same `Q`,
actual density; all harmonic degrees (including degree 0) kept. -/
theorem exists_referenceDensity_weighted_halfPairing_lower
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (y0 : R3) (ρ : ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ φ : R3 → ℝ, Continuous φ →
      (∀ y ∈ Metric.closedBall y0 ρ, 0 ≤ φ y) →
      ∀ x : R3 → Fin 3 → SphereSobolev (1/2 : ℝ), (∀ i : Fin 3, Continuous (fun y => x y i)) →
      lam * ∫ y in Metric.closedBall y0 ρ,
          (referenceDensityFamily g L (q,y) * φ y) * ∑ i : Fin 3, PP (x y i) (JL (x y i)) ≤
        ∫ y in Metric.closedBall y0 ρ, (referenceDensityFamily g L (q,y) * φ y) *
          ∑ i : Fin 3, ∑ j : Fin 3,
            referenceDensityPrincipalFrameCoefficient g g2 L q y i j * PP (x y j) (JL (x y i)) := by
  obtain ⟨lam, hlam, hlow⟩ :=
    exists_referenceDensityPrincipalFrameCoefficient_lower_closedBall g g2 hg hg2 L y0 ρ
  refine ⟨lam, hlam, ?_⟩
  intro q hq φ hφ hφnn x hx
  have hKc : IsCompact (Metric.closedBall y0 ρ) := isCompact_closedBall y0 ρ
  have hW : Continuous (fun y : R3 => referenceDensityFamily g L (q,y) * φ y) :=
    (continuous_referenceDensityFamily_slice g hg L q).mul hφ
  have hEc : Continuous (fun y : R3 => ∑ i : Fin 3, PP (x y i) (JL (x y i))) :=
    continuous_finset_sum _ (fun i _ => continuous_halfPairing_inclusion (hx i) (hx i))
  have hTc : Continuous (fun y : R3 => ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j * PP (x y j) (JL (x y i))) :=
    continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
      (continuous_referenceDensityPrincipalFrameCoefficient_slice g g2 hg hg2 L q i j).mul
        (continuous_halfPairing_inclusion (hx j) (hx i))))
  exact weighted_setIntegral_lower_of_pointwise volume (Metric.closedBall y0 ρ)
    measurableSet_closedBall lam
    (fun y => referenceDensityFamily g L (q,y) * φ y)
    (fun y => ∑ i : Fin 3, PP (x y i) (JL (x y i)))
    (fun y => ∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j * PP (x y j) (JL (x y i)))
    (fun y hy => mul_nonneg (referenceDensityFamily_pos g hg L (q,y)).le (hφnn y hy))
    (fun y hy => halfPairing_fin3_lower
      (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) lam
      (hlow q hq y hy) (x y))
    ((hW.mul hEc).continuousOn.integrableOn_compact hKc)
    ((hW.mul hTc).continuousOn.integrableOn_compact hKc)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceCoFrame_injective
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityPrincipalFrameCoefficient_posDef
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceDensityPrincipalFrameCoefficient_lower
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceDensityPrincipalFrameCoefficient_lower_closedBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_inner_fin3_lower
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.halfPairing_inclusion_eq_inner_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceDensityPrincipalFrameCoefficient_uniform_package
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceDensity_weighted_hilbert_lower
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceDensity_weighted_halfPairing_lower
