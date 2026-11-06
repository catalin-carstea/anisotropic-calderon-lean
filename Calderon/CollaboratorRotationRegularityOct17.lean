import Calderon.CollaboratorRotationSobolevOct17
import TauCeti.Analysis.Sobolev.TestFunctionLp
import TauCeti.Analysis.PDE.EnergyForm.Sobolev

/-! Tangential (rotational) `H¹` regularity of the gradient of a weak solution on the unit ball
(helper for task 05). -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.Rotation
open TauCeti TauCeti.PDE EnergyBridge
open scoped Distributions Gradient Topology

theorem norm_rot_sub_le (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ) (z : R3) :
    ‖rot j k hjk θ z - z‖ ≤ ‖z‖ * |θ| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (f := fun t => rot j k hjk t z) (f' := fun t => gen j k (rot j k hjk t z)) (C := ‖z‖)
    (fun t _ => (hasDerivAt_rot j k hjk t z).hasDerivWithinAt)
    (fun t _ => by
      have := norm_gen_le j k hjk (rot j k hjk t z)
      rwa [LinearIsometryEquiv.norm_map] at this) convex_univ (Set.mem_univ 0) (Set.mem_univ θ)
  simpa [rot_zero, Real.norm_eq_abs] using h

theorem abs_matrixBilinearForm_le {A : Matrix (Fin 3) (Fin 3) ℝ} {m : ℝ}
    (hA : ∀ i j, |A i j| ≤ m) (η ξ : R3) :
    |matrixBilinearForm A η ξ| ≤ 9 * m * (‖η‖ * ‖ξ‖) := by
  rw [matrixBilinearForm_apply]
  have hη : ∀ i, |η i| ≤ ‖η‖ := fun i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le η i
  have hξ : ∀ i, |ξ i| ≤ ‖ξ‖ := fun i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i
  have key : ∀ i j, |η i * (A i j * ξ j)| ≤ m * (‖η‖ * ‖ξ‖) := by
    intro i j
    rw [abs_mul, abs_mul]
    have := hA i j
    have h1 := hη i; have h2 := hξ j
    have h0 : 0 ≤ |A i j| := abs_nonneg _
    calc |η i| * (|A i j| * |ξ j|) ≤ ‖η‖ * (m * ‖ξ‖) := by gcongr; exact h0.trans this
      _ = _ := by ring
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, mul_add]
  have := fun i j => abs_le.1 (key i j)
  rw [abs_le]
  constructor <;> nlinarith [this 0 0, this 0 1, this 0 2, this 1 0, this 1 1, this 1 2,
    this 2 0, this 2 1, this 2 2]

theorem abs_form_rot_sub_le (j k : Fin 3) (hjk : j ≠ k) (t : ℝ)
    {A A' : Matrix (Fin 3) (Fin 3) ℝ} {m d : ℝ}
    (hA' : ∀ i l, |A' i l| ≤ m) (hd : ∀ i l, |A' i l - A i l| ≤ d) (η ξ : R3) :
    |matrixBilinearForm A' (rot j k hjk t η) (rot j k hjk t ξ) - matrixBilinearForm A η ξ| ≤
      (18 * m * |t| + 9 * d) * (‖η‖ * ‖ξ‖) := by
  set R := rot j k hjk t
  have hsplit : matrixBilinearForm A' (R η) (R ξ) - matrixBilinearForm A η ξ =
      matrixBilinearForm A' (R η - η) (R ξ) + matrixBilinearForm A' η (R ξ - ξ) +
        matrixBilinearForm (A' - A) η ξ := by
    have h3 : matrixBilinearForm A' η ξ =
        matrixBilinearForm (A' - A) η ξ + matrixBilinearForm A η ξ := by
      rw [← matrixBilinearForm_add_apply, sub_add_cancel]
    rw [map_sub, map_sub, sub_apply, h3]
    ring
  have hm : 0 ≤ m := (abs_nonneg _).trans (hA' 0 0)
  have h1 := abs_matrixBilinearForm_le hA' (R η - η) (R ξ)
  have h2 := abs_matrixBilinearForm_le hA' η (R ξ - ξ)
  have h3 := abs_matrixBilinearForm_le (A := A' - A) (fun i l => hd i l) η ξ
  have e1 := norm_rot_sub_le j k hjk t η
  have e2 := norm_rot_sub_le j k hjk t ξ
  have nR : ‖R ξ‖ = ‖ξ‖ := LinearIsometryEquiv.norm_map _ _
  rw [nR] at h1
  rw [hsplit]
  have hη := norm_nonneg η; have hξ := norm_nonneg ξ; have ht := abs_nonneg t
  calc _ ≤ |matrixBilinearForm A' (R η - η) (R ξ)| + |matrixBilinearForm A' η (R ξ - ξ)| +
        |matrixBilinearForm (A' - A) η ξ| := abs_add_three _ _ _
    _ ≤ 9 * m * (‖η‖ * |t| * ‖ξ‖) + 9 * m * (‖η‖ * (‖ξ‖ * |t|)) + 9 * d * (‖η‖ * ‖ξ‖) := by
        gcongr
        · exact h1.trans (by gcongr)
        · exact h2.trans (by gcongr)
    _ = _ := by ring

/-- Uniform bound for a Lipschitz coefficient on the ball. -/
theorem exists_coeff_bound {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {K : NNReal}
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ x ∈ (ballOpens : Set R3), ∀ i j, |a x i j| ≤ m := by
  refine ⟨∑ i, ∑ j, |a 0 i j| + K, by positivity, fun x hx i j => ?_⟩
  have hx1 : ‖x‖ < 1 := by
    have : x ∈ Metric.ball (0 : R3) 1 := hx
    simpa using this
  have h := (hlip i j).dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at h
  have hs : |a 0 i j| ≤ ∑ i, ∑ j, |a 0 i j| :=
    (Finset.single_le_sum (f := fun j => |a 0 i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |a 0 i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hK : (K : ℝ) * ‖x‖ ≤ K := mul_le_of_le_one_right K.2 hx1.le
  have := abs_sub_abs_le_abs_sub (a x i j) (a 0 i j)
  linarith

theorem coeff_rot_sub_le {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {K : NNReal}
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) (j k : Fin 3) (hjk : j ≠ k) (t : ℝ)
    {y : R3} (hy : y ∈ (ballOpens : Set R3)) (i l : Fin 3) :
    |a (rot j k hjk t y) i l - a y i l| ≤ K * |t| := by
  have hy1 : ‖y‖ < 1 := by
    have : y ∈ Metric.ball (0 : R3) 1 := hy
    simpa using this
  have h := (hlip i l).dist_le_mul (rot j k hjk t y) y
  rw [Real.dist_eq, dist_eq_norm] at h
  have h2 := norm_rot_sub_le j k hjk t y
  have : ‖y‖ * |t| ≤ |t| := by nlinarith [abs_nonneg t, norm_nonneg y]
  calc _ ≤ K * ‖rot j k hjk t y - y‖ := h
    _ ≤ K * |t| := by gcongr; linarith

theorem L2_norm_mul_norm {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (g : Lp E 2 μ) (h : Lp F 2 μ) :
    Integrable (fun x => ‖g x‖ * ‖h x‖) μ ∧ ∫ x, ‖g x‖ * ‖h x‖ ∂μ ≤ ‖g‖ * ‖h‖ := by
  set G : Lp ℝ 2 μ := (Lp.memLp g).norm.toLp _
  set H : Lp ℝ 2 μ := (Lp.memLp h).norm.toLp _
  have hae : (fun x => ⟪G x, H x⟫_ℝ) =ᵐ[μ] fun x => ‖g x‖ * ‖h x‖ := by
    filter_upwards [(Lp.memLp g).norm.coeFn_toLp, (Lp.memLp h).norm.coeFn_toLp] with x h1 h2
    rw [h1, h2]; simp [mul_comm]
  have hG : ‖G‖ = ‖g‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]; congr 1; exact eLpNorm_norm _ (Lp.aestronglyMeasurable _)
  have hH : ‖H‖ = ‖h‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]; congr 1; exact eLpNorm_norm _ (Lp.aestronglyMeasurable _)
  refine ⟨(L2.integrable_inner G H).congr hae, ?_⟩
  rw [← integral_congr_ae hae, ← L2.inner_def, ← hG, ← hH]
  exact real_inner_le_norm _ _

theorem L2_integral_mul_eq_inner {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : Lp ℝ 2 μ) : ∫ x, f x * g x ∂μ = ⟪f, g⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]


theorem continuous_coeff {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {K : NNReal}
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) : Continuous a :=
  continuous_pi fun i => continuous_pi fun j => (hlip i j).continuous

theorem aestronglyMeasurable_form {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : Continuous a)
    {μ : Measure R3} {g h : R3 → R3} (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) :
    AEStronglyMeasurable (fun x => matrixBilinearForm (a x) (g x) (h x)) μ := by
  have h1 : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) μ :=
    (continuous_matrixBilinearForm.comp ha).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun x => matrixBilinearForm (a x) (g x)) μ :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (L : R3 →L[ℝ] R3 →L[ℝ] ℝ) (v : R3) => L v)
      (continuous_fst.clm_apply continuous_snd) h1 hg
  exact Continuous.comp_aestronglyMeasurable₂ (g := fun (L : R3 →L[ℝ] ℝ) (v : R3) => L v)
      (continuous_fst.clm_apply continuous_snd) h2 hh

theorem integrable_form {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : Continuous a) {m : ℝ}
    (hm : ∀ x ∈ (ballOpens : Set R3), ∀ i j, |a x i j| ≤ m)
    (g h : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) :
    Integrable (fun x => matrixBilinearForm (a x) (g x) (h x))
      ((volume : Measure R3).restrict ballOpens) := by
  refine Integrable.mono' ((L2_norm_mul_norm g h).1.const_mul (9 * m))
    (aestronglyMeasurable_form ha (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable h)) ?_
  filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
  rw [Real.norm_eq_abs]
  exact abs_matrixBilinearForm_le (hm x hx) _ _


theorem norm_gradient_rotate (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure R3) ballOpens 2) :
    ‖W1p.gradient (rotate j k hjk θ u)‖ = ‖W1p.gradient u‖ := by
  rw [rotate_apply, gradient_rotateFun, norm_rotGradL]

theorem rotated_form_bound {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {K : NNReal}
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) {m : ℝ}
    (hm : ∀ x ∈ (ballOpens : Set R3), ∀ i j, |a x i j| ≤ m)
    (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ) (φ v : W1p (volume : Measure R3) ballOpens 2) :
    |(∫ x in (ballOpens : Set R3),
        matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient (rotate j k hjk θ v) x)) -
      ∫ x in (ballOpens : Set R3),
        matrixBilinearForm (a x) (W1p.gradient (rotate j k hjk (-θ) φ) x) (W1p.gradient v x)| ≤
      (18 * m * |θ| + 9 * (K * |θ|)) *
        (‖W1p.gradient φ‖ * ‖W1p.gradient v‖) := by
  have ha := continuous_coeff hlip
  have hfint : Integrable (fun x =>
      matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient (rotate j k hjk θ v) x))
      ((volume : Measure R3).restrict ballOpens) :=
    integrable_form ha hm _ _
  have hcov := (setIntegral_ball_comp_rot j k hjk (-θ) (fun x =>
      matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient (rotate j k hjk θ v) x))).symm
  have hmp := measurePreserving_rot_ball j k hjk (-θ)
  have hq := hmp.quasiMeasurePreserving.tendsto_ae
  have hfg : (fun y => matrixBilinearForm (a (rot j k hjk (-θ) y))
      (W1p.gradient φ (rot j k hjk (-θ) y))
      (W1p.gradient (rotate j k hjk θ v) (rot j k hjk (-θ) y))) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun y => matrixBilinearForm (a (rot j k hjk (-θ) y))
        (rot j k hjk (-θ) (W1p.gradient (rotate j k hjk (-θ) φ) y))
        (rot j k hjk (-θ) (W1p.gradient v y)) := by
    filter_upwards [hq.eventually (gradient_rotate_ae j k hjk θ v),
      gradient_rotate_ae j k hjk (-θ) φ] with y h1 h2
    rw [h1, h2]
    simp only [rot_symm, rot_add, neg_neg, add_neg_cancel, neg_add_cancel, rot_zero]
  have hgint : Integrable (fun y => matrixBilinearForm (a (rot j k hjk (-θ) y))
        (rot j k hjk (-θ) (W1p.gradient (rotate j k hjk (-θ) φ) y))
        (rot j k hjk (-θ) (W1p.gradient v y))) ((volume : Measure R3).restrict ballOpens) := by
    refine Integrable.congr ?_ hfg
    exact (hmp.integrable_comp_emb (rot j k hjk (-θ)).toHomeomorph.measurableEmbedding).2 hfint
  have h2int := integrable_form ha hm (W1p.gradient (rotate j k hjk (-θ) φ)) (W1p.gradient v)
  rw [hcov, integral_congr_ae hfg, ← integral_sub hgint h2int]
  have hHold := L2_norm_mul_norm (W1p.gradient (rotate j k hjk (-θ) φ)) (W1p.gradient v)
  rw [norm_gradient_rotate] at hHold
  have hC : 0 ≤ 18 * m * |θ| + 9 * (K * |θ|) := by
    have : 0 ≤ m := (abs_nonneg _).trans (hm 0 (by simp [ballOpens, B]) 0 0)
    positivity
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hHold.1.const_mul (18 * m * |θ| + 9 * (K * |θ|))) ?_).trans ?_
  · filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    have hRy : rot j k hjk (-θ) y ∈ (ballOpens : Set R3) := (rot_mem_ball_iff j k hjk (-θ) y).2 hy
    have := abs_form_rot_sub_le j k hjk (-θ) (A := a y) (A' := a (rot j k hjk (-θ) y)) (m := m)
      (d := K * |θ|) (hm _ hRy) (fun i l => by
        have := coeff_rot_sub_le hlip j k hjk (-θ) hy i l
        rwa [abs_neg] at this) (W1p.gradient (rotate j k hjk (-θ) φ) y) (W1p.gradient v y)
    rwa [abs_neg] at this
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hHold.2 hC


theorem gradient_dq_ae (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ)
    (v : W1p (volume : Measure R3) ballOpens 2) :
    ⇑(W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v))) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => θ⁻¹ • (W1p.gradient (rotate j k hjk θ v) x - W1p.gradient v x) := by
  have h : W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v)) =
      θ⁻¹ • (W1p.gradient (rotate j k hjk θ v) - W1p.gradient v) := by
    rw [W1p.gradient_smul]
    congr 1
    exact map_sub W1p.gradientL _ _
  rw [h]
  filter_upwards [Lp.coeFn_smul θ⁻¹ (W1p.gradient (rotate j k hjk θ v) - W1p.gradient v),
    Lp.coeFn_sub (W1p.gradient (rotate j k hjk θ v)) (W1p.gradient v)] with x h1 h2
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply]

theorem value_dq_ae (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ)
    (v : W1p (volume : Measure R3) ballOpens 2) :
    W1p.value (θ⁻¹ • (rotate j k hjk θ v - v)) =
      θ⁻¹ • (W1p.value (rotate j k hjk θ v) - W1p.value v) := by
  rw [W1p.value_smul]
  congr 1
  exact map_sub W1p.valueL _ _

theorem dq_form_bound {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {K : NNReal}
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) {m : ℝ}
    (hm : ∀ x ∈ (ballOpens : Set R3), ∀ i j, |a x i j| ≤ m)
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    {v : W1p (volume : Measure R3) ballOpens 2}
    (hv : ∀ φ : W1p (volume : Measure R3) ballOpens 2,
      φ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 →
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient v x) =
        ∫ x in (ballOpens : Set R3), F x * W1p.value φ x)
    (j k : Fin 3) (hjk : j ≠ k) {θ : ℝ} (hθ : θ ≠ 0)
    {φ : W1p (volume : Measure R3) ballOpens 2}
    (hφ : φ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2) :
    |∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (W1p.gradient φ x)
        (W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v)) x)| ≤
      ((18 * m + 9 * K) * ‖W1p.gradient v‖ + ‖F‖) * ‖W1p.gradient φ‖ := by
  have ha := continuous_coeff hlip
  have hae : (fun x => matrixBilinearForm (a x) (W1p.gradient φ x)
        (W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v)) x)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => θ⁻¹ * (matrixBilinearForm (a x) (W1p.gradient φ x)
        (W1p.gradient (rotate j k hjk θ v) x) -
        matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient v x)) := by
    filter_upwards [gradient_dq_ae j k hjk θ v] with x hx
    rw [hx, map_smul, map_sub, smul_eq_mul]
  rw [integral_congr_ae hae, integral_const_mul, integral_sub (integrable_form ha hm _ _)
    (integrable_form ha hm _ _), hv φ hφ]
  have hψ := rotate_mem_w1p0Submodule j k hjk (-θ) hφ
  have h1 := rotated_form_bound hlip hm j k hjk θ φ v
  rw [hv _ hψ] at h1
  have hF : |(∫ x in (ballOpens : Set R3), F x * W1p.value (rotate j k hjk (-θ) φ) x) -
      ∫ x in (ballOpens : Set R3), F x * W1p.value φ x| ≤ ‖F‖ * (|θ| * ‖W1p.gradient φ‖) := by
    rw [L2_integral_mul_eq_inner, L2_integral_mul_eq_inner, ← inner_sub_right]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    have := norm_value_rotate_sub_le j k hjk (-θ) hφ
    rwa [abs_neg] at this
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm 0 (by simp [ballOpens, B]) 0 0)
  have htot : |(∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (W1p.gradient φ x)
        (W1p.gradient (rotate j k hjk θ v) x)) -
      ∫ x in (ballOpens : Set R3), F x * W1p.value φ x| ≤
      |θ| * (((18 * m + 9 * K) * ‖W1p.gradient v‖ + ‖F‖) * ‖W1p.gradient φ‖) := by
    calc _ ≤ _ := abs_sub_le _ (∫ x in (ballOpens : Set R3),
          F x * W1p.value (rotate j k hjk (-θ) φ) x) _
      _ ≤ (18 * m * |θ| + 9 * (K * |θ|)) * (‖W1p.gradient φ‖ * ‖W1p.gradient v‖) +
          ‖F‖ * (|θ| * ‖W1p.gradient φ‖) := add_le_add h1 hF
      _ = _ := by ring
  rw [abs_mul, abs_inv]
  have hθ' : 0 < |θ| := abs_pos.2 hθ
  rw [inv_mul_le_iff₀ hθ']
  exact htot


theorem le_div_of_sq_le {lam n C : ℝ} (hlam : 0 < lam) (hn : 0 ≤ n) (hC : 0 ≤ C)
    (h : lam * n ^ 2 ≤ C * n) : n ≤ C / lam := by
  rw [le_div_iff₀ hlam]
  rcases hn.eq_or_lt with h0 | hpos
  · subst h0
    simpa using hC
  · nlinarith

theorem norm_gradient_dq_le {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam : ℝ}
    {K : NNReal} (hlam : 0 < lam)
    (hell : ∀ x ∈ (ballOpens : Set R3), ∀ ξ : R3, lam * ‖ξ‖ ^ 2 ≤ matrixBilinearForm (a x) ξ ξ)
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) {m : ℝ}
    (hm : ∀ x ∈ (ballOpens : Set R3), ∀ i j, |a x i j| ≤ m)
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    {v : W1p (volume : Measure R3) ballOpens 2}
    (hv0 : v ∈ w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hv : ∀ φ : W1p (volume : Measure R3) ballOpens 2,
      φ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 →
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient v x) =
        ∫ x in (ballOpens : Set R3), F x * W1p.value φ x)
    (j k : Fin 3) (hjk : j ≠ k) {θ : ℝ} (hθ : θ ≠ 0) :
    ‖W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v))‖ ≤
      ((18 * m + 9 * K) * ‖W1p.gradient v‖ + ‖F‖) / lam := by
  have hw : θ⁻¹ • (rotate j k hjk θ v - v) ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (rotate_mem_w1p0Submodule j k hjk θ hv0) hv0)
  have h := dq_form_bound hlip hm hv j k hjk hθ hw
  have hell' : lam * ‖W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v))‖ ^ 2 ≤
      ∫ x in (ballOpens : Set R3),
      matrixBilinearForm (a x) (W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v)) x)
        (W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v)) x) := by
    rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq, ← integral_const_mul]
    refine integral_mono_ae ((W1p.integrable_norm_gradient_sq _).const_mul lam)
      (integrable_form (continuous_coeff hlip) hm _ _) ?_
    filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
    exact hell x hx _
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm 0 (by simp [ballOpens, B]) 0 0)
  exact le_div_of_sq_le hlam (norm_nonneg _) (by positivity)
    (hell'.trans ((le_abs_self _).trans h))


/-- `L²` class of a test function on the ball. -/
@[inline, reducible]
def tLp (ψ : 𝓓(ballOpens, ℝ)) : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
  testFunctionLp (mu := (volume : Measure R3)) 2 ψ

theorem inner_tLp_value_rotate (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ) (ψ : 𝓓(ballOpens, ℝ))
    (u : W1p (volume : Measure R3) ballOpens 2) :
    ⟪tLp ψ, W1p.value (rotate j k hjk θ u)⟫_ℝ =
      ⟪tLp (compTestFunction (rot j k hjk (-θ)) (rot_mem_ball_iff j k hjk (-θ)) ψ),
        W1p.value u⟫_ℝ := by
  rw [← L2_integral_mul_eq_inner, ← L2_integral_mul_eq_inner]
  have h1 : ∫ x in (ballOpens : Set R3), tLp ψ x * W1p.value (rotate j k hjk θ u) x =
      ∫ x in (ballOpens : Set R3), ψ x * W1p.value u (rot j k hjk θ x) := by
    refine integral_congr_ae ?_
    filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ,
      value_rotate_ae j k hjk θ u] with x h1 h2
    rw [h1, h2]
  have h2 : ∫ x in (ballOpens : Set R3),
      tLp (compTestFunction (rot j k hjk (-θ)) (rot_mem_ball_iff j k hjk (-θ)) ψ) x *
        W1p.value u x =
      ∫ x in (ballOpens : Set R3), ψ (rot j k hjk (-θ) x) * W1p.value u x := by
    refine integral_congr_ae ?_
    filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2
      (compTestFunction (rot j k hjk (-θ)) (rot_mem_ball_iff j k hjk (-θ)) ψ)] with x h1
    rw [h1, compTestFunction_apply]
  rw [h1, h2, ← setIntegral_ball_comp_rot j k hjk (-θ)]
  simp only [rot_add, add_neg_cancel, rot_zero]

theorem test_rot_sub_le (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ)) {M : ℝ}
    (hM : ∀ x, ‖∇ (ψ : R3 → ℝ) x‖ ≤ M) (s : ℝ) (y : R3) :
    |ψ (rot j k hjk s y) - ψ y| ≤ M * |s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (f := fun t => ψ (rot j k hjk t y))
    (f' := fun t => fderiv ℝ (ψ : R3 → ℝ) (rot j k hjk t y) (gen j k (rot j k hjk t y))) (C := M)
    (fun t _ => (((ψ.contDiff.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_rot j k hjk t y)).hasDerivWithinAt)
    (fun t _ => (norm_fderiv_apply_gen_le j k hjk ψ _).trans (hM _)) convex_univ
    (Set.mem_univ 0) (Set.mem_univ s)
  simpa [rot_zero, Real.norm_eq_abs] using h

theorem tendsto_test_dq (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ)) (y : R3) :
    Filter.Tendsto (fun θ : ℝ => θ⁻¹ * (ψ (rot j k hjk (-θ) y) - ψ y)) (𝓝[≠] 0)
      (𝓝 (-fderiv ℝ (ψ : R3 → ℝ) y (gen j k y))) := by
  have hd : HasDerivAt (fun t => ψ (rot j k hjk t y))
      (fderiv ℝ (ψ : R3 → ℝ) (rot j k hjk (-0) y) (gen j k (rot j k hjk (-0) y))) (-0) :=
    ((ψ.contDiff.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt _
      (hasDerivAt_rot j k hjk (-0) y)
  have hd2 := hd.scomp (0 : ℝ) (hasDerivAt_neg 0)
  have := hd2.tendsto_slope_zero
  simp only [neg_zero, rot_zero, zero_add, smul_eq_mul, Function.comp_def] at this
  simpa using this


theorem integral_test_mul_dq (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ) (ψ : 𝓓(ballOpens, ℝ))
    (v : W1p (volume : Measure R3) ballOpens 2) :
    ∫ x in (ballOpens : Set R3), ψ x * W1p.value (θ⁻¹ • (rotate j k hjk θ v - v)) x =
      ∫ y in (ballOpens : Set R3), θ⁻¹ * (ψ (rot j k hjk (-θ) y) - ψ y) * W1p.value v y := by
  have h1 : ∫ x in (ballOpens : Set R3), ψ x * W1p.value (θ⁻¹ • (rotate j k hjk θ v - v)) x =
      ⟪tLp ψ, W1p.value (θ⁻¹ • (rotate j k hjk θ v - v))⟫_ℝ := by
    rw [← L2_integral_mul_eq_inner]
    refine integral_congr_ae ?_
    filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ] with x h1
    rw [h1]
  rw [h1, value_dq_ae, inner_smul_right, inner_sub_right, inner_tLp_value_rotate,
    ← inner_sub_left, ← L2_integral_mul_eq_inner, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub
      (tLp (compTestFunction (rot j k hjk (-θ)) (rot_mem_ball_iff j k hjk (-θ)) ψ)) (tLp ψ),
    testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ,
    testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2
      (compTestFunction (rot j k hjk (-θ)) (rot_mem_ball_iff j k hjk (-θ)) ψ)] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, compTestFunction_apply]
  ring

theorem isFiniteMeasure_ball :
    IsFiniteMeasure ((volume : Measure R3).restrict (ballOpens : Set R3)) :=
  isFiniteMeasure_restrict.2 (measure_ball_lt_top (x := (0 : R3)) (r := 1)).ne

attribute [instance] isFiniteMeasure_ball

theorem tendsto_integral_dq (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ))
    (v : W1p (volume : Measure R3) ballOpens 2) :
    Filter.Tendsto (fun θ : ℝ =>
      ∫ y in (ballOpens : Set R3), θ⁻¹ * (ψ (rot j k hjk (-θ) y) - ψ y) * W1p.value v y)
      (𝓝[≠] 0)
      (𝓝 (∫ y in (ballOpens : Set R3), -fderiv ℝ (ψ : R3 → ℝ) y (gen j k y) * W1p.value v y)) := by
  obtain ⟨M, hM⟩ := (continuous_gradient_testFunction ψ).bounded_above_of_compact_support
    (hasCompactSupport_gradient_testFunction ψ)
  have hvint : Integrable (W1p.value v) ((volume : Measure R3).restrict ballOpens) :=
    (Lp.memLp (W1p.value v)).integrable one_le_two
  refine tendsto_integral_filter_of_dominated_convergence (fun y => M * ‖W1p.value v y‖) ?_ ?_
    (hvint.norm.const_mul M) ?_
  · refine Filter.Eventually.of_forall fun θ => ?_
    exact (((continuous_const.mul ((ψ.continuous.comp (rot j k hjk (-θ)).continuous).sub
      ψ.continuous))).aestronglyMeasurable).mul (Lp.aestronglyMeasurable _)
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    refine Filter.Eventually.of_forall fun y => ?_
    have hθ' : θ ≠ 0 := hθ
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv]
    gcongr
    have := test_rot_sub_le j k hjk ψ hM (-θ) y
    rw [abs_neg] at this
    rw [inv_mul_le_iff₀ (abs_pos.2 hθ')]
    linarith
  · exact Filter.Eventually.of_forall fun y =>
      (tendsto_test_dq j k hjk ψ y).mul_const _


theorem weak_coord (v : W1p (volume : Measure R3) ballOpens 2) (j k : Fin 3) (hjk : j ≠ k) :
    HasWeakLineDerivOn volume ballOpens (fun x : R3 => x j * W1p.value v x)
      (fun x => x j * W1p.gradient v x k) (EuclideanSpace.single k 1) := by
  have h := ((W1p.hasWeakFDerivOn v).hasWeakLineDerivOn (EuclideanSpace.single k (1:ℝ))).contDiff_smul
    (ψ := ⇑(EuclideanSpace.proj j : R3 →L[ℝ] ℝ)) (ContinuousLinearMap.contDiff _)
  refine (h.congr_ae (Filter.Eventually.of_forall fun x => ?_)).congr_ae_deriv
    (Filter.Eventually.of_forall fun x => ?_)
  · simp [smul_eq_mul]
  · beta_reduce
    rw [ContinuousLinearMap.fderiv]
    simp [hjk, EuclideanSpace.inner_single_right]


theorem inner_gen (j k : Fin 3) (y w : R3) :
    ⟪gen j k y, w⟫_ℝ = y j * w k - y k * w j := by
  simp [gen, inner_sub_left, inner_smul_left, EuclideanSpace.inner_single_left]

theorem fderiv_gen (j k : Fin 3) (ψ : 𝓓(ballOpens, ℝ)) (y : R3) :
    fderiv ℝ (ψ : R3 → ℝ) y (gen j k y) =
      y j * lineDeriv ℝ (ψ : R3 → ℝ) y (EuclideanSpace.single k 1) -
        y k * lineDeriv ℝ (ψ : R3 → ℝ) y (EuclideanSpace.single j 1) := by
  have hd : DifferentiableAt ℝ (ψ : R3 → ℝ) y := (ψ.contDiff.differentiable (by simp)) y
  rw [hd.lineDeriv_eq_fderiv, hd.lineDeriv_eq_fderiv, gen, map_sub, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul]

theorem integral_fderiv_gen_mul (v : W1p (volume : Measure R3) ballOpens 2) (j k : Fin 3)
    (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ)) :
    ∫ y in (ballOpens : Set R3), -fderiv ℝ (ψ : R3 → ℝ) y (gen j k y) * W1p.value v y =
      ∫ y in (ballOpens : Set R3), ψ y * ⟪gen j k y, W1p.gradient v y⟫_ℝ := by
  have h1 := weak_coord v j k hjk
  have h2 := weak_coord v k j hjk.symm
  have I1 := h1.integral_lineDeriv_smul_eq_neg_integral_smul ψ
  have I2 := h2.integral_lineDeriv_smul_eq_neg_integral_smul ψ
  have A1 := integrable_lineDeriv_smul_of_locallyIntegrableOn h1.locallyIntegrableOn ψ
    (EuclideanSpace.single k 1)
  have A2 := integrable_lineDeriv_smul_of_locallyIntegrableOn h2.locallyIntegrableOn ψ
    (EuclideanSpace.single j 1)
  have B1 := integrable_smul_of_locallyIntegrableOn h1.locallyIntegrableOn_deriv ψ
  have B2 := integrable_smul_of_locallyIntegrableOn h2.locallyIntegrableOn_deriv ψ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      have : fderiv ℝ (ψ : R3 → ℝ) y = 0 :=
        fderiv_of_notMem_tsupport ℝ fun h => hy (ψ.tsupport_subset h)
      simp [this]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hy (ψ.tsupport_subset h)]
      simp)]
  calc ∫ y, -fderiv ℝ (ψ : R3 → ℝ) y (gen j k y) * W1p.value v y
      = ∫ y, (-(lineDeriv ℝ (ψ : R3 → ℝ) y (EuclideanSpace.single k 1) •
          (y j * W1p.value v y)) + lineDeriv ℝ (ψ : R3 → ℝ) y (EuclideanSpace.single j 1) •
          (y k * W1p.value v y)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [fderiv_gen, smul_eq_mul]
        ring
    _ = ∫ y, ((ψ : R3 → ℝ) y • (y j * W1p.gradient v y k) -
          (ψ : R3 → ℝ) y • (y k * W1p.gradient v y j)) := by
        have hadd := integral_add A1.neg A2
        simp only [Pi.neg_apply] at hadd
        rw [hadd, integral_neg, I1, I2, integral_sub B1 B2]
        ring
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [inner_gen, smul_eq_mul]
        ring


theorem norm_tLp (φ : 𝓓(ballOpens, ℝ)) :
    ‖tLp φ‖ = (eLpNorm (φ : R3 → ℝ) 2 (volume : Measure R3)).toReal := by
  rw [← enorm_testFunctionLp_eq_eLpNorm, toReal_enorm]

theorem norm_mul_innerSL_single_le {a b : ℝ} (h : a = b) (g : R3) (i : Fin 3) :
    ‖b * innerSL ℝ g (EuclideanSpace.single i (1:ℝ))‖ ≤ ‖a‖ * ‖g‖ := by
  subst h
  rw [norm_mul]
  gcongr
  rw [innerSL_apply_apply]
  refine (norm_inner_le_norm _ _).trans ?_
  simp

theorem abs_integral_test_dq_le (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ)
    (v : W1p (volume : Measure R3) ballOpens 2) (φ : 𝓓(ballOpens, ℝ)) (i : Fin 3) :
    |∫ x in (ballOpens : Set R3), lineDeriv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) *
        W1p.value (θ⁻¹ • (rotate j k hjk θ v - v)) x| ≤
      (eLpNorm (φ : R3 → ℝ) 2 (volume : Measure R3)).toReal *
        ‖W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v))‖ := by
  have hw := (W1p.hasWeakFDerivOn (θ⁻¹ • (rotate j k hjk θ v - v))).hasWeakLineDerivOn
    (EuclideanSpace.single i (1:ℝ))
  have I := hw.integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [smul_eq_mul] at I
  have e1 := setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul (μ := (volume : Measure R3))
    (w := W1p.value (θ⁻¹ • (rotate j k hjk θ v - v))) φ (EuclideanSpace.single i (1:ℝ))
  have e2 := setIntegral_smul_eq_integral_smul (μ := (volume : Measure R3))
    (w := fun x => innerSL ℝ (W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v)) x)
      (EuclideanSpace.single i (1:ℝ))) φ
  simp only [smul_eq_mul] at e1 e2
  rw [e1, I, ← e2, abs_neg, ← Real.norm_eq_abs]
  have hH := L2_norm_mul_norm (tLp φ) (W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v)))
  have hn := norm_tLp φ
  refine (norm_integral_le_of_norm_le hH.1 ?_).trans (hH.2.trans_eq
    (congrArg (· * ‖W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v))‖) hn))
  have hae := testFunctionLp_apply_ae (mu := (volume : Measure R3)) (Omega := ballOpens) 2 φ
  exact hae.mono fun x hx => norm_mul_innerSL_single_le hx _ i

theorem rotational_bound (j k : Fin 3) (hjk : j ≠ k)
    (v : W1p (volume : Measure R3) ballOpens 2) {C : ℝ}
    (hC : ∀ θ : ℝ, θ ≠ 0 → ‖W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v))‖ ≤ C)
    (i : Fin 3) (φ : 𝓓(ballOpens, ℝ)) :
    |∫ x, lineDeriv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) *
        ⟪gen j k x, W1p.gradient v x⟫_ℝ| ≤
      C * (eLpNorm (φ : R3 → ℝ) 2 (volume : Measure R3)).toReal := by
  let ψ : 𝓓(ballOpens, ℝ) := TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1:ℝ)) φ
  have hcoe : ∀ x, ψ x = lineDeriv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) :=
    fun x => TestFunction.lineDerivCLM_apply_of_le le_top
  have e0 := setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul (μ := (volume : Measure R3))
    (w := fun x => ⟪gen j k x, W1p.gradient v x⟫_ℝ) φ (EuclideanSpace.single i (1:ℝ))
  simp only [smul_eq_mul] at e0
  rw [← e0]
  have hlim := tendsto_integral_dq j k hjk ψ v
  rw [integral_fderiv_gen_mul v j k hjk ψ] at hlim
  have hfun : (fun θ : ℝ => ∫ y in (ballOpens : Set R3),
      θ⁻¹ * (ψ (rot j k hjk (-θ) y) - ψ y) * W1p.value v y) =
      fun θ : ℝ => ∫ x in (ballOpens : Set R3), ψ x * W1p.value (θ⁻¹ • (rotate j k hjk θ v - v)) x :=
    funext fun θ => (integral_test_mul_dq j k hjk θ ψ v).symm
  rw [hfun] at hlim
  simp only [hcoe] at hlim
  refine le_of_tendsto hlim.abs ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  refine (abs_integral_test_dq_le j k hjk θ v φ i).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hC θ hθ) ENNReal.toReal_nonneg


theorem continuous_gen (j k : Fin 3) : Continuous (gen j k) := by
  unfold gen; fun_prop

theorem locallyIntegrableOn_rotational (j k : Fin 3) (hjk : j ≠ k)
    (v : W1p (volume : Measure R3) ballOpens 2) :
    LocallyIntegrableOn (fun x => ⟪gen j k x, W1p.gradient v x⟫_ℝ) ballOpens volume := by
  refine IntegrableOn.locallyIntegrableOn ?_
  refine Integrable.mono' ((Lp.memLp (W1p.gradient v)).integrable one_le_two).norm
    ((continuous_gen j k).aestronglyMeasurable.inner (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
  refine (norm_inner_le_norm _ _).trans ?_
  have h1 : ‖gen j k x‖ ≤ 1 := by
    refine (norm_gen_le j k hjk x).trans ?_
    have : x ∈ Metric.ball (0 : R3) 1 := hx
    rw [Metric.mem_ball, dist_zero_right] at this
    exact this.le
  calc ‖gen j k x‖ * ‖W1p.gradient v x‖ ≤ 1 * ‖W1p.gradient v x‖ := by gcongr
    _ = _ := one_mul _

theorem memLp_smul_single (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (i : Fin 3) :
    MemLp (fun x => (f : R3 → ℝ) x • EuclideanSpace.single i (1:ℝ)) 2
      ((volume : Measure R3).restrict ballOpens) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1:ℝ))).comp_memLp'
    (Lp.memLp f)

theorem assemble_gradient {u : R3 → ℝ} (hu : LocallyIntegrableOn u ballOpens volume)
    (g : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (hg : ∀ i, HasWeakLineDerivOn volume ballOpens u (g i) (EuclideanSpace.single i 1)) :
    ∃ G : Lp R3 2 ((volume : Measure R3).restrict ballOpens),
      HasWeakFDerivOn volume ballOpens u (fun x => innerSL ℝ (G x)) := by
  have hmem : MemLp (fun x => ∑ i, (g i : R3 → ℝ) x • EuclideanSpace.single i (1:ℝ)) 2
      ((volume : Measure R3).restrict ballOpens) :=
    memLp_finsetSum' Finset.univ fun i _ => memLp_smul_single (g i) i
  refine ⟨hmem.toLp _, ?_⟩
  refine HasWeakFDerivOn.congr_ae_deriv (U := fun x => innerSL ℝ
    (∑ i, (g i : R3 → ℝ) x • EuclideanSpace.single i (1:ℝ))) ?_
    (hmem.coeFn_toLp.mono fun x hx => congrArg (innerSL ℝ) hx.symm)
  refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.hasWeakFDerivOn_of_forall hu fun i => ?_
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  refine (hg i).congr_ae_deriv (Filter.Eventually.of_forall fun x => ?_)
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]


/-- If `v ∈ H¹₀(B)` solves `-div(a ∇v) = F` weakly on `B` (tested against all of `H¹₀(B)`), with
`a` Lipschitz and uniformly elliptic on `B`, then the rotational derivative
`⟪gen j k x, ∇v x⟫ = x_j ∂_k v - x_k ∂_j v` has a weak gradient in `L²(B)`. -/
theorem exists_hasWeakFDerivOn_rotational {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam : ℝ}
    {K : NNReal} (hlam : 0 < lam)
    (hell : ∀ x ∈ (ballOpens : Set R3), ∀ ξ : R3, lam * ‖ξ‖ ^ 2 ≤ matrixBilinearForm (a x) ξ ξ)
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j))
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    {v : W1p (volume : Measure R3) ballOpens 2}
    (hv0 : v ∈ w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hv : ∀ φ : W1p (volume : Measure R3) ballOpens 2,
      φ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 →
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient v x) =
        ∫ x in (ballOpens : Set R3), F x * W1p.value φ x)
    (j k : Fin 3) (hjk : j ≠ k) :
    ∃ G : Lp R3 2 ((volume : Measure R3).restrict ballOpens),
      HasWeakFDerivOn volume ballOpens (fun x => ⟪gen j k x, W1p.gradient v x⟫_ℝ)
        (fun x => innerSL ℝ (G x)) := by
  have hmex := exists_coeff_bound hlip
  have hm0 : 0 ≤ hmex.choose := hmex.choose_spec.1
  have hm := hmex.choose_spec.2
  have hC : ∀ θ : ℝ, θ ≠ 0 → ‖W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v))‖ ≤
      ((18 * hmex.choose + 9 * K) * ‖W1p.gradient v‖ + ‖F‖) / lam :=
    fun θ hθ => norm_gradient_dq_le hlam hell hlip hm hv0 hv j k hjk hθ
  have hC0 : 0 ≤ ((18 * hmex.choose + 9 * K) * ‖W1p.gradient v‖ + ‖F‖) / lam := by positivity
  have hz := locallyIntegrableOn_rotational j k hjk v
  have hg : ∀ i : Fin 3, ∃ g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens),
      ‖g‖ ≤ ((18 * hmex.choose + 9 * K) * ‖W1p.gradient v‖ + ‖F‖) / lam ∧
        HasWeakLineDerivOn volume ballOpens (fun x => ⟪gen j k x, W1p.gradient v x⟫_ℝ) g
          (EuclideanSpace.single i 1) := fun i =>
    exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le hz _ hC0
      (rotational_bound j k hjk v hC i)
  exact assemble_gradient hz (fun i => (hg i).choose) fun i => (hg i).choose_spec.2

end OAI.AnisotropicCalderon.Rotation
