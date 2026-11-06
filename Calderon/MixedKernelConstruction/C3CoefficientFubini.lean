import Calderon.MixedKernelConstruction.C3Coefficients
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable

/-- Actual scalar product-arm coefficient, with exactly the manuscript orientation. -/
def integralCoefficient {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (F : X × Y → ℝ) (q : X → ℝ) (c : ℝ) (y : Y) : ℝ :=
  c * ∫ x, F (x,y) * q x ∂μ

/-- The actual coefficient is L2 and has the sharp Cauchy–Schwarz/Fubini bound. -/
theorem integralCoefficient_memLp_and_norm_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X × Y → ℝ) (hF : MemLp F 2 (μ.prod ν))
    (q : Lp ℝ 2 μ) (c : ℝ) :
    ∃ hb : MemLp (integralCoefficient μ F q c) 2 ν,
      ‖hb.toLp (integralCoefficient μ F q c)‖ ≤ |c| * ‖q‖ * ‖hF.toLp F‖ := by
  let b := integralCoefficient μ F q c
  have hm : AEStronglyMeasurable b ν := by
    have hh := hF.aestronglyMeasurable.mul (Lp.memLp q).aestronglyMeasurable.comp_fst
    exact hh.prod_swap.integral_prod_right'.const_mul c
  have hsec : ∀ᵐ y ∂ν, MemLp (fun x => F (x,y)) 2 μ := by
    filter_upwards [hF.aestronglyMeasurable.prodMk_right, hF.integrable_sq.prod_left_ae]
      with y hy hs
    exact (memLp_two_iff_integrable_sq hy).mpr hs
  have hbound : ∀ᵐ y ∂ν, b y ^ 2 ≤ (c ^ 2 * ‖q‖ ^ 2) * ∫ x, F (x,y) ^ 2 ∂μ := by
    filter_upwards [hsec] with y hy
    let v : Lp ℝ 2 μ := hy.toLp (fun x => F (x,y))
    have hi : (∫ x, F (x,y) * q x ∂μ) = inner ℝ q v := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hy.coeFn_toLp] with x hx
      simp only [v, hx, Real.inner_apply, mul_comm]
    have habs : |b y| ≤ |c| * ‖q‖ * ‖v‖ := by
      change |c * ∫ x, F (x,y) * q x ∂μ| ≤ _
      rw [abs_mul, hi]
      exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm q v) (abs_nonneg c)).trans_eq
        (mul_assoc _ _ _).symm
    have hv : ‖v‖ ^ 2 = ∫ x, F (x,y) ^ 2 ∂μ := by
      calc
        ‖v‖ ^ 2 = ∫ x, (v x) ^ 2 ∂μ := by
          simpa only [L2.inner_def, Real.inner_apply, ← pow_two] using
            (real_inner_self_eq_norm_sq v).symm
        _ = ∫ x, F (x,y) ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards [hy.coeFn_toLp] with x hx
          exact congrArg (fun z : ℝ => z ^ 2) hx
    have hs := sq_le_sq₀ (abs_nonneg (b y))
      (mul_nonneg (mul_nonneg (abs_nonneg c) (norm_nonneg q)) (norm_nonneg v))
    have hsq := hs.mpr habs
    simpa only [sq_abs, mul_pow, hv, mul_assoc] using hsq
  have hupper : Integrable (fun y => (c ^ 2 * ‖q‖ ^ 2) * ∫ x, F (x,y) ^ 2 ∂μ) ν :=
    hF.integrable_sq.integral_prod_right.const_mul _
  have hbint : Integrable (fun y => b y ^ 2) ν := by
    apply hupper.mono' (hm.pow 2)
    filter_upwards [hbound] with y hy
    change ‖b y ^ 2‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (b y))] using hy
  have hb : MemLp b 2 ν := (memLp_two_iff_integrable_sq hm).mpr hbint
  refine ⟨hb, ?_⟩
  have hnormb : ‖hb.toLp b‖ ^ 2 = ∫ y, b y ^ 2 ∂ν := by
    calc
      ‖hb.toLp b‖ ^ 2 = ∫ y, ((hb.toLp b) y) ^ 2 ∂ν := by
        simpa only [L2.inner_def, Real.inner_apply, ← pow_two] using
          (real_inner_self_eq_norm_sq (hb.toLp b)).symm
      _ = ∫ y, b y ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards [hb.coeFn_toLp] with y hy
        exact congrArg (fun z : ℝ => z ^ 2) hy
  have hnormF : ‖hF.toLp F‖ ^ 2 = ∫ y, ∫ x, F (x,y) ^ 2 ∂μ ∂ν := by
    calc
      ‖hF.toLp F‖ ^ 2 = ∫ p, F p ^ 2 ∂μ.prod ν := by
        calc
          _ = ∫ p, ((hF.toLp F) p) ^ 2 ∂μ.prod ν := by
            simpa only [L2.inner_def, Real.inner_apply, ← pow_two] using
              (real_inner_self_eq_norm_sq (hF.toLp F)).symm
          _ = ∫ p, F p ^ 2 ∂μ.prod ν := by
            apply integral_congr_ae
            filter_upwards [hF.coeFn_toLp] with p hp
            exact congrArg (fun z : ℝ => z ^ 2) hp
      _ = ∫ y, ∫ x, F (x,y) ^ 2 ∂μ ∂ν := integral_prod_symm _ hF.integrable_sq
  have hbnd := integral_mono_ae hbint hupper hbound
  rw [← hnormb, integral_const_mul, ← hnormF] at hbnd
  have hpos : 0 ≤ |c| * ‖q‖ * ‖hF.toLp F‖ := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hpos).mp
  simpa only [mul_pow, sq_abs, mul_assoc] using hbnd

/-- The SAME Gram system gives the manuscript bound `M / μ_i` for the actual
scalar product-arm kernel, without assuming an L2-valued measurable currying. -/
theorem singularIntegralCoefficient_memLp_and_norm_le
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : Measure X) (ν : Measure Y) [SFinite m] [SFinite ν]
    (R : E →L[ℝ] Lp ℝ 2 m) {ι : Type*} (w : ι → E) (μ : ι → ℝ)
    (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    (F : X × Y → ℝ) (hF : MemLp F 2 (m.prod ν)) (i : ι) :
    ∃ hb : MemLp (integralCoefficient m F (R (w i)) (μ i ^ 2)⁻¹) 2 ν,
      ‖hb.toLp (integralCoefficient m F (R (w i)) (μ i ^ 2)⁻¹)‖ ≤
        (μ i)⁻¹ * ‖hF.toLp F‖ := by
  have hnorm : ‖R (w i)‖ = μ i := by
    apply (sq_eq_sq₀ (norm_nonneg _) (hμ i).le).mp
    calc
      ‖R (w i)‖ ^ 2 = inner ℝ (R (w i)) (R (w i)) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = μ i ^ 2 := by rw [hgram, if_pos rfl]
  obtain ⟨hb, hbound⟩ := integralCoefficient_memLp_and_norm_le m ν F hF (R (w i))
    (μ i ^ 2)⁻¹
  refine ⟨hb, ?_⟩
  have hc : |(μ i ^ 2)⁻¹| * ‖R (w i)‖ = (μ i)⁻¹ := by
    rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), hnorm]
    field_simp
  simpa only [hc] using hbound

/-- The original coefficients on the first cross arm have the source's μ-independent L2 bound. -/
theorem harmonicIntegralCoefficient_memLp_and_norm_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (m : Measure X) (ν : Measure Y) [SFinite m] [SFinite ν]
    (H : Submodule ℝ (Lp ℝ 2 m)) {ι : Type*} (w : HilbertBasis ι ℝ H)
    (F : X × Y → ℝ) (hF : MemLp F 2 (m.prod ν)) (i : ι) :
    ∃ hb : MemLp (integralCoefficient m F (w i : Lp ℝ 2 m) 1) 2 ν,
      ‖hb.toLp (integralCoefficient m F (w i : Lp ℝ 2 m) 1)‖ ≤ ‖hF.toLp F‖ := by
  obtain ⟨hb, hbound⟩ := integralCoefficient_memLp_and_norm_le m ν F hF
    (w i : Lp ℝ 2 m) 1
  have hn : ‖(w i : Lp ℝ 2 m)‖ = 1 := w.orthonormal.1 i
  exact ⟨hb, by simpa only [abs_one, hn, one_mul] using hbound⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
