import Calderon.CompactContinuousDilationELpNorm
import Calderon.LpDilationScaling
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
namespace OAI.AnisotropicCalderon.DirichletFamily

theorem tendsto_eLpNorm_inv_dilation_sub_of_memLp
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : R3 → V) (hf : MemLp f 2 (volume : Measure R3)) :
    Tendsto (fun r : ℝ => eLpNorm (fun x : R3 => f (r⁻¹ • x) - f x) 2 volume)
      (𝓝 1) (𝓝 0) := by
  let c : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (r ^ ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal))
  have hcReal : Tendsto
      (fun r : ℝ => r ^ ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal))
      (𝓝 1) (𝓝 1) := by
    simpa only [id_eq,Real.one_rpow] using
      (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 1) (𝓝 1)).rpow_const
        (Or.inl (one_ne_zero : (1 : ℝ) ≠ 0))
  have hc : Tendsto c (𝓝 1) (𝓝 1) := by
    simpa only [Function.comp_def,c,ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hcReal
  have hcBound : ∀ᶠ r : ℝ in 𝓝 1, c r ≤ 2 :=
    (hc.eventually (gt_mem_nhds (show (1 : ℝ≥0∞) < 2 by norm_num))).mono
      (fun _ h => h.le)
  have hInv : Tendsto (fun r : ℝ => r⁻¹) (𝓝 1) (𝓝 1) := by
    simpa only [id_eq,inv_one] using
      (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 1) (𝓝 1)).inv₀ one_ne_zero
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨η,hη,hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (show (4 : ℝ≥0∞) ≠ ∞ by norm_num) hε.ne'
  have hηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.mpr hη
  have hApprox : ∃ g : R3 → V, HasCompactSupport g ∧
      eLpNorm (f-g) 2 (volume : Measure R3) ≤ (η : ℝ≥0∞) ∧
      Continuous g ∧ MemLp g 2 (volume : Measure R3) :=
    MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure R3)) (f := f)
      (ε := (η : ℝ≥0∞)) (by norm_num) hf hηpos.ne'
  obtain ⟨g,hgc,hfg,hg,hgm⟩ := hApprox
  have hgLim : Tendsto
      (fun r : ℝ => eLpNorm (fun x : R3 => g (r⁻¹ • x) - g x) 2 volume)
      (𝓝 1) (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_eLpNorm_dilation_sub_of_continuous_compactSupport g hg hgc).comp hInv
  have hgSmall : ∀ᶠ r : ℝ in 𝓝 1,
      eLpNorm (fun x : R3 => g (r⁻¹ • x) - g x) 2 volume ≤ η :=
    ENNReal.tendsto_nhds_zero.mp hgLim η hηpos
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num),hcBound,hgSmall]
    with r hr hcr hgr
  have hdecomp : (fun x : R3 => f (r⁻¹ • x) - f x) =
      ((fun x : R3 => (f - g) (r⁻¹ • x)) +
        (fun x : R3 => g (r⁻¹ • x) - g x)) + (g - f) := by
    funext x
    simp only [Pi.add_apply,Pi.sub_apply]
    abel
  have hscale : eLpNorm (fun x : R3 => (f-g) (r⁻¹ • x)) 2 volume =
      c r * eLpNorm (f-g) 2 volume :=
    eLpNorm_comp_inv_smul_R3 (f-g) hr 2
  have hgf : eLpNorm (g-f) 2 volume ≤ η := by
    rw [eLpNorm_sub_comm g f]
    exact hfg
  calc
    eLpNorm (fun x : R3 => f (r⁻¹ • x) - f x) 2 volume
      = eLpNorm (((fun x : R3 => (f-g) (r⁻¹ • x)) +
          (fun x : R3 => g (r⁻¹ • x) - g x)) + (g-f)) 2 volume := by rw [hdecomp]
    _ ≤ eLpNorm ((fun x : R3 => (f-g) (r⁻¹ • x)) +
          (fun x : R3 => g (r⁻¹ • x) - g x)) 2 volume + eLpNorm (g-f) 2 volume :=
      eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (fun x : R3 => (f-g) (r⁻¹ • x)) 2 volume +
          eLpNorm (fun x : R3 => g (r⁻¹ • x) - g x) 2 volume) + eLpNorm (g-f) 2 volume :=
      add_le_add
        (eLpNorm_add_le
          (f := fun x : R3 => (f-g) (r⁻¹ • x))
          (g := fun x : R3 => g (r⁻¹ • x) - g x)
          (p := (2 : ℝ≥0∞)) (μ := (volume : Measure R3)) (by norm_num)) le_rfl
    _ = (c r * eLpNorm (f-g) 2 volume +
          eLpNorm (fun x : R3 => g (r⁻¹ • x) - g x) 2 volume) + eLpNorm (g-f) 2 volume :=
      by rw [hscale]
    _ ≤ (2 * (η : ℝ≥0∞) + η) + η :=
      add_le_add (add_le_add (mul_le_mul' hcr hfg) hgr) hgf
    _ = (η : ℝ≥0∞) * 4 := by ring
    _ ≤ ε := hηε.le

theorem tendsto_eLpNorm_dilation_sub_of_memLp
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : R3 → V) (hf : MemLp f 2 (volume : Measure R3)) :
    Tendsto (fun a : ℝ => eLpNorm (fun x : R3 => f (a • x) - f x) 2 volume)
      (𝓝 1) (𝓝 0) := by
  have hInv : Tendsto (fun a : ℝ => a⁻¹) (𝓝 1) (𝓝 1) := by
    simpa only [id_eq,inv_one] using
      (tendsto_id : Tendsto (fun a : ℝ => a) (𝓝 1) (𝓝 1)).inv₀ one_ne_zero
  simpa only [Function.comp_def,inv_inv] using
    (tendsto_eLpNorm_inv_dilation_sub_of_memLp f hf).comp hInv

end OAI.AnisotropicCalderon.DirichletFamily
