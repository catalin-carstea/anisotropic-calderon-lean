import Calderon.RadiusTwoNativeSourceFoundation
import TauCeti.Analysis.Sobolev.W1p.Multiplication

/-! EXPANSION.json precedes actual L2 cutoff multiplication/value identification. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem memLp_radiusTwo_smoothValue_mul (χ : SmoothData) {M : ℝ}
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ.1 x| ≤ M) (f : RadiusTwoL2) :
    MemLp (fun x : R3 => χ.1 x * f x) 2 ((volume : Measure R3).restrict radiusTwoOpens) := by
  apply (Lp.memLp f).of_le_mul (c := M)
    (χ.2.continuous.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem radiusTwoOpens.isOpen.measurableSet] with x hx
  simp only [Pi.mul_apply]
  rw [norm_mul,Real.norm_eq_abs (χ.1 x)]
  exact mul_le_mul_of_nonneg_right (hAbs x hx) (norm_nonneg _)

theorem norm_radiusTwo_smoothValue_mul_toLp_le (χ : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ.1 x| ≤ M) (f : RadiusTwoL2) :
    ‖(memLp_radiusTwo_smoothValue_mul χ hAbs f).toLp (fun x : R3 => χ.1 x * f x)‖ ≤ M * ‖f‖ := by
  calc
    _ ≤ ‖M • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [MemLp.coeFn_toLp (memLp_radiusTwo_smoothValue_mul χ hAbs f),
        Lp.coeFn_smul M f,ae_restrict_mem radiusTwoOpens.isOpen.measurableSet] with x hL hR hx
      change (M • f) x = M • f x at hR
      rw [hL,hR,norm_mul,norm_smul,Real.norm_eq_abs (χ.1 x),Real.norm_eq_abs M,abs_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right (hAbs x hx) (norm_nonneg _)
    _ = _ := by rw [norm_smul,Real.norm_eq_abs M,abs_of_nonneg hM]

def radiusTwoSmoothValueMultiplierL (χ : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ.1 x| ≤ M) : RadiusTwoL2 →L[ℝ] RadiusTwoL2 := by
  let L : RadiusTwoL2 →ₗ[ℝ] RadiusTwoL2 :=
    { toFun := fun f => (memLp_radiusTwo_smoothValue_mul χ hAbs f).toLp (fun x : R3 => χ.1 x * f x)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_radiusTwo_smoothValue_mul χ hAbs (f+g)),
          MemLp.coeFn_toLp (memLp_radiusTwo_smoothValue_mul χ hAbs f),
          MemLp.coeFn_toLp (memLp_radiusTwo_smoothValue_mul χ hAbs g),
          Lp.coeFn_add
            ((memLp_radiusTwo_smoothValue_mul χ hAbs f).toLp (fun x : R3 => χ.1 x*f x))
            ((memLp_radiusTwo_smoothValue_mul χ hAbs g).toLp (fun x : R3 => χ.1 x*g x)),
          Lp.coeFn_add f g] with x hFG hF hG hAdd hOld
        change (f+g) x = f x + g x at hOld
        simp only [Pi.add_apply] at hAdd
        rw [hFG,hAdd,hF,hG,hOld,mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_radiusTwo_smoothValue_mul χ hAbs (c • f)),
          MemLp.coeFn_toLp (memLp_radiusTwo_smoothValue_mul χ hAbs f),
          Lp.coeFn_smul c ((memLp_radiusTwo_smoothValue_mul χ hAbs f).toLp (fun x : R3 => χ.1 x*f x)),
          Lp.coeFn_smul c f] with x hCF hF hSmul hOld
        change (c • f) x = c • f x at hOld
        simp only [Pi.smul_apply] at hSmul
        have hResult :
            ((memLp_radiusTwo_smoothValue_mul χ hAbs (c • f)).toLp
              (fun x : R3 => χ.1 x * (c • f) x)) x =
            (c • ((memLp_radiusTwo_smoothValue_mul χ hAbs f).toLp
              (fun x : R3 => χ.1 x * f x))) x := by
          rw [hCF,hSmul,hF,hOld]
          simp only [smul_eq_mul]
          ring
        simpa only [RingHom.id_apply] using hResult }
  exact L.mkContinuous M (fun f => by
    change ‖(memLp_radiusTwo_smoothValue_mul χ hAbs f).toLp (fun x : R3 => χ.1 x*f x)‖ ≤ M * ‖f‖
    exact norm_radiusTwo_smoothValue_mul_toLp_le χ hM hAbs f)

theorem radiusTwoSmoothValueMultiplierL_apply_ae (χ : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ.1 x| ≤ M) (f : RadiusTwoL2) :
    (radiusTwoSmoothValueMultiplierL χ hM hAbs f : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
      (fun x : R3 => χ.1 x * f x) := MemLp.coeFn_toLp (memLp_radiusTwo_smoothValue_mul χ hAbs f)

theorem value_contDiffSMulL_eq_radiusTwoSmoothValueMultiplier (χ : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ.1 x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient χ.1 x‖ ≤ M) (u : RadiusTwoH1) :
    TauCeti.W1p.value (TauCeti.W1p.contDiffSMulL χ.1 χ.2 hM hAbs hGrad u) =
      radiusTwoSmoothValueMultiplierL χ hM hAbs (TauCeti.W1p.value u) := by
  rw [TauCeti.W1p.contDiffSMulL_apply]
  apply Lp.ext
  filter_upwards [TauCeti.W1p.value_contDiffSMul_ae χ.2 hM hAbs hGrad u,
    radiusTwoSmoothValueMultiplierL_apply_ae χ hM hAbs (TauCeti.W1p.value u)] with x hL hR
  simpa only [smul_eq_mul] using hL.trans hR.symm

end OAI.AnisotropicCalderon.ExteriorSource
