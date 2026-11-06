import Calderon.SingularProfileLpParameterCalculus
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.ConnectionError


theorem boundedContinuousMulLpL_add_profile
    (μ : Measure R3) (phi : R3 →ᵇ ℝ) (f g : Lp ℝ 2 μ) :
    boundedContinuousMulLpL μ (f+g) phi =
      boundedContinuousMulLpL μ f phi + boundedContinuousMulLpL μ g phi := by
  apply Lp.ext
  filter_upwards [boundedContinuousMulLpL_apply_ae μ (f+g) phi,
    boundedContinuousMulLpL_apply_ae μ f phi,
    boundedContinuousMulLpL_apply_ae μ g phi,
    Lp.coeFn_add f g,
    Lp.coeFn_add (boundedContinuousMulLpL μ f phi) (boundedContinuousMulLpL μ g phi)]
    with z hfg hf hg hadd hsum
  rw [hfg, hsum]
  change phi z * ((f+g) z) =
    (boundedContinuousMulLpL μ f phi) z + (boundedContinuousMulLpL μ g phi) z
  rw [hf, hg, hadd]
  simp only [Pi.add_apply]
  ring

theorem boundedContinuousMulLpL_smul_profile
    (μ : Measure R3) (phi : R3 →ᵇ ℝ) (c : ℝ) (f : Lp ℝ 2 μ) :
    boundedContinuousMulLpL μ (c • f) phi = c • boundedContinuousMulLpL μ f phi := by
  apply Lp.ext
  filter_upwards [boundedContinuousMulLpL_apply_ae μ (c • f) phi,
    boundedContinuousMulLpL_apply_ae μ f phi, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (boundedContinuousMulLpL μ f phi)] with z hcf hf hsmul hout
  rw [hcf, hout]
  change phi z * ((c • f) z) = c * (boundedContinuousMulLpL μ f phi) z
  rw [hf, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_boundedContinuousMulLpL_apply_le
    (μ : Measure R3) (phi : R3 →ᵇ ℝ) (f : Lp ℝ 2 μ) :
    ‖boundedContinuousMulLpL μ f phi‖ ≤ ‖phi‖ * ‖f‖ := by
  calc
    _ ≤ ‖boundedContinuousMulLpL μ f‖ * ‖phi‖ := (boundedContinuousMulLpL μ f).le_opNorm phi
    _ ≤ ‖f‖ * ‖phi‖ := mul_le_mul_of_nonneg_right
      (norm_boundedContinuousMulLpL_le μ f) (norm_nonneg phi)
    _ = ‖phi‖ * ‖f‖ := mul_comm _ _


def boundedContinuousMulLpLinear₂ (μ : Measure R3) :
    (R3 →ᵇ ℝ) →ₗ[ℝ] (Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ) :=
  { toFun := fun phi =>
      { toFun := fun f => boundedContinuousMulLpL μ f phi
        map_add' := boundedContinuousMulLpL_add_profile μ phi
        map_smul' := fun c f => by
          simpa only [RingHom.id_apply] using boundedContinuousMulLpL_smul_profile μ phi c f }
    map_add' := fun phi psi => by
      apply LinearMap.ext
      intro f
      change boundedContinuousMulLpL μ f (phi+psi) = _
      exact (boundedContinuousMulLpL μ f).map_add phi psi
    map_smul' := fun c phi => by
      apply LinearMap.ext
      intro f
      change boundedContinuousMulLpL μ f (c • phi) = _
      exact (boundedContinuousMulLpL μ f).map_smul c phi }

def boundedContinuousMulLpBilin (μ : Measure R3) :
    (R3 →ᵇ ℝ) →L[ℝ] (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :=
  (boundedContinuousMulLpLinear₂ μ).mkContinuous₂ 1 (fun phi f => by
    change ‖boundedContinuousMulLpL μ f phi‖ ≤ 1 * ‖phi‖ * ‖f‖
    simpa only [one_mul] using norm_boundedContinuousMulLpL_apply_le μ phi f)


theorem boundedContinuousMulLpBilin_apply
    (μ : Measure R3) (phi : R3 →ᵇ ℝ) (f : Lp ℝ 2 μ) :
    boundedContinuousMulLpBilin μ phi f = boundedContinuousMulLpL μ f phi := by rfl

theorem boundedContinuousMulLpBilin_apply_ae
    (μ : Measure R3) (phi : R3 →ᵇ ℝ) (f : Lp ℝ 2 μ) :
    boundedContinuousMulLpBilin μ phi f =ᵐ[μ] (fun z => phi z * f z) := by
  exact boundedContinuousMulLpL_apply_ae μ f phi

theorem norm_boundedContinuousMulLpBilin_le (μ : Measure R3) :
    ‖boundedContinuousMulLpBilin μ‖ ≤ 1 := by
  exact LinearMap.mkContinuous₂_norm_le _ (by norm_num) _

theorem contDiff_boundedContinuousMulLpBilin_comp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μ : Measure R3) (A : P → (R3 →ᵇ ℝ)) (F : P → Lp ℝ 2 μ)
    (hA : ContDiff ℝ ∞ A) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p => boundedContinuousMulLpBilin μ (A p) (F p)) := by
  exact ((boundedContinuousMulLpBilin μ).contDiff.comp hA).clm_apply hF

end OAI.AnisotropicCalderon.ConnectionError
