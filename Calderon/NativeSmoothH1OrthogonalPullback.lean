import Calderon.NativeGlobalSmoothH1Density
import Calderon.NativeOrthogonalSmoothPullback
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def nativeSmoothFunctionSpace : Submodule ℝ (R3 → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : R3 => (0 : ℝ))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ f at hf
    exact contDiff_const.smul hf

lemma smoothSobolev_const_smul (c : ℝ) (f : SmoothData) :
    smoothSobolev ⟨c • f.1,contDiff_const.smul f.2⟩ = c • smoothSobolev f := by
  apply TauCeti.W1p.ext_value
  simp only [← TauCeti.W1p.valueL_apply, map_smul]
  simp only [TauCeti.W1p.valueL_apply,value_smoothSobolev]
  exact MemLp.toLp_const_smul c (memLp_smooth_value f)

def nativeSmoothSobolevLinear : nativeSmoothFunctionSpace →ₗ[ℝ] BallH1 where
  toFun f := smoothSobolev ⟨f.1,f.2⟩
  map_add' f g := smoothSobolev_add ⟨f.1,f.2⟩ ⟨g.1,g.2⟩
  map_smul' c f := smoothSobolev_const_smul c ⟨f.1,f.2⟩

lemma denseRange_nativeSmoothSobolevLinear : DenseRange nativeSmoothSobolevLinear := by
  change DenseRange smoothSobolev
  exact denseRange_smoothSobolev

def nativeSmoothOrthogonalPullbackLinear (e : R3 ≃ₗᵢ[ℝ] R3) :
    nativeSmoothFunctionSpace →ₗ[ℝ] nativeSmoothFunctionSpace where
  toFun f := ⟨f.1 ∘ e,(show ContDiff ℝ ∞ f.1 from f.2).comp e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff⟩
  map_add' f g := rfl
  map_smul' c f := rfl

lemma norm_smoothSobolev_orthogonalSmoothPullback (e : R3 ≃ₗᵢ[ℝ] R3) (f : SmoothData) :
    ‖smoothSobolev (orthogonalSmoothPullback e f)‖ = ‖smoothSobolev f‖ := by
  have hsq : ‖smoothSobolev (orthogonalSmoothPullback e f)‖^2 = ‖smoothSobolev f‖^2 := by
    rw [norm_smoothSobolev_sq_eq_graph_integrals,norm_smoothSobolev_sq_eq_graph_integrals]
    have hv := integral_comp_orthogonal_unitBall e (fun x => (f.1 x)^2)
    have hg := integral_comp_orthogonal_unitBall e (fun x => ‖gradient f.1 x‖^2)
    change (∫ x in B, (f.1 (e x))^2) +
      (∫ x in B, ‖energyGradient (f.1 ∘ e) x‖^2) = _
    simp only [energyGradient_eq_gradient,gradient_comp_orthogonal e f.1 f.2,e.symm.norm_map]
    exact congrArg₂ (fun a b : ℝ => a+b) hv hg
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma norm_nativeSmoothOrthogonalPullbackLinear (e : R3 ≃ₗᵢ[ℝ] R3)
    (f : nativeSmoothFunctionSpace) :
    ‖nativeSmoothSobolevLinear (nativeSmoothOrthogonalPullbackLinear e f)‖ =
      ‖nativeSmoothSobolevLinear f‖ :=
  norm_smoothSobolev_orthogonalSmoothPullback e ⟨f.1,f.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothFunctionSpace
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothSobolev_const_smul
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothSobolevLinear
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.denseRange_nativeSmoothSobolevLinear
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothOrthogonalPullbackLinear
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_smoothSobolev_orthogonalSmoothPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_nativeSmoothOrthogonalPullbackLinear
