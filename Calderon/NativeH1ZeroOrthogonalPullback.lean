import Calderon.NativeH1OrthogonalPullback

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient Distributions
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def orthogonalTestFunctionPullback (e : R3 ≃ₗᵢ[ℝ] R3)
    (φ : 𝓓(ballOpens, ℝ)) : 𝓓(ballOpens, ℝ) where
  toFun := φ ∘ e
  contDiff' := φ.contDiff.comp e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph e.toHomeomorph
  tsupport_subset' := by
    intro x hx
    have hx' : e x ∈ (ballOpens : Set R3) :=
      φ.tsupport_subset (tsupport_comp_subset_preimage φ e.continuous hx)
    have hxpre : x ∈ e ⁻¹' (ballOpens : Set R3) := hx'
    rw [orthogonal_preimage_unitBall e] at hxpre
    exact hxpre

lemma nativeH1OrthogonalPullback_ofTestFunction (e : R3 ≃ₗᵢ[ℝ] R3)
    (φ : 𝓓(ballOpens, ℝ)) :
    nativeH1OrthogonalPullback e (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 φ) =
      TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 (orthogonalTestFunctionPullback e φ) := by
  change nativeH1OrthogonalPullback e (testFunctionSobolev φ) =
    testFunctionSobolev (orthogonalTestFunctionPullback e φ)
  rw [← smoothSobolev_testFunction, nativeH1OrthogonalPullback_smoothSobolev,
    ← smoothSobolev_testFunction]
  rfl

lemma nativeH1OrthogonalPullback_mem_zero (e : R3 ≃ₗᵢ[ℝ] R3) (u : BallH1)
    (hu : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) :
    nativeH1OrthogonalPullback e u ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  apply (TauCeti.w1p0Submodule_subset_of_isClosed
    ((TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).isClosed.preimage
      (nativeH1OrthogonalPullback e).continuous) ?_) hu
  intro φ
  change nativeH1OrthogonalPullback e (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 φ) ∈
    TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2
  rw [nativeH1OrthogonalPullback_ofTestFunction]
  exact TauCeti.W1p.ofTestFunctionₗ_mem_w1p0Submodule (orthogonalTestFunctionPullback e φ)

def nativeH1ZeroOrthogonalPullback (e : R3 ≃ₗᵢ[ℝ] R3) : BallH1Zero →ₗᵢ[ℝ] BallH1Zero where
  toLinearMap :=
    { toFun := fun u => ⟨nativeH1OrthogonalPullback e u.val,
        nativeH1OrthogonalPullback_mem_zero e u.val u.property⟩
      map_add' := fun u v => Subtype.ext ((nativeH1OrthogonalPullback e).map_add u.val v.val)
      map_smul' := fun c u => Subtype.ext ((nativeH1OrthogonalPullback e).map_smul c u.val) }
  norm_map' := fun u => (nativeH1OrthogonalPullback e).norm_map u.val

lemma nativeH1ZeroOrthogonalPullback_coe (e : R3 ≃ₗᵢ[ℝ] R3) (u : BallH1Zero) :
    (nativeH1ZeroOrthogonalPullback e u : BallH1) = nativeH1OrthogonalPullback e (u : BallH1) := rfl

lemma nativeH1ZeroOrthogonalPullback_symm_apply (e : R3 ≃ₗᵢ[ℝ] R3) (u : BallH1Zero) :
    nativeH1ZeroOrthogonalPullback e.symm (nativeH1ZeroOrthogonalPullback e u) = u :=
  Subtype.ext (nativeH1OrthogonalPullback_symm_apply e u.val)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonalTestFunctionPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullback_ofTestFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullback_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1ZeroOrthogonalPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1ZeroOrthogonalPullback_coe
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1ZeroOrthogonalPullback_symm_apply
