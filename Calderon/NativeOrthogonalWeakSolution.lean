import Calderon.NativeContinuousCoefficientOrthogonalEnergy
import Calderon.NativeH1ZeroOrthogonalPullback

/-! Upfront argument: EXPANSION-native-H1-orthogonal-energy-covariance-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma nativeH1OrthogonalPullback_weak_solution
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (u : BallH1)
    (hu : ∀ v : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u (v : BallH1) = 0)
    (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e)
      (nativeH1OrthogonalPullback e u) (v : BallH1) = 0 := by
  have hback : nativeH1OrthogonalPullback e
      (nativeH1OrthogonalPullback e.symm (v : BallH1)) = (v : BallH1) := by
    simpa only [LinearIsometryEquiv.symm_symm] using
      nativeH1OrthogonalPullback_symm_apply e.symm (v : BallH1)
  have he := energyFormH1_orthogonal_covariance e a b c ha hb hc u
    (nativeH1OrthogonalPullback e.symm (v : BallH1))
  rw [hback] at he
  exact he.trans (hu (nativeH1ZeroOrthogonalPullback e.symm v))

lemma nativeH1OrthogonalPullback_affine_difference
    (e : R3 ≃ₗᵢ[ℝ] R3) (E u : BallH1)
    (hz : E-u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) :
    nativeH1OrthogonalPullback e E-nativeH1OrthogonalPullback e u ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  rw [← map_sub]
  exact nativeH1OrthogonalPullback_mem_zero e (E-u) hz

lemma nativeEnergyForm_sub_left
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v w : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a b c (u-v) w =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u w -
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c v w := by
  have h := TauCeti.PDE.energyFormH1_add_left (a := a) (b := b) (c := c)
    hcoeff (u-v) w v
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

lemma nativeEnergyFormH1L0_difference_eq_zero
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (u v : BallH1)
    (hz : u-v ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hu : ∀ w : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u (w : BallH1) = 0)
    (hv : ∀ w : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) a b c v (w : BallH1) = 0) :
    TauCeti.PDE.energyFormH1L0 (a := a) (b := b) (c := c) hcoeff ⟨u-v,hz⟩ = 0 := by
  apply ContinuousLinearMap.ext
  intro w
  have hA := TauCeti.PDE.energyFormH1L0_apply (a := a) (b := b) (c := c)
    hcoeff ⟨u-v,hz⟩ w
  have hsub := nativeEnergyForm_sub_left a b c hcoeff u v (w : BallH1)
  have hzero : TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) a b c (u-v) (w : BallH1) = 0 := by
    exact hsub.trans ((congrArg₂ (fun x y : ℝ => x-y) (hu w) (hv w)).trans (sub_self 0))
  exact hA.trans hzero

lemma eq_of_native_weak_solution_of_isInvertible
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hi : (TauCeti.PDE.energyFormH1L0 hcoeff).IsInvertible)
    (u v : BallH1)
    (hz : u-v ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hu : ∀ w : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u (w : BallH1) = 0)
    (hv : ∀ w : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) a b c v (w : BallH1) = 0) :
    u = v := by
  let z : BallH1Zero := ⟨u-v,hz⟩
  have hAz := nativeEnergyFormH1L0_difference_eq_zero a b c hcoeff u v hz hu hv
  have hA0 := map_zero (TauCeti.PDE.energyFormH1L0 (a := a) (b := b) (c := c) hcoeff)
  have hz0 : z = 0 := hi.injective (hAz.trans hA0.symm)
  have hzval := congrArg (fun t : BallH1Zero => t.val) hz0
  exact sub_eq_zero.mp hzval

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullback_weak_solution
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullback_affine_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eq_of_native_weak_solution_of_isInvertible

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeEnergyForm_sub_left

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeEnergyFormH1L0_difference_eq_zero
