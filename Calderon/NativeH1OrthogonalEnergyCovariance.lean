import Calderon.NativeH1OrthogonalPullback
import Calderon.NativeOrthogonalCoefficientEnergyCovariance

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma nativeBilinearForm_eq_of_smooth
    (F G : BallH1 →L[ℝ] BallH1 →L[ℝ] ℝ)
    (h : ∀ f g : SmoothData, F (smoothSobolev f) (smoothSobolev g) =
      G (smoothSobolev f) (smoothSobolev g)) (u v : BallH1) : F u v = G u v := by
  exact denseRange_smoothSobolev.induction_on₂
    (isClosed_eq ((F.continuous.comp continuous_fst).clm_apply continuous_snd)
      ((G.continuous.comp continuous_fst).clm_apply continuous_snd)) h u v

lemma nativeBilinearComp_orthogonal_smooth_apply
    (F : BallH1 →L[ℝ] BallH1 →L[ℝ] ℝ) (e : R3 ≃ₗᵢ[ℝ] R3)
    (f g : SmoothData) :
    (F.bilinearComp (nativeH1OrthogonalPullback e).toContinuousLinearMap
      (nativeH1OrthogonalPullback e).toContinuousLinearMap)
      (smoothSobolev f) (smoothSobolev g) =
    F (smoothSobolev (orthogonalSmoothPullback e f))
      (smoothSobolev (orthogonalSmoothPullback e g)) := by
  change F (nativeH1OrthogonalPullback e (smoothSobolev f))
    (nativeH1OrthogonalPullback e (smoothSobolev g)) = _
  exact congrArg₂ (fun u v : BallH1 => F u v)
    (nativeH1OrthogonalPullback_smoothSobolev e f)
    (nativeH1OrthogonalPullback_smoothSobolev e g)

lemma energyFormH1L_orthogonal_bilinearComp_apply
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) (c (e x))) ⊤
        ((volume : Measure R3).restrict ballOpens)) (u v : BallH1) :
    ((TauCeti.PDE.energyFormH1L
      (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
      (c := c ∘ e) hrot).bilinearComp
      (nativeH1OrthogonalPullback e).toContinuousLinearMap
      (nativeH1OrthogonalPullback e).toContinuousLinearMap) u v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e)
      (nativeH1OrthogonalPullback e u) (nativeH1OrthogonalPullback e v) := by
  exact TauCeti.PDE.energyFormH1L_apply
    (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
    (c := c ∘ e) hrot (nativeH1OrthogonalPullback e u) (nativeH1OrthogonalPullback e v)

lemma energyFormH1L_orthogonal_smooth_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) (c (e x))) ⊤
        ((volume : Measure R3).restrict ballOpens)) (f g : SmoothData) :
    ((TauCeti.PDE.energyFormH1L
      (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
      (c := c ∘ e) hrot).bilinearComp
      (nativeH1OrthogonalPullback e).toContinuousLinearMap
      (nativeH1OrthogonalPullback e).toContinuousLinearMap)
      (smoothSobolev f) (smoothSobolev g) =
    TauCeti.PDE.energyFormH1L (a := a) (b := b) (c := c) hcoeff
      (smoothSobolev f) (smoothSobolev g) := by
  let A : BallH1 →L[ℝ] BallH1 →L[ℝ] ℝ := TauCeti.PDE.energyFormH1L
    (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
    (c := c ∘ e) hrot
  have h₁ := nativeBilinearComp_orthogonal_smooth_apply A e f g
  have h₂ := TauCeti.PDE.energyFormH1L_apply
    (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
    (c := c ∘ e) hrot (smoothSobolev (orthogonalSmoothPullback e f))
      (smoothSobolev (orthogonalSmoothPullback e g))
  have h₃ := energyFormH1_smooth_orthogonal_covariance e a b c f g
  have h₄ := TauCeti.PDE.energyFormH1L_apply (a := a) (b := b) (c := c)
    hcoeff (smoothSobolev f) (smoothSobolev g)
  exact h₁.trans (h₂.trans (h₃.trans h₄.symm))

lemma energyFormH1_orthogonal_covariance_of_memLp
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) (c (e x))) ⊤
        ((volume : Measure R3).restrict ballOpens)) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e)
      (nativeH1OrthogonalPullback e u) (nativeH1OrthogonalPullback e v) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u v := by
  let F : BallH1 →L[ℝ] BallH1 →L[ℝ] ℝ :=
    TauCeti.PDE.energyFormH1L (a := a) (b := b) (c := c) hcoeff
  let G : BallH1 →L[ℝ] BallH1 →L[ℝ] ℝ :=
    (TauCeti.PDE.energyFormH1L
      (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
      (c := c ∘ e) hrot).bilinearComp
      (nativeH1OrthogonalPullback e).toContinuousLinearMap
      (nativeH1OrthogonalPullback e).toContinuousLinearMap
  have hs (f g : SmoothData) : G (smoothSobolev f) (smoothSobolev g) =
      F (smoothSobolev f) (smoothSobolev g) :=
    energyFormH1L_orthogonal_smooth_covariance e a b c hcoeff hrot f g
  have hG := energyFormH1L_orthogonal_bilinearComp_apply e a b c hrot u v
  have hF := TauCeti.PDE.energyFormH1L_apply (a := a) (b := b) (c := c) hcoeff u v
  exact hG.symm.trans ((nativeBilinearForm_eq_of_smooth G F hs u v).trans hF)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeBilinearForm_eq_of_smooth
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_orthogonal_covariance_of_memLp

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeBilinearComp_orthogonal_smooth_apply

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1L_orthogonal_bilinearComp_apply

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1L_orthogonal_smooth_covariance
