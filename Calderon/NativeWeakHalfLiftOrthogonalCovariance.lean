import Calderon.NativeCoefficientWeakHalfLift
import Calderon.NativeHarmonicFirstOrderOrthogonalPullback
import Calderon.NativeOrthogonalWeakSolution

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Fully expanded before source in EXPANSION-native-coefficient-weak-half-lift-rotation-v001.json.
Coefficients transform by actual matrix conjugation and vector pullback. -/

lemma memLp_nativeOrthogonalEnergyIntegrand_of_continuous
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) ((c ∘ e) x)) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
  memLp_nativeEnergyIntegrand_of_continuous
    (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e)
    (continuous_orthogonalPrincipalCoefficient e a ha)
    (e.symm.continuous.comp (hb.comp e.continuous)) (hc.comp e.continuous)

lemma nativeWeakHalfLift_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) ((c ∘ e) x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hi : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff).IsInvertible)
    (hirot : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
      (c := c ∘ e) hrot).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) :
    nativeH1OrthogonalPullback e (nativeWeakHalfLift a b c hcoeff hF f) =
      nativeWeakHalfLift (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b)
        (c ∘ e) hrot hF (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e f) := by
  let E : BallH1 := harmonicFirstOrderLiftCompletion hF
    (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e f)
  let U : BallH1 := nativeH1OrthogonalPullback e (nativeWeakHalfLift a b c hcoeff hF f)
  let V : BallH1 := nativeWeakHalfLift (orthogonalPrincipalCoefficient e a)
    (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF
      (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e f)
  have hEU : E-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    have hz := nativeH1OrthogonalPullback_affine_difference e
      (harmonicFirstOrderLiftCompletion hF f) (nativeWeakHalfLift a b c hcoeff hF f)
        (nativeWeakHalfLift_affine_difference a b c hcoeff hF f)
    rw [harmonicFirstOrderLiftCompletion_orthogonalPullback hF hO] at hz
    exact hz
  have hEV : E-V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    nativeWeakHalfLift_affine_difference (orthogonalPrincipalCoefficient e a)
      (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF
        (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e f)
  have hUV : U-V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    have he : U-V = (E-V)-(E-U) := by abel
    rw [he]
    exact (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).sub_mem hEV hEU
  apply eq_of_native_weak_solution_of_isInvertible
    (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e)
      hrot hirot U V hUV
  · intro v
    exact nativeH1OrthogonalPullback_weak_solution e a b c ha hb hc
      (nativeWeakHalfLift a b c hcoeff hF f)
      (nativeWeakHalfLift_weak_solution a b c hcoeff hF hi f) v
  · intro v
    exact nativeWeakHalfLift_weak_solution (orthogonalPrincipalCoefficient e a)
      (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF hirot
        (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e f) v

lemma nativeWeakHalfLift_orthogonal_covariance_of_continuous
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hi : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) (memLp_nativeEnergyIntegrand_of_continuous a b c ha hb hc)).IsInvertible)
    (hirot : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := orthogonalPrincipalCoefficient e a) (b := orthogonalDriftCoefficient e b)
      (c := c ∘ e) (memLp_nativeOrthogonalEnergyIntegrand_of_continuous e a b c ha hb hc)).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) :
    nativeH1OrthogonalPullback e
      (nativeWeakHalfLift a b c (memLp_nativeEnergyIntegrand_of_continuous a b c ha hb hc) hF f) =
    nativeWeakHalfLift (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b)
      (c ∘ e) (memLp_nativeOrthogonalEnergyIntegrand_of_continuous e a b c ha hb hc) hF
        (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e f) := by
  exact nativeWeakHalfLift_orthogonal_covariance e a b c ha hb hc
    (memLp_nativeEnergyIntegrand_of_continuous a b c ha hb hc)
    (memLp_nativeOrthogonalEnergyIntegrand_of_continuous e a b c ha hb hc)
    hF hO hi hirot f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_nativeOrthogonalEnergyIntegrand_of_continuous
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_orthogonal_covariance_of_continuous
