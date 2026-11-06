import Calderon.NativeCoefficientWeakConormalEndpoint
import Calderon.NativeWeakHalfLiftOrthogonalCovariance
import Calderon.NativeOrthogonalZeroEnergyInvertibility
import Calderon.SphereSobolevDualOrthogonalPullback

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
  (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
    ((volume : Measure R3).restrict ballOpens))
  (hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
    (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) ((c ∘ e) x)) ⊤
    ((volume : Measure R3).restrict ballOpens))
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hi : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := a) (b := b) (c := c) hcoeff).IsInvertible)

include ha hb hc hO hi

lemma nativeWeakConormalEndpointFunctional_orthogonal_covariance
    (f z : SphereSobolev (1/2:ℝ)) :
    nativeWeakConormalEndpointFunctional
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e f)
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e z) =
    nativeWeakConormalEndpointFunctional a b c hcoeff hF f z := by
  have hirot := energyFormH1L0_orthogonal_isInvertible e a b c hcoeff hrot hi
  have hW := nativeWeakHalfLift_orthogonal_covariance
    e a b c ha hb hc hcoeff hrot hF hO hi hirot f
  have hP := harmonicFirstOrderLiftCompletion_orthogonalPullback hF hO e z
  have hE := energyFormH1_orthogonal_covariance_of_memLp e a b c hcoeff hrot
    (nativeWeakHalfLift a b c hcoeff hF f) (harmonicFirstOrderLiftCompletion hF z)
  have hargs := congrArg₂ (fun U V : BallH1 => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) U V) hW hP
  have henergy := hargs.symm.trans hE
  have hleft := nativeWeakConormalEndpointFunctional_apply
    (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF
    (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e f)
    (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e z)
  have hright := nativeWeakConormalEndpointFunctional_apply a b c hcoeff hF f z
  exact hleft.trans ((congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) henergy).trans hright.symm)

lemma nativeWeakConormalEndpointFunctional_orthogonal_transfer
    (f : SphereSobolev (1/2:ℝ)) :
    nativeWeakConormalEndpointFunctional
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e f) =
    (nativeWeakConormalEndpointFunctional a b c hcoeff hF f).comp
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e.symm) := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e.symm z) = z := by
    simpa only [LinearIsometryEquiv.symm_symm] using
      sphereSobolevOrthogonalPullbackL_symm_apply (1/2:ℝ) e.symm z
  have h := nativeWeakConormalEndpointFunctional_orthogonal_covariance
    e a b c ha hb hc hcoeff hrot hF hO hi f
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e.symm z)
  exact (congrArg (nativeWeakConormalEndpointFunctional
    (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF
    (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e f)) hz).symm.trans h

lemma nativeWeakConormalEndpoint_orthogonal_covariance
    (f : SphereSobolev (1/2:ℝ)) :
    nativeWeakConormalEndpoint
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e f) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
      (nativeWeakConormalEndpoint a b c hcoeff hF f) := by
  have h := nativeWeakConormalEndpointFunctional_orthogonal_transfer
    e a b c ha hb hc hcoeff hrot hF hO hi f
  exact (congrArg (sphereSobolevDualRieszL (1/2:ℝ)) h).trans
    (sphereSobolevDualRieszL_orthogonalPullback (1/2:ℝ) e
      (nativeWeakConormalEndpointFunctional a b c hcoeff hF f))

lemma nativeWeakConormalEndpoint_comp_orthogonalPullback :
    (nativeWeakConormalEndpoint
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF).comp
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e) =
    (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e).comp
      (nativeWeakConormalEndpoint a b c hcoeff hF) := by
  apply ContinuousLinearMap.ext
  intro f
  exact nativeWeakConormalEndpoint_orthogonal_covariance
    e a b c ha hb hc hcoeff hrot hF hO hi f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakConormalEndpointFunctional_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakConormalEndpointFunctional_orthogonal_transfer
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakConormalEndpoint_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakConormalEndpoint_comp_orthogonalPullback
