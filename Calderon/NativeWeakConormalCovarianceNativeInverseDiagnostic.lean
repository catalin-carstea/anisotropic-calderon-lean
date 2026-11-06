import Calderon.NativeWeakConormalOrthogonalCovariance

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeZeroCoefficientEnergyL nativeWeakConormalEndpoint
  sphereSobolevOrthogonalPullbackL

/-! Full upfront expansion: EXPANSION-v001.json. Convert the existing normalized
native inverse predicate through its checked iff before applying raw covariance. -/
lemma nativeWeakConormalEndpoint_orthogonal_covariance_of_nativeZero_isInvertible
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hrot : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e a x) (orthogonalDriftCoefficient e b x) ((c ∘ e) x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hi : (nativeZeroCoefficientEnergyL a b c hcoeff).IsInvertible)
    (f : SphereSobolev (1/2:ℝ)) :
    nativeWeakConormalEndpoint
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e) hrot hF
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e f) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
      (nativeWeakConormalEndpoint a b c hcoeff hF f) := by
  have hRaw := (nativeZeroCoefficientEnergyL_isInvertible_iff a b c hcoeff).mp hi
  have hCov := nativeWeakConormalEndpoint_orthogonal_covariance
  exact hCov e a b c ha hb hc hcoeff hrot hF hO hRaw f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakConormalEndpoint_orthogonal_covariance_of_nativeZero_isInvertible
