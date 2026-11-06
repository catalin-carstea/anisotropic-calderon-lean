import Calderon.NativeCoefficientWeakHalfLift
import Calderon.SphereSobolevDualRiesz
import Calderon.NativePolynomialBulkMoments

/-! Expanded before source in EXPANSION-native-weak-conormal-orthogonal-covariance-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
    ((volume : Measure R3).restrict ballOpens))
  (hF : SphereFischerInner)

def nativeWeakConormalEndpointFunctional :
    SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
  sphereSurfaceMass⁻¹ •
    (TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff).bilinearComp
        (nativeWeakHalfLift a b c hcoeff hF) (harmonicFirstOrderLiftCompletion hF)

lemma nativeWeakConormalEndpointFunctional_apply (f z : SphereSobolev (1/2:ℝ)) :
    nativeWeakConormalEndpointFunctional a b c hcoeff hF f z =
      sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
        (mu := (volume : Measure R3)) (Omega := ballOpens) a b c
        (nativeWeakHalfLift a b c hcoeff hF f) (harmonicFirstOrderLiftCompletion hF z) := by
  change sphereSurfaceMass⁻¹ *
    TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff
      (nativeWeakHalfLift a b c hcoeff hF f) (harmonicFirstOrderLiftCompletion hF z) = _
  exact congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t)
    (TauCeti.PDE.energyFormH1L_apply (a := a) (b := b) (c := c) hcoeff
      (nativeWeakHalfLift a b c hcoeff hF f) (harmonicFirstOrderLiftCompletion hF z))

def nativeWeakConormalEndpoint :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevDualRieszL (1/2:ℝ)).comp
    (nativeWeakConormalEndpointFunctional a b c hcoeff hF)

lemma sphereSobolevDualPairing_nativeWeakConormalEndpoint
    (f z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z (nativeWeakConormalEndpoint a b c hcoeff hF f) =
      sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
        (mu := (volume : Measure R3)) (Omega := ballOpens) a b c
        (nativeWeakHalfLift a b c hcoeff hF f) (harmonicFirstOrderLiftCompletion hF z) :=
  (sphereSobolevDualPairing_dualRiesz (1/2:ℝ)
    (nativeWeakConormalEndpointFunctional a b c hcoeff hF f) z).trans
      (nativeWeakConormalEndpointFunctional_apply a b c hcoeff hF f z)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakConormalEndpointFunctional
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakConormalEndpointFunctional_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakConormalEndpoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_nativeWeakConormalEndpoint
