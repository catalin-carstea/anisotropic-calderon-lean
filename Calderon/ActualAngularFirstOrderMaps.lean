import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.ActualAngularCoordinateJets

set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft

/-! ## Actual setting -/

open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)

attribute [local instance] angularHighHalfCompleteSpace angularHighNegativeCompleteSpace

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
  (EuclideanSpace.single j (1 : ℝ))

/-- Low lowering operator `a_i^l = Σ_j Mn_j Rl_{ji} + Mn_i Bl`. -/
def loweringLow (i : Fin 3) : Half →L[ℝ] NegH :=
  (∑ j : Fin 3, (Mn j).comp (sphereSobolevRotationL (1/2 : ℝ) j i)) +
    (Mn i).comp (sphereSobolevShiftedDegreeL (1/2 : ℝ))

/-- High lowering operator `a_i^h = Σ_j Ml_j Rh_{ji} + Ml_i Bh`. -/
def loweringHigh (i : Fin 3) : Hi →L[ℝ] Half :=
  (∑ j : Fin 3, (Ml j).comp (sphereSobolevRotationL (3/2 : ℝ) j i)) +
    (Ml i).comp (sphereSobolevShiftedDegreeL (3/2 : ℝ))

/-- High raising operator `A_i^h = -Σ_j Rh_{ji} Mh_j + Bh Mh_i` (parent reduction, right side). -/
def raisingHigh (i : Fin 3) : Hi →L[ℝ] Half :=
  (-∑ j : Fin 3, (sphereSobolevRotationL (3/2 : ℝ) j i).comp (Mh j)) +
    (sphereSobolevShiftedDegreeL (3/2 : ℝ)).comp (Mh i)

/-- Low raising operator `A_i^l = -Σ_j Rl_{ji} Ml_j + Bl Ml_i`. -/
def raisingLow (i : Fin 3) : Half →L[ℝ] NegH :=
  (-∑ j : Fin 3, (sphereSobolevRotationL (1/2 : ℝ) j i).comp (Ml j)) +
    (sphereSobolevShiftedDegreeL (1/2 : ℝ)).comp (Ml i)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft
