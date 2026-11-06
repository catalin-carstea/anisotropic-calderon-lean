import Calderon.NativeCoordinateHarmonicDefect
import Calderon.NativeWeakMultiplicationDefectReduction

set_option autoImplicit false
noncomputable section
open MvPolynomial Set MeasureTheory
open scoped ENNReal ContDiff Gradient DirectSum
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHalfSmoothMultiplier

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (i : Fin 3) {M : ℝ} (hM : 0 ≤ M)
  (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothPolynomialData (X i)).1 x| ≤ M)
  (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothPolynomialData (X i)).1 x‖ ≤ M)

def nativeCoordinateHarmonicDefectL : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  (harmonicFirstOrderLiftCompletion hF).comp
    (nativeHalfSmoothMulL hF hO hD τ0 (smoothPolynomialData (X i)) hM hm hg) -
  (TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
    (p := 2) (smoothPolynomialData (X i)).1 (smoothPolynomialData (X i)).2 hM hm hg).comp
      (harmonicFirstOrderLiftCompletion hF)

lemma nativeCoordinateHarmonicDefectL_finite_mem_zero (a : HarmonicFiniteCoefficients) :
    nativeCoordinateHarmonicDefectL hF hO hD τ0 i hM hm hg (harmonicHalfBoundaryFiniteL a) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  rw [harmonicHalfBoundaryFiniteL_eq_sum,map_sum]
  apply (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).sum_mem
  intro k hk
  exact harmonicFirstOrderLift_coordinate_defect_single_mem_zero hF hO hD τ0 i hM hm hg k (a k)

lemma harmonicFirstOrderLift_coordinate_defect_mem_zero (f : SphereSobolev (1/2:ℝ)) :
    harmonicFirstOrderLiftCompletion hF
      (nativeHalfSmoothMulL hF hO hD τ0 (smoothPolynomialData (X i)) hM hm hg f) -
    TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (smoothPolynomialData (X i)).1 (smoothPolynomialData (X i)).2 hM hm hg
      (harmonicFirstOrderLiftCompletion hF f) ∈
    TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let D : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 := nativeCoordinateHarmonicDefectL hF hO hD τ0 i hM hm hg
  change D f ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2
  refine denseRange_harmonicHalfBoundaryFiniteL.induction_on f
    ((TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).isClosed.preimage D.continuous) ?_
  intro a
  exact nativeCoordinateHarmonicDefectL_finite_mem_zero hF hO hD τ0 i hM hm hg a

lemma nativeWeakHalfLift_coordinate_defect_mem_zero
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (f : SphereSobolev (1/2:ℝ)) :
    nativeWeakHalfLift a b c hcoeff hF
      (nativeHalfSmoothMulL hF hO hD τ0 (smoothPolynomialData (X i)) hM hm hg f) -
    TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (smoothPolynomialData (X i)).1 (smoothPolynomialData (X i)).2 hM hm hg
      (nativeWeakHalfLift a b c hcoeff hF f) ∈
    TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  exact (nativeWeakHalfLift_multiplication_defect_mem_zero_iff a b c hcoeff
    hF hO hD τ0 (smoothPolynomialData (X i)) hM hm hg f).mpr
      (harmonicFirstOrderLift_coordinate_defect_mem_zero hF hO hD τ0 i hM hm hg f)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoordinateHarmonicDefectL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoordinateHarmonicDefectL_finite_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.harmonicFirstOrderLift_coordinate_defect_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakHalfLift_coordinate_defect_mem_zero
