import Calderon.NativeHessianCoordinateBound

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.NativePolynomialH2Graph
open NativePolynomialBulkMoments NativeHarmonicBulkDerivativeMoments NativeHessianCoordinateBound
  SphereHarmonic DirichletFamily EnergyBridge MetricVolume

lemma lowerOrder_polynomialBallSobolev_two (p : MvPolynomial (Fin 3) ℝ) :
    TauCeti.Wkp.lowerOrder 1 (polynomialBallSobolev 2 p) =
      smoothSobolev (smoothPolynomialData p) := by
  rw [polynomialBallSobolev, lowerOrder_smoothBallSobolev]
  exact firstOrder_smoothBallSobolev 0 (smoothPolynomialData p)

lemma norm_sq_polynomialBallSobolev_two (p : MvPolynomial (Fin 3) ℝ) :
    ‖polynomialBallSobolev 2 p‖^2 =
      (∫ x in Metric.ball (0 : R3) 1, (p.eval (fun i => x i))^2) +
      (∫ x in Metric.ball (0 : R3) 1, ‖energyGradient (smoothPolynomialData p).1 x‖^2) +
      (∫ x in Metric.ball (0 : R3) 1,
        ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 1 x‖^2) := by
  rw [TauCeti.Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ 0,
    lowerOrder_polynomialBallSobolev_two]
  change ‖smoothSobolev (smoothPolynomialData p)‖^2 +
    ‖TauCeti.Wkp.iteratedGradient 1 (polynomialBallSobolev 2 p)‖^2 = _
  rw [norm_smoothSobolev_sq_eq_graph_integrals, ← Lp.integral_norm_sq_eq_norm_sq]
  congr 1
  apply integral_congr_ae
  filter_upwards [iteratedGradient_smoothBallSobolev_ae 1 (smoothPolynomialData p)] with x hx
  change ‖TauCeti.Wkp.iteratedGradient 1 (smoothBallSobolev 2 (smoothPolynomialData p)) x‖^2 = _
  rw [hx]

lemma norm_sq_polynomialBallSobolev_two_le (hF : SphereFischerInner) (m : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous (m+2)) :
    ‖polynomialBallSobolev 2 p‖^2 ≤
      sphereSurfaceMass * (1/(2*(m:ℝ)+7) + ((m:ℝ)+2) +
        ((m:ℝ)+2)*((m:ℝ)+1)*(2*(m:ℝ)+5)) * ‖polynomialSphereL2 p‖^2 := by
  have hp' : p ∈ harmonicHomogeneous ((m+1)+1) := by simpa [Nat.add_assoc] using hp
  have hLow := norm_smoothPolynomialSobolev_sq hF (m+1) p hp'
  have hHigh := integral_polynomial_iteratedGradient_square_le hF m p hp
  have hNative := TauCeti.Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ
    0 (polynomialBallSobolev 2 p)
  rw [lowerOrder_polynomialBallSobolev_two] at hNative
  change ‖polynomialBallSobolev 2 p‖^2 =
    ‖smoothSobolev (smoothPolynomialData p)‖^2 +
    ‖TauCeti.Wkp.iteratedGradient 1 (polynomialBallSobolev 2 p)‖^2 at hNative
  have hEq : ‖TauCeti.Wkp.iteratedGradient 1 (polynomialBallSobolev 2 p)‖^2 =
      ∫ x in Metric.ball (0 : R3) 1,
        ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 1 x‖^2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [iteratedGradient_smoothBallSobolev_ae 1 (smoothPolynomialData p)] with x hx
    change ‖TauCeti.Wkp.iteratedGradient 1 (smoothBallSobolev 2 (smoothPolynomialData p)) x‖^2 = _
    rw [hx]
  rw [hEq,hLow] at hNative
  push_cast at hNative
  calc
    ‖polynomialBallSobolev 2 p‖^2 =
        sphereSurfaceMass * (1/(2*((m:ℝ)+1)+5) + ((m:ℝ)+1+1)) *
          ‖polynomialSphereL2 p‖^2 +
        (∫ x in Metric.ball (0 : R3) 1,
          ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 1 x‖^2) := hNative
    _ ≤ sphereSurfaceMass * (1/(2*((m:ℝ)+1)+5) + ((m:ℝ)+1+1)) *
          ‖polynomialSphereL2 p‖^2 +
        sphereSurfaceMass * ((m:ℝ)+2)*((m:ℝ)+1)*(2*(m:ℝ)+5)*
          ‖polynomialSphereL2 p‖^2 := add_le_add (le_refl _) hHigh
    _ = _ := by ring

#print axioms lowerOrder_polynomialBallSobolev_two
#print axioms norm_sq_polynomialBallSobolev_two
#print axioms norm_sq_polynomialBallSobolev_two_le
end OAI.AnisotropicCalderon.NativePolynomialH2Graph
