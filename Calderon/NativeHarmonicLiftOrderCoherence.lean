import Calderon.NativeHarmonicH1LiftCompletion
import Calderon.NativeHarmonicLiftExtension
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence
open NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion SphereHarmonic
  DirichletFamily EnergyBridge

lemma sphereSobolevInclusionL_harmonicBoundaryFiniteL (a : HarmonicFiniteCoefficients) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (harmonicBoundaryFiniteL a) =
      harmonicHalfBoundaryFiniteL a := by
  rw [harmonicBoundaryFiniteL_eq_sum,harmonicHalfBoundaryFiniteL_eq_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact sphereSobolevInclusionL_single (3/2:ℝ) (1/2:ℝ) (by norm_num) k (a k)

lemma firstOrder_harmonicNativeFiniteL (hF : SphereFischerInner) (a : HarmonicFiniteCoefficients) :
    TauCeti.Wkp.firstOrderL 1 (harmonicNativeFiniteL hF a) = harmonicFirstOrderFiniteL hF a := by
  rw [harmonicNativeFiniteL_eq_polynomial,harmonicFirstOrderFiniteL_eq_polynomial]
  exact firstOrder_smoothBallSobolev 1 _

lemma firstOrder_harmonicLiftCompletion (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (u : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrderL 1 (harmonicLiftCompletion hF u) =
      harmonicFirstOrderLiftCompletion hF
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) := by
  have hfirst (k : ℕ) : Continuous
      (fun v : BallSobolev (k+1) => TauCeti.Wkp.firstOrder
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := (2:ℝ≥0∞)) k v) :=
    (TauCeti.Wkp.firstOrderL (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
      (Omega := ballOpens) (p := (2:ℝ≥0∞)) k).continuous
  let A : SphereSobolev (3/2:ℝ) → BallH1 := fun v =>
    TauCeti.Wkp.firstOrder 1 (harmonicLiftCompletion hF v)
  let B : SphereSobolev (3/2:ℝ) → BallH1 := fun v =>
    harmonicFirstOrderLiftCompletion hF
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
  have hA : Continuous A := (hfirst 1).comp (harmonicLiftCompletion hF).continuous
  have hB : Continuous B := (harmonicFirstOrderLiftCompletion hF).continuous.comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).continuous
  have he : A = B := by
    apply denseRange_harmonicBoundaryFiniteL.equalizer hA hB
    funext a
    change TauCeti.Wkp.firstOrderL 1 (harmonicLiftCompletion hF (harmonicBoundaryFiniteL a)) =
      harmonicFirstOrderLiftCompletion hF
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (harmonicBoundaryFiniteL a))
    rw [sphereSobolevInclusionL_harmonicBoundaryFiniteL,
      harmonicLiftCompletion_finite hF hO,harmonicFirstOrderLiftCompletion_finite hF hO,
      firstOrder_harmonicNativeFiniteL]
  exact congr_fun he u

end OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence
