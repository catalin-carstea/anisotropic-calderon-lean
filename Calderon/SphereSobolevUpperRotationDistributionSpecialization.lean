import Calderon.SphereSobolevLocalRotationDistributionDerivative
import Calderon.ActualUpperRotationInputOrderDiagnostic

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation SmoothSphereRotationProjection DirichletFamily.DriftBootstrap
  SpectralWeightedGraph
/-! Full upfront expansion: EXPANSION-v005.json. This only specializes the checked
abstract derivative identity to exact upper orders before actual family arguments. -/

lemma sphereSobolevInclusionL_upper_fixed_input_order :
    sphereSobolevInclusionL ((3/2:ℝ)+1) (3/2:ℝ) (by norm_num) =
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  change besselWeight ((3/2:ℝ)-((3/2:ℝ)+1)) k • u k =
    besselWeight ((3/2:ℝ)-(5/2:ℝ)) k • u k
  rw [show (3/2:ℝ)-((3/2:ℝ)+1) = (3/2:ℝ)-(5/2:ℝ) from by norm_num]

lemma sphereSobolevInclusionL_upper_fixed_output_order :
    sphereSobolevInclusionL (1/2:ℝ) ((1/2:ℝ)-1) (by norm_num) =
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  change besselWeight (((1/2:ℝ)-1)-(1/2:ℝ)) k • u k =
    besselWeight ((-(1/2:ℝ))-(1/2:ℝ)) k • u k
  rw [show ((1/2:ℝ)-1)-(1/2:ℝ) = (-(1/2:ℝ))-(1/2:ℝ) from by norm_num]



#eval (show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "UPPER_DIST BEFORE_DECL"
  out.flush)

lemma sphereSobolev_upper_rotation_derivative_distribution
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i j : Fin 3)
    (Q : ℝ → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (A D : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hQ : HasDerivAt Q D 0)
    (hcov : ∀ᶠ θ in 𝓝 (0:ℝ), ∀ u : SphereSobolev (3/2:ℝ),
      Q θ (sphereSobolevOrthogonalPullbackL (3/2:ℝ) (coordinateRotationIsometry i j θ) u) =
      sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ) (A u))
    (f : SphereSobolev (5/2:ℝ)) :
    sphereSobolevRotationL (1/2:ℝ) i j
      (A (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f)) =
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (D (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f) +
        A (sphereSobolevRotationL (5/2:ℝ) i j f)) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UPPER_DIST_COMPONENT PROOF_ENTER"
    out.flush
  have h := sphereSobolev_local_rotation_derivative_distribution
    hO hD (3/2:ℝ) (1/2:ℝ) i j Q A D hQ hcov f
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UPPER_DIST_COMPONENT GENERIC_APPLIED"
    out.flush
  have hInput :
      sphereSobolevInclusionL ((3/2:ℝ)+1) (3/2:ℝ) (by norm_num) f =
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f := by
    apply lp.ext
    funext k
    change besselWeight ((3/2:ℝ)-((3/2:ℝ)+1)) k • f k =
      besselWeight ((3/2:ℝ)-(5/2:ℝ)) k • f k
    rw [show (3/2:ℝ)-((3/2:ℝ)+1) = (3/2:ℝ)-(5/2:ℝ) from by norm_num]
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UPPER_DIST_COMPONENT INPUT_VALUE"
    out.flush
  have hRotation : sphereSobolevRotationL ((3/2:ℝ)+1) i j f =
      sphereSobolevRotationL (5/2:ℝ) i j f := by
    apply lp.ext
    funext k
    change (1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j (f k) =
      (1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j (f k)
    rfl
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UPPER_DIST_COMPONENT ROTATION_VALUE"
    out.flush
  have hSum :
      D (sphereSobolevInclusionL ((3/2:ℝ)+1) (3/2:ℝ) (by norm_num) f) +
        A (sphereSobolevRotationL ((3/2:ℝ)+1) i j f) =
      D (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f) +
        A (sphereSobolevRotationL (5/2:ℝ) i j f) :=
    congrArg₂ (fun u v : SphereSobolev (1/2:ℝ) => u+v)
      (congrArg (fun v : SphereSobolev (3/2:ℝ) => D v) hInput)
      (congrArg (fun v : SphereSobolev (3/2:ℝ) => A v) hRotation)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UPPER_DIST_COMPONENT SUM_VALUES"
    out.flush
  apply lp.ext
  funext k
  have hk := congrArg (fun v : SphereSobolev (-(1/2:ℝ)) => v k) h
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UPPER_DIST_COMPONENT GENERIC_COMPONENT"
    out.flush
  have hLeft := congrArg
    (fun v : SphereSobolev (3/2:ℝ) => sphereSobolevRotationL (1/2:ℝ) i j (A v) k) hInput
  have hOld := sphereSobolevInclusionL_apply (1/2:ℝ) ((1/2:ℝ)-1) (by norm_num)
    (D (sphereSobolevInclusionL ((3/2:ℝ)+1) (3/2:ℝ) (by norm_num) f) +
      A (sphereSobolevRotationL ((3/2:ℝ)+1) i j f)) k
  have hNew := sphereSobolevInclusionL_apply (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    (D (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f) +
      A (sphereSobolevRotationL (5/2:ℝ) i j f)) k
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UPPER_DIST_COMPONENT POINT_INCLUSIONS"
    out.flush
  have hComponentSum := congrArg (fun v : SphereSobolev (1/2:ℝ) => v k) hSum
  have hMiddle := congrArg
    (fun v : harmonicSphereSubspace k => besselWeight (((1/2:ℝ)-1)-(1/2:ℝ)) k • v)
      hComponentSum
  have hScalar : ((1/2:ℝ)-1)-(1/2:ℝ) = (-(1/2:ℝ))-(1/2:ℝ) := by norm_num
  have hWeight := congrArg (fun s : ℝ => besselWeight s k •
    (D (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f) +
      A (sphereSobolevRotationL (5/2:ℝ) i j f)) k) hScalar
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UPPER_DIST_COMPONENT WEIGHT_COMPONENT_TRANSPORT"
    out.flush
  exact hLeft.symm.trans (hk.trans
    (hOld.trans (hMiddle.trans (hWeight.trans hNew.symm))))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UPPER_DIST_COMPONENT PROOF_BODY_COMPLETE"
    out.flush

#eval (show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "UPPER_DIST AFTER_DECL"
  out.flush)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_upper_fixed_input_order

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_upper_fixed_output_order

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_upper_rotation_derivative_distribution
