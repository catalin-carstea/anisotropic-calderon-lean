import Calderon.FirstOrderCoordinateJetCalculus

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma clm_apply_euclidean_coordinate_sum
    (T : R3 →L[ℝ] SphereSobolev (5/2:ℝ)) (e : R3) :
    T e = ∑ k : Fin 3, e k • T (EuclideanSpace.single k 1) := by
  have hSum : (∑ k : Fin 3, e k • EuclideanSpace.single k 1) = e := by
    ext j
    simp [Pi.single_apply]
  have h := congrArg T hSum
  simpa only [map_sum,map_smul] using h.symm

lemma firstOrderCoordinateAction_frame_eq
    (I : SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (e : R3 → R3) (B : R3 → SphereSobolev (5/2:ℝ) →L[ℝ] W)
    (u : R3 → SphereSobolev (5/2:ℝ)) (y : R3) :
    firstOrderCoordinateAction (fun k y => e y k • I) B u y =
      I (fderiv ℝ u y (e y)) + B y (u y) := by
  have h := congrArg I (clm_apply_euclidean_coordinate_sum (fderiv ℝ u y) (e y))
  have h' : I (fderiv ℝ u y (e y)) =
      ∑ k : Fin 3, e y k • I (fderiv ℝ u y (EuclideanSpace.single k 1)) := by
    simpa only [map_sum,map_smul] using h
  exact congrArg (fun v : W => v+B y (u y)) h'.symm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
