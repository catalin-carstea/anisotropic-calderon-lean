import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.SphereSobolevCoordinateInclusion
import Mathlib.Tactic.Module

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily DirichletFamily.DriftBootstrap
attribute [local irreducible] sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL sphereSobolevShiftedDegreeL sphereSobolevSingleL

lemma linearCoordinate_degree_commutator_constant_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (a : harmonicSphereSubspace 0) :
    sphereSobolevLinearCoordinateMulL hF hO hD (s-1) d
      (sphereSobolevShiftedDegreeL s (sphereSobolevSingleL s 0 a)) -
    sphereSobolevShiftedDegreeL s
      (sphereSobolevLinearCoordinateMulL hF hO hD s d (sphereSobolevSingleL s 0 a)) =
    sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevRadialDriftAdjointL hF hO hD s d (sphereSobolevSingleL s 0 a) -
       sphereSobolevRadialDriftL hF hO hD s d (sphereSobolevSingleL s 0 a)) := by
  let x := sphereSobolevSingleL s 0 a
  let us := sphereSobolevSingleL s 1 (radialDriftAdjointBlockL hF d 0 a)
  let ut := sphereSobolevSingleL (s-1) 1 (radialDriftAdjointBlockL hF d 0 a)
  let B := sphereSobolevShiftedDegreeL s
  let Ms := sphereSobolevLinearCoordinateMulL hF hO hD s d
  let Mt := sphereSobolevLinearCoordinateMulL hF hO hD (s-1) d
  let I := sphereSobolevInclusionL s (s-1) (by linarith)
  have hBx : B x = 0 := by
    simpa only [Nat.cast_zero,zero_smul] using sphereSobolevShiftedDegreeL_single s 0 a
  have hMx : Ms x = -us := sphereSobolevLinearCoordinateMulL_constant hF hO hD s d a
  have hBu : B us = ut := by
    simpa only [Nat.cast_one,one_smul] using
      sphereSobolevShiftedDegreeL_single s 1 (radialDriftAdjointBlockL hF d 0 a)
  have hLeft1 : Mt (B x) = 0 := (congrArg Mt hBx).trans (Mt.map_zero)
  have hLeft2 : B (Ms x) = -ut :=
    (congrArg B hMx).trans ((B.map_neg us).trans (congrArg (fun z => -z) hBu))
  have hAdj : sphereSobolevRadialDriftAdjointL hF hO hD s d x = us :=
    sphereSobolevRadialDriftAdjointL_single hF hO hD s d 0 a
  have hDrift : sphereSobolevRadialDriftL hF hO hD s d x = 0 :=
    sphereSobolevRadialDriftL_constant hF hO hD s d a
  have hDiff : sphereSobolevRadialDriftAdjointL hF hO hD s d x -
      sphereSobolevRadialDriftL hF hO hD s d x = us :=
    (congrArg₂ (fun u v : SphereSobolev s => u-v) hAdj hDrift).trans (sub_zero us)
  have hRight : I (sphereSobolevRadialDriftAdjointL hF hO hD s d x -
      sphereSobolevRadialDriftL hF hO hD s d x) = ut :=
    (congrArg I hDiff).trans (sphereSobolevInclusionL_single s (s-1) (by linarith) 1
      (radialDriftAdjointBlockL hF d 0 a))
  have hLeft : Mt (B x)-B (Ms x) = ut :=
    (congrArg₂ (fun u v : SphereSobolev (s-1) => u-v) hLeft1 hLeft2).trans (by simp only [zero_sub,neg_neg])
  exact hLeft.trans hRight.symm

lemma linearCoordinate_degree_commutator_succ_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (k : ℕ) (a : harmonicSphereSubspace (k+1)) :
    sphereSobolevLinearCoordinateMulL hF hO hD (s-1) d
      (sphereSobolevShiftedDegreeL s (sphereSobolevSingleL s (k+1) a)) -
    sphereSobolevShiftedDegreeL s
      (sphereSobolevLinearCoordinateMulL hF hO hD s d (sphereSobolevSingleL s (k+1) a)) =
    sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevRadialDriftAdjointL hF hO hD s d (sphereSobolevSingleL s (k+1) a) -
       sphereSobolevRadialDriftL hF hO hD s d (sphereSobolevSingleL s (k+1) a)) := by
  let x := sphereSobolevSingleL s (k+1) a
  let xt := sphereSobolevSingleL (s-1) (k+1) a
  let ls := sphereSobolevSingleL s k (radialDriftBlockL hF d k a)
  let us := sphereSobolevSingleL s (k+2) (radialDriftAdjointBlockL hF d (k+1) a)
  let lt := sphereSobolevSingleL (s-1) k (radialDriftBlockL hF d k a)
  let ut := sphereSobolevSingleL (s-1) (k+2) (radialDriftAdjointBlockL hF d (k+1) a)
  let B := sphereSobolevShiftedDegreeL s
  let Ms := sphereSobolevLinearCoordinateMulL hF hO hD s d
  let Mt := sphereSobolevLinearCoordinateMulL hF hO hD (s-1) d
  let I := sphereSobolevInclusionL s (s-1) (by linarith)
  have hBx : B x = ((k+1 : ℕ) : ℝ) • xt := sphereSobolevShiftedDegreeL_single s (k+1) a
  have hMx : Ms x = -ls-us := sphereSobolevLinearCoordinateMulL_single_succ hF hO hD s d k a
  have hMxt : Mt xt = -lt-ut := sphereSobolevLinearCoordinateMulL_single_succ hF hO hD (s-1) d k a
  have hBl : B ls = (k : ℝ) • lt :=
    sphereSobolevShiftedDegreeL_single s k (radialDriftBlockL hF d k a)
  have hBu : B us = ((k+2 : ℕ) : ℝ) • ut :=
    sphereSobolevShiftedDegreeL_single s (k+2) (radialDriftAdjointBlockL hF d (k+1) a)
  have hLeft1 : Mt (B x) = ((k+1 : ℕ) : ℝ) • (-lt-ut) :=
    (congrArg Mt hBx).trans ((Mt.map_smul _ _).trans (congrArg (fun z => ((k+1 : ℕ) : ℝ) • z) hMxt))
  have hLeft2 : B (Ms x) = -((k : ℝ) • lt)-((k+2 : ℕ) : ℝ) • ut :=
    (congrArg B hMx).trans ((B.map_sub (-ls) us).trans
      ((congrArg₂ (fun u v : SphereSobolev (s-1) => u-v) (B.map_neg ls) rfl).trans
        (congrArg₂ (fun u v : SphereSobolev (s-1) => -u-v) hBl hBu)))
  have hAdj : sphereSobolevRadialDriftAdjointL hF hO hD s d x = us :=
    sphereSobolevRadialDriftAdjointL_single hF hO hD s d (k+1) a
  have hDrift : sphereSobolevRadialDriftL hF hO hD s d x = ls :=
    sphereSobolevRadialDriftL_single hF hO hD s d k a
  have hRight : I (sphereSobolevRadialDriftAdjointL hF hO hD s d x -
      sphereSobolevRadialDriftL hF hO hD s d x) = ut-lt :=
    (congrArg I (congrArg₂ (fun u v : SphereSobolev s => u-v) hAdj hDrift)).trans
      ((I.map_sub us ls).trans
        (congrArg₂ (fun u v : SphereSobolev (s-1) => u-v)
          (sphereSobolevInclusionL_single s (s-1) (by linarith) (k+2) (radialDriftAdjointBlockL hF d (k+1) a))
          (sphereSobolevInclusionL_single s (s-1) (by linarith) k (radialDriftBlockL hF d k a))))
  have hAlgebra : ((k+1 : ℕ) : ℝ) • (-lt-ut) -
      (-((k : ℝ) • lt)-((k+2 : ℕ) : ℝ) • ut) = ut-lt := by
    push_cast
    module
  exact (congrArg₂ (fun u v : SphereSobolev (s-1) => u-v) hLeft1 hLeft2).trans
    (hAlgebra.trans hRight.symm)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.linearCoordinate_degree_commutator_constant_graph
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.linearCoordinate_degree_commutator_succ_graph
