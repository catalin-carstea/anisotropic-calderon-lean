import Calderon.ActualLowerHorizontalScalarLeibniz
import Calderon.SphereSobolevShiftedPhysicalDegree

/-! Original horizontal actions plus the original log-radius times physical degree. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SmoothMetricFrame MovingFrameConnection

def referenceHighWeightedHorizontalAction (g : MatrixField) (L q : ℝ)
    (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) :=
  referenceHighHorizontalAction g L q u y i +
    referenceRadiusHorizontalLogDerivative g L q R y i •
      sphereSobolevShiftedDegreeL (3/2 : ℝ) (u y)

def referenceLowerWeightedHorizontalAction (g : MatrixField) (L q : ℝ)
    (R : R3 → ℝ) (v : R3 → SphereSobolev (1/2 : ℝ)) (y : R3) (i : Fin 3) :
    SphereSobolev (-(1/2 : ℝ)) :=
  referenceLowerHorizontalAction g L q v y i +
    referenceRadiusHorizontalLogDerivative g L q R y i •
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (v y)

attribute [local irreducible] referenceHighWeightedHorizontalAction
  referenceLowerWeightedHorizontalAction referenceRadiusHorizontalLogDerivative
  referenceHighHorizontalAction referenceLowerHorizontalAction sphereSobolevShiftedDegreeL
  sphereSobolevInclusionL referenceMetricGramFrame

lemma referenceLowerWeightedHorizontalAction_add
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (u v : R3 → SphereSobolev (1/2 : ℝ)) (y : R3) (i : Fin 3)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    referenceLowerWeightedHorizontalAction g L q R (fun x => u x+v x) y i =
      referenceLowerWeightedHorizontalAction g L q R u y i +
        referenceLowerWeightedHorizontalAction g L q R v y i := by
  have hHorizontal := referenceLowerHorizontalAction_add g L q u v y i hu hv
  have hDegree := congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      referenceRadiusHorizontalLogDerivative g L q R y i • z)
    ((sphereSobolevShiftedDegreeL (1/2 : ℝ)).map_add (u y) (v y))
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b)
    hHorizontal hDegree
  unfold referenceLowerWeightedHorizontalAction
  exact hCombined.trans (by simp only [smul_add]; abel)

lemma referenceLowerWeightedHorizontalAction_smul
    (g : MatrixField) (L q : ℝ) (R c : R3 → ℝ)
    (v : R3 → SphereSobolev (1/2 : ℝ)) (y : R3) (i : Fin 3)
    (hc : DifferentiableAt ℝ c y) (hv : DifferentiableAt ℝ v y) :
    referenceLowerWeightedHorizontalAction g L q R (fun x => c x • v x) y i =
      c y • referenceLowerWeightedHorizontalAction g L q R v y i +
        fderiv ℝ c y (referenceMetricGramFrame g L (q,y) i) •
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (v y) := by
  have hHorizontal := referenceLowerHorizontalAction_smul g L q c v y i hc hv
  have hDegree := congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      referenceRadiusHorizontalLogDerivative g L q R y i • z)
    ((sphereSobolevShiftedDegreeL (1/2 : ℝ)).map_smul (c y) (v y))
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b)
    hHorizontal hDegree
  unfold referenceLowerWeightedHorizontalAction
  exact hCombined.trans (by
    rw [smul_comm (referenceRadiusHorizontalLogDerivative g L q R y i) (c y)]
    simp only [smul_add]
    abel)

lemma contDiffAt_referenceHighWeightedHorizontalAction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y) :
    ContDiffAt ℝ ∞ (fun x => referenceHighWeightedHorizontalAction g L q R u x i) y := by
  have hHorizontal := contDiffAt_referenceHighHorizontalAction g hg L q u y i hu
  have hScalar : ContDiffAt ℝ ∞
      (fun x => referenceRadiusHorizontalLogDerivative g L q R x i) y :=
    (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i hR hr).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  have hDegree := (sphereSobolevShiftedDegreeL (3/2 : ℝ)).contDiff.contDiffAt.comp y hu
  simpa only [referenceHighWeightedHorizontalAction, Function.comp_def, Pi.add_def, Pi.smul_def'] using
    hHorizontal.add (hScalar.smul hDegree)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighWeightedHorizontalAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerWeightedHorizontalAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerWeightedHorizontalAction_add
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerWeightedHorizontalAction_smul
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighWeightedHorizontalAction
