import Calderon.NativeHarmonicLiftFiniteCore

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace DirectSum Topology ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open NativePolynomialBulkMoments NativeFiniteHarmonicH2Bound
  SphereHarmonic SmoothSphereRotationProjection SpectralWeightedGraph DirichletFamily

def harmonicLiftCompletion (hF : SphereFischerInner) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2 :=
  LinearMap.extendOfNorm (E := HarmonicFiniteCoefficients)
    (Eₗ := SphereSobolev (3/2 : ℝ)) (F := BallSobolev 2)
    (harmonicNativeFiniteL hF) harmonicBoundaryFiniteL

local instance completionBoundaryNormedAddCommGroup :
    NormedAddCommGroup (SphereSobolev (3/2 : ℝ)) := inferInstance
local instance completionBoundaryNormedSpace :
    NormedSpace ℝ (SphereSobolev (3/2 : ℝ)) := inferInstance

attribute [local irreducible] harmonicNativeFiniteL harmonicBoundaryFiniteL



lemma harmonicLiftCompletion_finite (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (a : HarmonicFiniteCoefficients) :
    harmonicLiftCompletion hF (harmonicBoundaryFiniteL a) = harmonicNativeFiniteL hF a := by
  trace "extension: entered proof"
  unfold harmonicLiftCompletion
  trace "extension: unfolded completion"
  have hd : DenseRange
      (harmonicBoundaryFiniteL : HarmonicFiniteCoefficients → SphereSobolev (3/2 : ℝ)) := by
    intro v
    have hmem (n : ℕ) : sphereSobolevPartialSum (3/2 : ℝ) n v ∈
        Set.range (harmonicBoundaryFiniteL : HarmonicFiniteCoefficients → SphereSobolev (3/2 : ℝ)) := by
      refine ⟨∑ k ∈ Finset.range n,
        DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace k)) k
          (sphereSobolevCoefficientL (3/2 : ℝ) k v), ?_⟩
      simp only [map_sum,harmonicBoundaryFiniteL,DirectSum.toModule_lof,
        sphereSobolevPartialSum,ContinuousLinearMap.coe_coe]
    exact isClosed_closure.mem_of_tendsto
      (tendsto_sphereSobolevPartialSum (3/2 : ℝ) v)
      (Filter.Eventually.of_forall fun n => subset_closure (hmem n))
  trace "extension: density established"
  apply LinearMap.extendOfNorm_eq
  · trace "extension: apply matched, density goal"
    exact hd
  · trace "extension: bound goal"
    exact ⟨Real.sqrt (3*sphereSurfaceMass), norm_harmonicNativeFiniteL_le hF hO⟩

lemma norm_harmonicLiftCompletion_le (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (u : SphereSobolev (3/2 : ℝ)) :
    ‖harmonicLiftCompletion hF u‖ ≤ Real.sqrt (3*sphereSurfaceMass)*‖u‖ := by
  trace "extension: entered proof"
  unfold harmonicLiftCompletion
  trace "extension: unfolded completion"
  have hd : DenseRange
      (harmonicBoundaryFiniteL : HarmonicFiniteCoefficients → SphereSobolev (3/2 : ℝ)) := by
    intro v
    have hmem (n : ℕ) : sphereSobolevPartialSum (3/2 : ℝ) n v ∈
        Set.range (harmonicBoundaryFiniteL : HarmonicFiniteCoefficients → SphereSobolev (3/2 : ℝ)) := by
      refine ⟨∑ k ∈ Finset.range n,
        DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace k)) k
          (sphereSobolevCoefficientL (3/2 : ℝ) k v), ?_⟩
      simp only [map_sum,harmonicBoundaryFiniteL,DirectSum.toModule_lof,
        sphereSobolevPartialSum,ContinuousLinearMap.coe_coe]
    exact isClosed_closure.mem_of_tendsto
      (tendsto_sphereSobolevPartialSum (3/2 : ℝ) v)
      (Filter.Eventually.of_forall fun n => subset_closure (hmem n))
  trace "extension: density established"
  apply LinearMap.norm_extendOfNorm_apply_le
  · trace "extension: norm apply matched, density goal"
    exact hd
  · trace "extension: norm bound goal"
    exact norm_harmonicNativeFiniteL_le hF hO

#print axioms harmonicLiftCompletion
#print axioms harmonicLiftCompletion_finite
#print axioms norm_harmonicLiftCompletion_le
end OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
