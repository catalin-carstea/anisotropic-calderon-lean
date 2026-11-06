import Calderon.SupportedWeightedL2NullCalculus
import Calderon.SphereSobolevCompletion
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds WeightedBaseSpectral

/-- The original half-to-zero inclusion followed by the original zero-order
sphere isometry. -/
def sphereSobolevHalfToSphereL2L (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereL2 :=
  (sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv

lemma sphereSobolevHalfToSphereL2L_negative_compatibility
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (sphereSobolevHalfToSphereL2L hO hD v)) =
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v := by
  let Z := sphereSobolevZeroEquiv hO hD
  let I0 := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  have hCancel := congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
    (Z.apply_symm_apply (I0 v))
  have hTrans := congrArg
    (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A v)
    (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  exact hCancel.trans hTrans

theorem weighted_half_graph_limits_in_zero_and_sphereL2
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (S : Set R3) (hS : IsCompact S)
    (W : ℕ → R3 → SphereSobolev (1/2:ℝ)) (w : R3 → SphereSobolev (1/2:ℝ))
    (hW : ∀ n, Continuous (W n)) (hw : Continuous w)
    (hSuppW : ∀ n, tsupport (W n) ⊆ S) (hSuppw : tsupport w ⊆ S)
    (hLimit : Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖W n y - w y‖^2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (W n y) -
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (w y)‖^2) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) *
      ‖sphereSobolevHalfToSphereL2L hO hD (W n y) -
        sphereSobolevHalfToSphereL2L hO hD (w y)‖^2) atTop (𝓝 0) := by
  have hNull : SupportedWeightedL2Null g L q S (fun n y => W n y - w y) := by
    refine ⟨fun n => (hW n).sub hw,?_,hLimit⟩
    intro n
    apply closure_minimal ?_ hS.isClosed
    intro y hy
    by_contra hOutside
    have hn : W n y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hOutside (hSuppW n h))
    have hi : w y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hOutside (hSuppw h))
    exact hy (by simp only [hn,hi,sub_self])
  have hZero := SupportedWeightedL2Null.clm hg hS hNull
    (fun _ => sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) (fun _ _ => continuousAt_const)
  have hL2 := SupportedWeightedL2Null.clm hg hS hNull
    (fun _ => sphereSobolevHalfToSphereL2L hO hD) (fun _ _ => continuousAt_const)
  exact ⟨by simpa only [map_sub] using hZero.tendsto,
    by simpa only [map_sub] using hL2.tendsto⟩

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
