import Calderon.SphereHarmonicBridge
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory Set
open scoped Pointwise
namespace OAI.AnisotropicCalderon.OrthogonalSphereMeasure
open SphereHarmonic

def orthogonalSphereHomeomorph (T : R3 ≃ₗᵢ[ℝ] R3) : UnitSphere ≃ₜ UnitSphere where
  toFun u := ⟨T u, by simpa only [Metric.mem_sphere,dist_zero_right,T.norm_map] using u.property⟩
  invFun u := ⟨T.symm u, by simpa only [Metric.mem_sphere,dist_zero_right,T.symm.norm_map] using u.property⟩
  left_inv u := by apply Subtype.ext; exact T.symm_apply_apply u
  right_inv u := by apply Subtype.ext; exact T.apply_symm_apply u
  continuous_toFun := (T.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (T.symm.continuous.comp continuous_subtype_val).subtype_mk _

lemma orthogonalSphereHomeomorph_apply_val (T : R3 ≃ₗᵢ[ℝ] R3) (u : UnitSphere) :
    (orthogonalSphereHomeomorph T u).val = T u.val := rfl

lemma orthogonalSphereHomeomorph_symm_apply_val (T : R3 ≃ₗᵢ[ℝ] R3) (u : UnitSphere) :
    ((orthogonalSphereHomeomorph T).symm u).val = T.symm u.val := rfl

theorem orthogonal_unitCone_preimage (T : R3 ≃ₗᵢ[ℝ] R3) (s : Set UnitSphere) :
    T ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0 : ℝ) 1 • (Subtype.val '' (orthogonalSphereHomeomorph T ⁻¹' s)) := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨r,hr,w,⟨u,hu,huw⟩,he⟩
    subst w
    refine ⟨r,hr,T.symm u.val,?_,?_⟩
    · refine ⟨(orthogonalSphereHomeomorph T).symm u,?_,rfl⟩
      simpa only [mem_preimage,(orthogonalSphereHomeomorph T).apply_symm_apply] using hu
    · have h := congrArg T.symm he
      simpa only [T.symm.map_smul,T.symm_apply_apply] using h
  · intro hv
    rcases hv with ⟨r,hr,w,⟨u,hu,huw⟩,he⟩
    subst w
    refine ⟨r,hr,T u.val,⟨orthogonalSphereHomeomorph T u,hu,rfl⟩,?_⟩
    have h := congrArg T he
    simpa only [T.map_smul] using h

theorem orthogonalSphereHomeomorph_surfaceMeasure_preserving (T : R3 ≃ₗᵢ[ℝ] R3) :
    MeasurePreserving (orthogonalSphereHomeomorph T) surfaceMeasure surfaceMeasure := by
  refine ⟨(orthogonalSphereHomeomorph T).measurable,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (orthogonalSphereHomeomorph T).measurable hs]
  change (volume : Measure R3).toSphere (orthogonalSphereHomeomorph T ⁻¹' s) =
    (volume : Measure R3).toSphere s
  rw [Measure.toSphere_apply' _ ((orthogonalSphereHomeomorph T).measurable hs),
    Measure.toSphere_apply' _ hs,← orthogonal_unitCone_preimage T s]
  rw [T.measurePreserving.measure_preimage_emb T.toHomeomorph.measurableEmbedding]

theorem orthogonalSphereHomeomorph_sphereProbability_preserving (T : R3 ≃ₗᵢ[ℝ] R3) :
    MeasurePreserving (orthogonalSphereHomeomorph T) sphereProbability sphereProbability := by
  refine ⟨(orthogonalSphereHomeomorph T).measurable,?_⟩
  rw [sphereProbability,Measure.map_smul,
    (orthogonalSphereHomeomorph_surfaceMeasure_preserving T).map_eq]
  exact (orthogonalSphereHomeomorph T).measurable.aemeasurable

end OAI.AnisotropicCalderon.OrthogonalSphereMeasure
