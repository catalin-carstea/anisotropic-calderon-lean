import Calderon.SphereMeanZero
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section
open MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

def positiveHarmonicSpan : Submodule ℝ SphereL2 :=
  ⨆ k : ℕ, harmonicSphereSubspace (k + 1)

def sphereConstantSpan : Submodule ℝ SphereL2 :=
  ℝ ∙ polynomialSphereL2 (C 1)

lemma sphereConstant_inner_self :
    ⟪polynomialSphereL2 (C 1), polynomialSphereL2 (C 1)⟫_ℝ = 1 := by
  rw [polynomialSphereL2_inner]
  simp

lemma sphereMean_constant_one : sphereMean (polynomialSphereL2 (C 1)) = 1 := by
  simpa [sphereMean, innerSL_apply_apply] using sphereConstant_inner_self

lemma harmonicSphereSubspace_zero_eq : harmonicSphereSubspace 0 = sphereConstantSpan := by
  apply le_antisymm
  · rintro u ⟨p,hp,rfl⟩
    have hd : p.totalDegree = 0 := (totalDegree_zero_iff_isHomogeneous (Fin 3)).2 hp.1
    have he := (totalDegree_eq_zero_iff_eq_C (p := p)).mp hd
    rw [he]
    change polynomialSphereL2 (C (p.coeff 0)) ∈ ℝ ∙ polynomialSphereL2 (C 1)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨p.coeff 0, ?_⟩
    rw [← map_smul]
    simp [smul_eq_C_mul]
  · apply Submodule.span_le.mpr
    rintro u (rfl : u = _)
    exact polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)

lemma sphereConstantSpan_orthogonal_eq : sphereConstantSpanᗮ = meanZeroSphere := by
  ext u
  change u ∈ (ℝ ∙ polynomialSphereL2 (C 1))ᗮ ↔ sphereMean u = 0
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rfl

lemma sphereConstant_mem_positiveHarmonic_orthogonal (hO : OrthogonalSphereHarmonics) :
    polynomialSphereL2 (C 1) ∈ positiveHarmonicSpanᗮ := by
  apply (positiveHarmonicSpan.mem_orthogonal' _).mpr
  intro u hu
  have hm := positiveHarmonicSpan_le_meanZero hO hu
  change sphereMean u = 0 at hm
  simpa [sphereMean, innerSL_apply_apply] using hm

lemma positiveHarmonic_orthogonal_eq_constants (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) : positiveHarmonicSpanᗮ = sphereConstantSpan := by
  apply le_antisymm
  · intro v hv
    let e := polynomialSphereL2 (C 1)
    let w := v - sphereMean v • e
    have hwmean : sphereMean w = 0 := by
      change sphereMean (v - sphereMean v • polynomialSphereL2 (C 1)) = 0
      rw [map_sub,map_smul,sphereMean_constant_one]
      simp
    have hwP : w ∈ positiveHarmonicSpanᗮ :=
      positiveHarmonicSpanᗮ.sub_mem hv
        (positiveHarmonicSpanᗮ.smul_mem _ (sphereConstant_mem_positiveHarmonic_orthogonal hO))
    have hwAll : w ∈ (⨆ k : ℕ, harmonicSphereSubspace k)ᗮ := by
      apply (Submodule.mem_orthogonal _ _).mpr
      have hle : (⨆ k : ℕ, harmonicSphereSubspace k) ≤ (ℝ ∙ w)ᗮ := by
        refine iSup_le fun k => ?_
        intro u hu
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        cases k with
        | zero =>
            have hw0 : w ∈ (harmonicSphereSubspace 0)ᗮ := by
              rw [harmonicSphereSubspace_zero_eq,sphereConstantSpan_orthogonal_eq]
              exact hwmean
            exact (harmonicSphereSubspace 0).inner_left_of_mem_orthogonal hu hw0
        | succ k =>
            have hup : u ∈ positiveHarmonicSpan :=
              (le_iSup (fun k : ℕ => harmonicSphereSubspace (k+1)) k) hu
            exact positiveHarmonicSpan.inner_left_of_mem_orthogonal hup hwP
      intro u hu
      exact inner_eq_zero_symm.mp
        (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu))
    have hwzero : w = 0 := by
      have hcl : w ∈ (⨆ k : ℕ, harmonicSphereSubspace k).topologicalClosureᗮ := by
        rwa [Submodule.orthogonal_closure]
      rw [hD,Submodule.top_orthogonal_eq_bot] at hcl
      exact hcl
    have heq : v = sphereMean v • e := sub_eq_zero.mp hwzero
    rw [heq]
    exact sphereConstantSpan.smul_mem _ (Submodule.mem_span_singleton_self e)
  · apply Submodule.span_le.mpr
    rintro u (rfl : u = _)
    exact sphereConstant_mem_positiveHarmonic_orthogonal hO

lemma positiveHarmonicClosure_eq_meanZero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) : positiveHarmonicSpan.topologicalClosure = meanZeroSphere := by
  rw [← positiveHarmonicSpan.orthogonal_orthogonal_eq_closure,
    positiveHarmonic_orthogonal_eq_constants hO hD,sphereConstantSpan_orthogonal_eq]

end OAI.AnisotropicCalderon.SphereHarmonic
