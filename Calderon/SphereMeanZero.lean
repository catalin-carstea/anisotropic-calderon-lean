import Calderon.SphereHarmonicBridge

noncomputable section
open MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

lemma C_harmonicHomogeneous (c : ℝ) :
    C c ∈ harmonicHomogeneous 0 := by
  refine ⟨isHomogeneous_C (Fin 3) c, ?_⟩
  simp [laplacian]

def sphereMean : SphereL2 →L[ℝ] ℝ :=
  innerSL ℝ (polynomialSphereL2 (C 1))

def meanZeroSphere : Submodule ℝ SphereL2 := sphereMean.ker

lemma meanZeroSphere_isClosed : IsClosed (meanZeroSphere : Set SphereL2) :=
  sphereMean.isClosed_ker

lemma sphereMean_polynomialSphereL2 (p : MvPolynomial (Fin 3) ℝ) :
    sphereMean (polynomialSphereL2 p) =
      ∫ x : UnitSphere, p.eval (x.val : Fin 3 → ℝ) ∂sphereProbability := by
  simp [sphereMean, innerSL_apply_apply, polynomialSphereL2_inner]

lemma polynomialSphere_integral_eq_zero (hO : OrthogonalSphereHarmonics)
    (k : ℕ) (hk : k ≠ 0) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    (∫ x : UnitSphere, p.eval (x.val : Fin 3 → ℝ) ∂sphereProbability) = 0 := by
  have h := hO k 0 hk (polynomialSphereL2 p) (polynomialSphereL2_mem k p hp)
    (polynomialSphereL2 (C 1)) (polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1))
  simpa [polynomialSphereL2_inner] using h

lemma harmonicSphereSubspace_le_meanZero (hO : OrthogonalSphereHarmonics)
    (k : ℕ) (hk : k ≠ 0) : harmonicSphereSubspace k ≤ meanZeroSphere := by
  rintro u ⟨p, hp, rfl⟩
  change sphereMean (polynomialSphereL2 p) = 0
  rw [sphereMean_polynomialSphereL2]
  exact polynomialSphere_integral_eq_zero hO k hk p hp

lemma positiveHarmonicSpan_le_meanZero (hO : OrthogonalSphereHarmonics) :
    (⨆ k : ℕ, harmonicSphereSubspace (k + 1)) ≤ meanZeroSphere := by
  refine iSup_le fun k => harmonicSphereSubspace_le_meanZero hO (k + 1) ?_
  omega

lemma positiveHarmonicClosure_le_meanZero (hO : OrthogonalSphereHarmonics) :
    (⨆ k : ℕ, harmonicSphereSubspace (k + 1)).topologicalClosure ≤ meanZeroSphere := by
  exact Submodule.topologicalClosure_minimal _ (positiveHarmonicSpan_le_meanZero hO)
    meanZeroSphere_isClosed

end OAI.AnisotropicCalderon.SphereHarmonic
