import Calderon.SmoothSphereRotation
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SmoothSphereRotation

lemma contDiff_coordinateRotation_of_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin 3) (θ : E → ℝ) (X : E → R3)
    (hθ : ContDiff ℝ ∞ θ) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (fun q => coordinateRotation i j (θ q) (X q)) := by
  by_cases hij : i = j
  · simpa only [coordinateRotation,if_pos hij] using hX
  · apply contDiff_piLp'
    intro l
    have hXi : ContDiff ℝ ∞ (fun q => X q i) := by
      apply (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
      exact hX
    have hXj : ContDiff ℝ ∞ (fun q => X q j) := by
      apply (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp
      exact hX
    by_cases hli : l = i
    · subst l
      simp only [coordinateRotation,if_neg hij,PiLp.toLp_apply,if_pos rfl]
      exact (hθ.cos.mul hXi).sub (hθ.sin.mul hXj)
    · by_cases hlj : l = j
      · subst l
        simp only [coordinateRotation,if_neg hij,PiLp.toLp_apply,if_neg hli,if_pos rfl]
        exact (hθ.sin.mul hXi).add (hθ.cos.mul hXj)
      · simp only [coordinateRotation,if_neg hij,PiLp.toLp_apply,if_neg hli,if_neg hlj]
        apply (EuclideanSpace.proj l : R3 →L[ℝ] ℝ).contDiff.comp
        exact hX

lemma contDiff_coordinateRotationSourceMap
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (i j : Fin 3) :
    ContDiff ℝ ∞ (fun q : (ℝ × P) × R3 => (q.1.2,coordinateRotation i j q.1.1 q.2)) := by
  apply ContDiff.prodMk
  · exact contDiff_fst.snd
  · apply contDiff_coordinateRotation_of_smooth
    · exact contDiff_fst.fst
    · exact contDiff_snd

lemma contDiff_matrix_conjugation_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M A : E → Matrix (Fin 3) (Fin 3) ℝ)
    (hM : ContDiff ℝ ∞ M) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun q => (M q)ᵀ * A q * M q) := by
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  apply ContDiff.sum
  intro v hv
  exact (ContDiff.sum (fun u hu =>
    ((contDiff_pi.mp (contDiff_pi.mp hM u) k).mul
      (contDiff_pi.mp (contDiff_pi.mp hA u) v)))).mul
        (contDiff_pi.mp (contDiff_pi.mp hM v) l)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_coordinateRotation_of_smooth
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_coordinateRotationSourceMap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_matrix_conjugation_fields
