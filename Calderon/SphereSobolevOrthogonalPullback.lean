import Calderon.OrthogonalHarmonicPolynomialPullback
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

/-! Expanded before source in EXPANSION-sphere-sobolev-orthogonal-pullback-v001.json.
Harmonic block parent is an author candidate awaiting serial checks.
No equal-order norm-smoothness in the rotation angle is asserted. -/

lemma harmonicSphereOrthogonalPullback_symm_apply (e : R3 ≃ₗᵢ[ℝ] R3) (k : ℕ)
    (u : harmonicSphereSubspace k) :
    harmonicSphereOrthogonalPullback e.symm k (harmonicSphereOrthogonalPullback e k u) = u := by
  apply Subtype.ext
  change sphereL2OrthogonalPullback e.symm (sphereL2OrthogonalPullback e u.val) = u.val
  rcases u.property with ⟨p,hp,hpu⟩
  rw [← hpu,sphereL2OrthogonalPullback_polynomialSphereL2,
    sphereL2OrthogonalPullback_polynomialSphereL2,polynomialOrthogonalPullback_symm_apply]

def sphereSobolevOrthogonalPullbackL (s : ℝ) (e : R3 ≃ₗᵢ[ℝ] R3) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  lp.mapCLM 2 (fun k => (harmonicSphereOrthogonalPullback e k).toContinuousLinearMap)
    (show (0 : ℝ) ≤ 1 by norm_num) (by
      intro k
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro u
      simp only [LinearIsometry.coe_toContinuousLinearMap,LinearIsometry.norm_map,one_mul]
      exact le_rfl)

lemma norm_sphereSobolevOrthogonalPullbackL_le (s : ℝ) (e : R3 ≃ₗᵢ[ℝ] R3) :
    ‖sphereSobolevOrthogonalPullbackL s e‖ ≤ 1 := by
  unfold sphereSobolevOrthogonalPullbackL
  exact lp.norm_mapCLM_le _ _ _ _

lemma sphereSobolevOrthogonalPullbackL_apply (s : ℝ) (e : R3 ≃ₗᵢ[ℝ] R3)
    (u : SphereSobolev s) (k : ℕ) :
    sphereSobolevOrthogonalPullbackL s e u k = harmonicSphereOrthogonalPullback e k (u k) := rfl

lemma sphereSobolevCoefficientL_orthogonalPullback (s : ℝ) (e : R3 ≃ₗᵢ[ℝ] R3)
    (u : SphereSobolev s) (k : ℕ) :
    sphereSobolevCoefficientL s k (sphereSobolevOrthogonalPullbackL s e u) =
      harmonicSphereOrthogonalPullback e k (sphereSobolevCoefficientL s k u) := by
  change besselWeight (-s) k • harmonicSphereOrthogonalPullback e k (u k) =
    harmonicSphereOrthogonalPullback e k (besselWeight (-s) k • u k)
  exact ((harmonicSphereOrthogonalPullback e k).map_smul _ _).symm

lemma sphereSobolevInclusionL_orthogonalPullback (s t : ℝ) (hts : t ≤ s)
    (e : R3 ≃ₗᵢ[ℝ] R3) :
    (sphereSobolevInclusionL s t hts).comp (sphereSobolevOrthogonalPullbackL s e) =
      (sphereSobolevOrthogonalPullbackL t e).comp (sphereSobolevInclusionL s t hts) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext t
  intro k
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,
    sphereSobolevCoefficientL_orthogonalPullback]

lemma sphereSobolevOrthogonalPullbackL_single (s : ℝ) (e : R3 ≃ₗᵢ[ℝ] R3)
    (k : ℕ) (u : harmonicSphereSubspace k) :
    sphereSobolevOrthogonalPullbackL s e (sphereSobolevSingleL s k u) =
      sphereSobolevSingleL s k (harmonicSphereOrthogonalPullback e k u) := by
  apply sphereSobolev_ext s
  intro j
  rw [sphereSobolevCoefficientL_orthogonalPullback]
  by_cases hj : j = k
  · subst j
    rw [sphereSobolevCoefficientL_single_self,sphereSobolevCoefficientL_single_self]
  · rw [sphereSobolevCoefficientL_single_ne s k j hj,sphereSobolevCoefficientL_single_ne s k j hj]
    exact (harmonicSphereOrthogonalPullback e j).map_zero

lemma sphereSobolevOrthogonalPullbackL_symm_apply (s : ℝ) (e : R3 ≃ₗᵢ[ℝ] R3)
    (u : SphereSobolev s) :
    sphereSobolevOrthogonalPullbackL s e.symm (sphereSobolevOrthogonalPullbackL s e u) = u := by
  apply sphereSobolev_ext s
  intro k
  rw [sphereSobolevCoefficientL_orthogonalPullback,sphereSobolevCoefficientL_orthogonalPullback,
    harmonicSphereOrthogonalPullback_symm_apply]

lemma norm_sphereSobolevOrthogonalPullbackL_apply (s : ℝ) (e : R3 ≃ₗᵢ[ℝ] R3)
    (u : SphereSobolev s) : ‖sphereSobolevOrthogonalPullbackL s e u‖ = ‖u‖ := by
  have hle (a : R3 ≃ₗᵢ[ℝ] R3) (v : SphereSobolev s) :
      ‖sphereSobolevOrthogonalPullbackL s a v‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖sphereSobolevOrthogonalPullbackL s a‖ * ‖v‖ :=
        (sphereSobolevOrthogonalPullbackL s a).le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (norm_sphereSobolevOrthogonalPullbackL_le s a) (norm_nonneg _)
      _ = _ := one_mul _
  apply le_antisymm (hle e u)
  simpa only [sphereSobolevOrthogonalPullbackL_symm_apply] using hle e.symm (sphereSobolevOrthogonalPullbackL s e u)

def sphereSobolevOrthogonalPullback (s : ℝ) (e : R3 ≃ₗᵢ[ℝ] R3) :
    SphereSobolev s →ₗᵢ[ℝ] SphereSobolev s where
  toLinearMap := (sphereSobolevOrthogonalPullbackL s e).toLinearMap
  norm_map' := norm_sphereSobolevOrthogonalPullbackL_apply s e

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.harmonicSphereOrthogonalPullback_symm_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevOrthogonalPullbackL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevOrthogonalPullbackL_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevOrthogonalPullbackL_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_orthogonalPullback
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_orthogonalPullback
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevOrthogonalPullbackL_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevOrthogonalPullbackL_symm_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevOrthogonalPullbackL_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevOrthogonalPullback
