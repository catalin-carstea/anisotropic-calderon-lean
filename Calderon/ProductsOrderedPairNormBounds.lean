import Calderon.SphereSobolevCompletion
import Calderon.ProductsOperatorNormBounds

set_option autoImplicit false

/-!
The ordered-pair norm estimate at the original fixed Sobolev carriers and
canonical full operator structures, before actual physical families occur.
-/

open scoped BigOperators

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOrderedPairNormBounds

open OAI.AnisotropicCalderon.SphereHarmonic

/-- The eighteen ordered compositions obey the original norm bound on the
fixed three-half and half Sobolev spaces. -/
theorem norm_sq_smul_sum_ordered_pairs_le_sobolev :
    letI productsOperatorNormedAddCommGroup :
        NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
    letI productsOperatorNormedSpace : NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedAddCommGroup :
        NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedSpace : NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHalfEndNormedAddCommGroup :
        NormedAddCommGroup (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
    letI backgroundHalfEndNormedSpace : NormedSpace ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
    ∀ (q : Fin 3 → Fin 3 → ℝ)
      (fl : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (fh : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
      (ee : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (cq cf ce r : ℝ),
      0 ≤ cq → 0 ≤ cf → 0 ≤ ce →
      (∀ i j : Fin 3, |q i j| ≤ cq) →
      (∀ i : Fin 3, ‖fl i‖ ≤ cf) →
      (∀ i : Fin 3, ‖fh i‖ ≤ cf) →
      (∀ i : Fin 3, ‖ee i‖ ≤ ce) →
      ‖(r ^ 2) • (∑ i : Fin 3, ∑ j : Fin 3,
        (q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j)))‖
        ≤ (18 * cq * cf * ce) * r ^ 2 := by
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace : NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedSpace : NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  letI backgroundHalfEndNormedSpace : NormedSpace ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ)) (σ₁₂ := RingHom.id ℝ)
  intro q fl fh ee cq cf ce r hcq hcf hce hq hfl hfh hee
  exact @OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOperatorNormBounds.norm_sq_smul_sum_ordered_pairs_le
    (SphereSobolev (3/2 : ℝ)) (SphereSobolev (1/2 : ℝ))
    (inferInstance : NormedAddCommGroup (SphereSobolev (3/2 : ℝ)))
    (inferInstance : NormedSpace ℝ (SphereSobolev (3/2 : ℝ)))
    (inferInstance : NormedAddCommGroup (SphereSobolev (1/2 : ℝ)))
    (inferInstance : NormedSpace ℝ (SphereSobolev (1/2 : ℝ)))
    q fl fh ee cq cf ce r hcq hcf hce hq hfl hfh hee

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOrderedPairNormBounds
