import Calderon.ProductsOrderedPairNormBounds

set_option autoImplicit false

/-!
Equality transport for the ordered-pair norm estimate at the fixed Sobolev
carriers and the same six canonical full operator structures as the source
bound. Actual physical families and their exact expansion remain caller data.
-/

open scoped BigOperators

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOrderedPairNormEqualityBounds

open OAI.AnisotropicCalderon.SphereHarmonic

/-- An exact squared-radius ordered-pair expansion transfers its canonical
Sobolev operator norm bound to an arbitrary operator. -/
theorem norm_le_of_eq_sq_smul_sum_ordered_pairs_sobolev :
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
    ∀ (a : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (q : Fin 3 → Fin 3 → ℝ)
      (fl : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (fh : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
      (ee : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (cq cf ce r : ℝ),
      a = (r ^ 2) • (∑ i : Fin 3, ∑ j : Fin 3,
        (q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j))) →
      0 ≤ cq → 0 ≤ cf → 0 ≤ ce →
      (∀ i j : Fin 3, |q i j| ≤ cq) →
      (∀ i : Fin 3, ‖fl i‖ ≤ cf) →
      (∀ i : Fin 3, ‖fh i‖ ≤ cf) →
      (∀ i : Fin 3, ‖ee i‖ ≤ ce) →
      ‖a‖ ≤ (18 * cq * cf * ce) * r ^ 2 := by
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
  intro a q fl fh ee cq cf ce r hA hcq hcf hce hq hfl hfh hee
  have hnorm : ‖a‖ = ‖(r ^ 2) • (∑ i : Fin 3, ∑ j : Fin 3,
      (q i j) • ((fl i).comp (ee j) + (ee i).comp (fh j)))‖ :=
    congrArg (fun t : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => ‖t‖) hA
  exact hnorm.trans_le
    (OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOrderedPairNormBounds.norm_sq_smul_sum_ordered_pairs_le_sobolev
      q fl fh ee cq cf ce r hcq hcf hce hq hfl hfh hee)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOrderedPairNormEqualityBounds
