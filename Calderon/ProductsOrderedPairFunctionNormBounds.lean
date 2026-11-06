import Calderon.ProductsOrderedPairNormEqualityBounds

set_option autoImplicit false

open scoped BigOperators

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOrderedPairFunctionNormBounds

open OAI.AnisotropicCalderon.SphereHarmonic

/-- A whole-function ordered-pair identity gives its pointwise Sobolev norm estimate. -/
theorem norm_le_of_fun_eq_sq_smul_sum_ordered_pairs_sobolev :
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
    ∀ (A : R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (coeff : Fin 3 → Fin 3 → R3 → ℝ)
      (Fl : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (Fh : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
      (Eh : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (R : R3 → ℝ),
      A = (fun y : R3 => (R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
        coeff i j y • ((Fl i y).comp (Eh j y) + (Eh i y).comp (Fh j y)))) →
      ∀ (y : R3) (CQ CF CE : ℝ),
      0 ≤ CQ → 0 ≤ CF → 0 ≤ CE →
      (∀ i j : Fin 3, |coeff i j y| ≤ CQ) →
      (∀ i : Fin 3, ‖Fl i y‖ ≤ CF) →
      (∀ i : Fin 3, ‖Fh i y‖ ≤ CF) →
      (∀ i : Fin 3, ‖Eh i y‖ ≤ CE) →
      ‖A y‖ ≤ (18 * CQ * CF * CE) * (R y)^2 := by
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
  intro A coeff Fl Fh Eh R hA y CQ CF CE hCQ hCF hCE hcoeff hFl hFh hEh
  exact OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOrderedPairNormEqualityBounds.norm_le_of_eq_sq_smul_sum_ordered_pairs_sobolev
    (A y) (fun i j => coeff i j y) (fun i => Fl i y)
    (fun i => Fh i y) (fun i => Eh i y) CQ CF CE (R y)
    (congrFun hA y) hCQ hCF hCE hcoeff hFl hFh hEh

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsOrderedPairFunctionNormBounds
