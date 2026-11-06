import Calderon.ActualHighAdjointWeightedCorrectionPointwiseIdentity
import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.ProductsOperatorNormBounds
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
An actual high moving correction estimate from the selected weighted identity.
The numerical current-point caps are conditional assembly inputs; this module
does not add hypotheses to the original uniform Products target.
-/

open Set Metric
open scoped BigOperators ContDiff Topology

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  NativeThreeHalfCoefficientMultiplier

private theorem eq_ordered_five_terms_of_sq_smul_eq
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T D E : U →L[ℝ] V) (C : Fin 3 → U →L[ℝ] V)
    (N K : Fin 3 → U →L[ℝ] U) (i : Fin 3) (r f : ℝ) (hr : r ≠ 0)
    (hEq : r ^ 2 • E =
      (r ^ 2 • T).comp (K i)
        + (∑ j : Fin 3, (C j).comp (r ^ 2 • N j))
        + (∑ j : Fin 3, D.comp ((K j).comp (r ^ 3 • N j)))
        + (∑ j : Fin 3, (r ^ 2 • T).comp ((K j).comp (r ^ 2 • N j)))
        + f • (r ^ 3 • T)) :
    E = T.comp (K i) + (∑ j : Fin 3, (C j).comp (N j))
      + r • (∑ j : Fin 3, D.comp ((K j).comp (N j)))
      + (r ^ 2) • (∑ j : Fin 3, T.comp ((K j).comp (N j)))
      + (r * f) • T := by
  have hFactor :
      (r ^ 2 • T).comp (K i)
        + (∑ j : Fin 3, (C j).comp (r ^ 2 • N j))
        + (∑ j : Fin 3, D.comp ((K j).comp (r ^ 3 • N j)))
        + (∑ j : Fin 3, (r ^ 2 • T).comp ((K j).comp (r ^ 2 • N j)))
        + f • (r ^ 3 • T) =
      r ^ 2 • (T.comp (K i) + (∑ j : Fin 3, (C j).comp (N j))
        + r • (∑ j : Fin 3, D.comp ((K j).comp (N j)))
        + (r ^ 2) • (∑ j : Fin 3, T.comp ((K j).comp (N j)))
        + (r * f) • T) := by
    ext u
    simp only [Fin.sum_univ_three, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_smul]
    module
  have hCancel := congrArg (fun A : U →L[ℝ] V => (r ^ 2)⁻¹ • A) (hEq.trans hFactor)
  simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hr), one_smul] using hCancel

/-- Specialize the ordered cancellation argument to the prescribed Sobolev
operator structures before inserting the actual physical families. -/
private theorem eq_ordered_five_terms_of_sq_smul_eq_sobolev :
    letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    ∀ (T D E : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (C : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (N K : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
      (i : Fin 3) (r f : ℝ), r ≠ 0 →
      (r ^ 2 • E =
        (r ^ 2 • T).comp (K i)
          + (∑ j : Fin 3, (C j).comp (r ^ 2 • N j))
          + (∑ j : Fin 3, D.comp ((K j).comp (r ^ 3 • N j)))
          + (∑ j : Fin 3, (r ^ 2 • T).comp ((K j).comp (r ^ 2 • N j)))
          + f • (r ^ 3 • T)) →
      E = T.comp (K i) + (∑ j : Fin 3, (C j).comp (N j))
        + r • (∑ j : Fin 3, D.comp ((K j).comp (N j)))
        + (r ^ 2) • (∑ j : Fin 3, T.comp ((K j).comp (N j)))
        + (r * f) • T := by
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  intro T D E C N K i r f hr hEq
  exact @eq_ordered_five_terms_of_sq_smul_eq
    (SphereSobolev (3/2 : ℝ)) (SphereSobolev (1/2 : ℝ))
    (inferInstance : NormedAddCommGroup (SphereSobolev (3/2 : ℝ)))
    (inferInstance : NormedSpace ℝ (SphereSobolev (3/2 : ℝ)))
    (inferInstance : NormedAddCommGroup (SphereSobolev (1/2 : ℝ)))
    (inferInstance : NormedSpace ℝ (SphereSobolev (1/2 : ℝ)))
    T D E C N K i r f hr hEq

/-- Freeze the prescribed Sobolev operator structures before applying the
abstract five-term norm bound to the actual correction. -/
private theorem norm_le_of_eq_ordered_five_terms_sobolev :
    letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    ∀ (T D E : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (C : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (N J : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
      (i : Fin 3) (m cn cm cg r f : ℝ),
      0 ≤ m → 0 ≤ cn → 0 ≤ cm → 0 ≤ cg → 0 ≤ r → r ≤ 1 →
      ‖T‖ ≤ m / 2 → ‖D‖ ≤ m →
      (∀ j : Fin 3, ‖C j‖ ≤ m) →
      (∀ j : Fin 3, ‖N j‖ ≤ cn) →
      (∀ j : Fin 3, ‖J j‖ ≤ cm) → |r * f| ≤ cg →
      (E = T.comp (J i) + (∑ j : Fin 3, (C j).comp (N j))
        + r • (∑ j : Fin 3, D.comp ((J j).comp (N j)))
        + (r ^ 2) • (∑ j : Fin 3, T.comp ((J j).comp (N j)))
        + (r * f) • T) →
      ‖E‖ ≤ 1 + (m / 2) * cm + 3 * m * cn + 3 * m * cm * cn
        + 3 * (m / 2) * cm * cn + cg * (m / 2) := by
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  intro T D E C N J i m cn cm cg r f hm hcn hcm hcg hr0 hr1 hT hD hC hN hJ hrf hE
  exact @ProductsOperatorNormBounds.norm_le_of_eq_ordered_five_terms
    (SphereSobolev (3/2 : ℝ)) (SphereSobolev (1/2 : ℝ))
    (inferInstance : NormedAddCommGroup (SphereSobolev (3/2 : ℝ)))
    (inferInstance : NormedSpace ℝ (SphereSobolev (3/2 : ℝ)))
    (inferInstance : NormedAddCommGroup (SphereSobolev (1/2 : ℝ)))
    (inferInstance : NormedSpace ℝ (SphereSobolev (1/2 : ℝ)))
    T D E C N J i m cn cm cg r f hm hcn hcm hcg hr0 hr1 hT hD hC hN hJ hrf hE

/-- Combine weighted cancellation and the norm estimate before inserting
the actual physical operator families. -/
theorem norm_le_of_sq_smul_eq_ordered_five_terms_sobolev :
    letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    ∀ (T D E : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (C : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (N J : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
      (i : Fin 3) (m cn cm cg r f : ℝ), r ≠ 0 →
      0 ≤ m → 0 ≤ cn → 0 ≤ cm → 0 ≤ cg → 0 ≤ r → r ≤ 1 →
      ‖T‖ ≤ m / 2 → ‖D‖ ≤ m →
      (∀ j : Fin 3, ‖C j‖ ≤ m) →
      (∀ j : Fin 3, ‖N j‖ ≤ cn) →
      (∀ j : Fin 3, ‖J j‖ ≤ cm) → |r * f| ≤ cg →
      (r ^ 2 • E =
        (r ^ 2 • T).comp (J i)
          + (∑ j : Fin 3, (C j).comp (r ^ 2 • N j))
          + (∑ j : Fin 3, D.comp ((J j).comp (r ^ 3 • N j)))
          + (∑ j : Fin 3, (r ^ 2 • T).comp ((J j).comp (r ^ 2 • N j)))
          + f • (r ^ 3 • T)) →
      ‖E‖ ≤ 1 + (m / 2) * cm + 3 * m * cn + 3 * m * cm * cn
        + 3 * (m / 2) * cm * cn + cg * (m / 2) := by
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI jacobiOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  intro T D E C N J i m cn cm cg r f hr hm hcn hcm hcg hr0 hr1 hT hD hC hN hJ hrf hEq
  have hOrdered :
      E = T.comp (J i) + (∑ j : Fin 3, (C j).comp (N j))
        + r • (∑ j : Fin 3, D.comp ((J j).comp (N j)))
        + (r ^ 2) • (∑ j : Fin 3, T.comp ((J j).comp (N j)))
        + (r * f) • T := by
    apply eq_ordered_five_terms_of_sq_smul_eq_sobolev T D E C N J i r f hr
    exact hEq
  exact norm_le_of_eq_ordered_five_terms_sobolev T D E C N J i m cn cm cg r f
    hm hcn hcm hcg hr0 hr1 hT hD hC hN hJ hrf hOrdered

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
