import Calderon.CoordinateConnection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

set_option maxSynthPendingDepth 10
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def adjointMap : (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] E →L[ℝ] E).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def koszulLinearMap :
    (E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ _ + (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearEquiv.toContinuousLinearMap -
    ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)) adjointMap).comp
      (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearEquiv.toContinuousLinearMap

theorem koszulLinearMap_apply (D : E →L[ℝ] E →L[ℝ] E) (X Y : E) :
    koszulLinearMap D X Y = D X Y+D Y X-(D.flip X).adjoint Y := by
  simp [koszulLinearMap, adjointMap]

noncomputable def coordinateConnectionLinearMap (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] E :=
  (1/2:ℝ) • (((ContinuousLinearMap.compL ℝ E E E) Q).comp (koszulLinearMap D))

theorem coordinateConnectionLinearMap_apply (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (X Y : E) :
    coordinateConnectionLinearMap Q D X Y =
      (1/2:ℝ) • Q (D X Y+D Y X-(D.flip X).adjoint Y) := by
  simp [coordinateConnectionLinearMap, koszulLinearMap_apply]

theorem toDual_symm_koszulFunctional (D : E →L[ℝ] E →L[ℝ] E) (X Y : E) :
    (InnerProductSpace.toDual ℝ E).symm (koszulFunctional D X Y) =
      D X Y+D Y X-(D.flip X).adjoint Y := by
  have h : InnerProductSpace.toDual ℝ E (D X Y+D Y X-(D.flip X).adjoint Y) =
      koszulFunctional D X Y := by
    ext Z
    simp [koszulFunctional_apply, inner_add_left, inner_sub_left, inner_add_right,
      inner_sub_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  rw [← h]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _

theorem coordinateConnectionLinearMap_eq (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (X Y : E) :
    coordinateConnectionLinearMap Q D X Y = coordinateConnection Q D X Y := by
  simp only [coordinateConnectionLinearMap_apply, coordinateConnection,
    toDual_symm_koszulFunctional]

noncomputable def coordinateConnectionField (Q M : E → E →L[ℝ] E) :
    E → E →L[ℝ] E →L[ℝ] E :=
  fun x => coordinateConnectionLinearMap (Q x) (fderiv ℝ M x)

theorem coordinateConnectionField_apply (Q M : E → E →L[ℝ] E) (x X Y : E) :
    coordinateConnectionField Q M x X Y =
      coordinateConnection (Q x) (fderiv ℝ M x) X Y :=
  coordinateConnectionLinearMap_eq _ _ _ _

theorem contDiff_coordinateConnectionField {n m : ℕ∞ω} (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ n Q) (hM : ContDiff ℝ m M) (hnm : n+1 ≤ m) :
    ContDiff ℝ n (coordinateConnectionField Q M) := by
  have hD := koszulLinearMap.contDiff.comp (hM.fderiv_right hnm)
  have hComp := ((ContinuousLinearMap.compL ℝ E E E).contDiff.comp hQ).clm_comp hD
  exact hComp.const_smul (1/2:ℝ)

theorem contDiff_coordinateConnectionField_infty (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (coordinateConnectionField Q M) :=
  contDiff_coordinateConnectionField Q M hQ hM (by simp)

theorem hasFDerivAt_coordinateConnectionField (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (x : E) :
    HasFDerivAt (coordinateConnectionField Q M)
      (fderiv ℝ (coordinateConnectionField Q M) x) x :=
  ((contDiff_infty_iff_fderiv.mp
    (contDiff_coordinateConnectionField_infty Q M hQ hM)).1 x).hasFDerivAt

theorem contDiff_fderiv_coordinateConnectionField (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (fderiv ℝ (coordinateConnectionField Q M)) :=
  (contDiff_infty_iff_fderiv.mp
    (contDiff_coordinateConnectionField_infty Q M hQ hM)).2

theorem exists_connection_bounds_on_compact (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (K : Set E) (hK : IsCompact K) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ x ∈ K,
      ‖coordinateConnectionField Q M x‖ ≤ C ∧
      ‖fderiv ℝ (coordinateConnectionField Q M) x‖ ≤ D := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (contDiff_coordinateConnectionField_infty Q M hQ hM).continuous.continuousOn
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (contDiff_fderiv_coordinateConnectionField Q M hQ hM).continuous.continuousOn
  exact ⟨max C 0,max D 0,le_max_right _ _,le_max_right _ _,
    fun x hx => ⟨(hC x hx).trans (le_max_left _ _),
      (hD x hx).trans (le_max_left _ _)⟩⟩

private theorem norm_bilinear_apply_le (D : E →L[ℝ] E →L[ℝ] E) (X Y : E) :
    ‖D X Y‖ ≤ ‖D‖*‖X‖*‖Y‖ :=
  ((D X).le_opNorm Y).trans
    (mul_le_mul_of_nonneg_right (D.le_opNorm X) (norm_nonneg Y))

theorem norm_koszulLinearMap_apply_le (D : E →L[ℝ] E →L[ℝ] E) (X Y : E) :
    ‖koszulLinearMap D X Y‖ ≤ 3*‖D‖*‖X‖*‖Y‖ := by
  rw [koszulLinearMap_apply]
  have hAdjNorm : ‖(D.flip X).adjoint‖ = ‖D.flip X‖ :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] E →L[ℝ] E).norm_map _
  have hFlipNorm : ‖D.flip‖ = ‖D‖ := (ContinuousLinearMap.flipₗᵢ ℝ E E E).norm_map D
  have hAdj := (D.flip X).adjoint.le_opNorm Y
  rw [hAdjNorm] at hAdj
  have hAdj := hAdj.trans
    (mul_le_mul_of_nonneg_right (D.flip.le_opNorm X) (norm_nonneg Y))
  rw [hFlipNorm] at hAdj
  have h1 := norm_bilinear_apply_le D X Y
  have h2 := norm_bilinear_apply_le D Y X
  have h3 := norm_add_le (D X Y) (D Y X)
  have h4 := norm_sub_le (D X Y+D Y X) ((D.flip X).adjoint Y)
  nlinarith

theorem norm_coordinateConnectionLinearMap_apply_le (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (X Y : E) :
    ‖coordinateConnectionLinearMap Q D X Y‖ ≤ (3/2)*‖Q‖*‖D‖*‖X‖*‖Y‖ := by
  change ‖(1/2:ℝ) • Q (koszulLinearMap D X Y)‖ ≤ _
  have hQ := Q.le_opNorm (koszulLinearMap D X Y)
  have hD := norm_koszulLinearMap_apply_le D X Y
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  nlinarith [mul_le_mul_of_nonneg_left hD (norm_nonneg Q)]

theorem norm_coordinateConnectionLinearMap_le (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) :
    ‖coordinateConnectionLinearMap Q D‖ ≤ (3/2)*‖Q‖*‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro X
    apply ContinuousLinearMap.opNorm_le_bound
    · positivity
    · exact norm_coordinateConnectionLinearMap_apply_le Q D X

#print axioms coordinateConnectionLinearMap_eq
#print axioms contDiff_coordinateConnectionField_infty
#print axioms norm_coordinateConnectionLinearMap_le
#print axioms hasFDerivAt_coordinateConnectionField
#print axioms exists_connection_bounds_on_compact
end OAI.AnisotropicCalderon.ConnectionError
