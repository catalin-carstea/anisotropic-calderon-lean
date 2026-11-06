import Calderon.JacobiCurvature
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

set_option maxSynthPendingDepth 10

open Set
namespace OAI.AnisotropicCalderon.CoordinateCurvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def curvatureOperator (Γ : E → E →L[ℝ] E →L[ℝ] E) (x v : E) :
    E →L[ℝ] E :=
  ((fderiv ℝ Γ x).flip v).flip v - ((fderiv ℝ Γ x) v).flip v +
    (Γ x).flip (Γ x v v) - (Γ x v).comp ((Γ x).flip v)

theorem curvatureOperator_apply (Γ : E → E →L[ℝ] E →L[ℝ] E) (x v X : E) :
    curvatureOperator Γ x v X = (fderiv ℝ Γ x X) v v -
      (fderiv ℝ Γ x v) X v + Γ x X (Γ x v v) - Γ x v (Γ x X v) := by
  simp [curvatureOperator]

theorem curvatureOperator_of_hasFDerivAt (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (x v : E) (B : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (hΓ : HasFDerivAt Γ B x) :
    curvatureOperator Γ x v = (B.flip v).flip v - (B v).flip v +
      (Γ x).flip (Γ x v v) - (Γ x v).comp ((Γ x).flip v) := by
  unfold curvatureOperator
  rw [hΓ.fderiv]

private theorem norm_bilinear_apply_le (B : E →L[ℝ] E →L[ℝ] E) (X Y : E) :
    ‖B X Y‖ ≤ ‖B‖*‖X‖*‖Y‖ := by
  exact ((B X).le_opNorm Y).trans
    (mul_le_mul_of_nonneg_right (B.le_opNorm X) (norm_nonneg Y))

private theorem norm_trilinear_apply_le (B : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (X Y Z : E) : ‖B X Y Z‖ ≤ ‖B‖*‖X‖*‖Y‖*‖Z‖ := by
  exact (norm_bilinear_apply_le (B X) Y Z).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (B.le_opNorm X) (norm_nonneg Y)) (norm_nonneg Z))

theorem norm_curvatureOperator_apply_le (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (x v X : E) : ‖curvatureOperator Γ x v X‖ ≤
      (2*(‖fderiv ℝ Γ x‖+‖Γ x‖^2)*‖v‖^2)*‖X‖ := by
  rw [curvatureOperator_apply]
  have hD1 := norm_trilinear_apply_le (fderiv ℝ Γ x) X v v
  have hD2 := norm_trilinear_apply_le (fderiv ℝ Γ x) v X v
  have hG1 := (norm_bilinear_apply_le (Γ x) X (Γ x v v)).trans
    (mul_le_mul_of_nonneg_left (norm_bilinear_apply_le (Γ x) v v)
      (mul_nonneg (norm_nonneg (Γ x)) (norm_nonneg X)))
  have hG2 := (norm_bilinear_apply_le (Γ x) v (Γ x X v)).trans
    (mul_le_mul_of_nonneg_left (norm_bilinear_apply_le (Γ x) X v)
      (mul_nonneg (norm_nonneg (Γ x)) (norm_nonneg v)))
  have h1 := norm_sub_le ((fderiv ℝ Γ x X) v v) ((fderiv ℝ Γ x v) X v)
  have h2 := norm_add_le ((fderiv ℝ Γ x X) v v-(fderiv ℝ Γ x v) X v)
    (Γ x X (Γ x v v))
  have h3 := norm_sub_le
    ((fderiv ℝ Γ x X) v v-(fderiv ℝ Γ x v) X v+Γ x X (Γ x v v))
    (Γ x v (Γ x X v))
  nlinarith

theorem norm_curvatureOperator_le (Γ : E → E →L[ℝ] E →L[ℝ] E) (x v : E) :
    ‖curvatureOperator Γ x v‖ ≤ 2*(‖fderiv ℝ Γ x‖+‖Γ x‖^2)*‖v‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · exact norm_curvatureOperator_apply_le Γ x v

theorem norm_curvatureOperator_le_of_bounds (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (x v : E) (C D V : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hΓ : ‖Γ x‖ ≤ C) (hΓ' : ‖fderiv ℝ Γ x‖ ≤ D) (hv : ‖v‖ ≤ V) :
    ‖curvatureOperator Γ x v‖ ≤ 2*(D+C^2)*V^2 := by
  have hΓ2 : ‖Γ x‖^2 ≤ C^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg (Γ x)) hΓ
  have hv2 : ‖v‖^2 ≤ V^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg v) hv
  refine (norm_curvatureOperator_le Γ x v).trans ?_
  exact mul_le_mul (by linarith) hv2 (sq_nonneg _) (by positivity)

theorem continuousOn_curvatureOperator
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (q v : ℝ → E) (S : Set ℝ)
    (hΓc : ContinuousOn (fun s => Γ (q s)) S)
    (hΓ'c : ContinuousOn (fun s => fderiv ℝ Γ (q s)) S)
    (hvc : ContinuousOn v S) :
    ContinuousOn (fun s => curvatureOperator Γ (q s) (v s)) S := by
  have hflipΓ : ContinuousOn (fun s => (Γ (q s)).flip) S :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.comp_continuousOn hΓc
  have hflipD : ContinuousOn (fun s => (fderiv ℝ Γ (q s)).flip) S :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] E)).continuous.comp_continuousOn hΓ'c
  have hflipDv : ContinuousOn (fun s => ((fderiv ℝ Γ (q s)).flip (v s)).flip) S :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.comp_continuousOn (hflipD.clm_apply hvc)
  have hflipDAtv : ContinuousOn (fun s => ((fderiv ℝ Γ (q s)) (v s)).flip) S :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.comp_continuousOn (hΓ'c.clm_apply hvc)
  exact (((hflipDv.clm_apply hvc).sub (hflipDAtv.clm_apply hvc)).add
    (hflipΓ.clm_apply ((hΓc.clm_apply hvc).clm_apply hvc))).sub
    ((hΓc.clm_apply hvc).clm_comp (hflipΓ.clm_apply hvc))

theorem abs_indexIntegral_coordinate_sub_norm_sq_le
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (q v j j' : ℝ → E) (r C D V : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hΓ : ∀ s ∈ Icc 0 1, ‖Γ (q s)‖ ≤ C)
    (hΓ' : ∀ s ∈ Icc 0 1, ‖fderiv ℝ Γ (q s)‖ ≤ D)
    (hv : ∀ s ∈ Icc 0 1, ‖v s‖ ≤ V)
    (hRC : ContinuousOn (fun s => curvatureOperator Γ (q s) (v s)) (Icc 0 1))
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1,
      HasDerivAt j' (-(r^2) • curvatureOperator Γ (q s) (v s) (j s)) s)
    (hsmall : (2*(D+C^2)*V^2)*r^2 ≤ 1) :
    |JacobiIntegral.indexIntegral j j'
      (fun s => -(r^2) • curvatureOperator Γ (q s) (v s) (j s))-‖j 1-j 0‖^2| ≤
      2*(2*(D+C^2)*V^2)*r^2*(JacobiIntegral.endpointSize j)^2 := by
  apply JacobiIntegral.abs_indexIntegral_continuous_operator_sub_norm_sq_le
  · exact hj
  · exact hj'
  · exact hRC
  · positivity
  · exact hsmall
  · intro s hs
    exact norm_curvatureOperator_le_of_bounds Γ (q s) (v s) C D V hC hD hV
      (hΓ s hs) (hΓ' s hs) (hv s hs)

theorem abs_indexIntegral_continuous_coordinate_sub_norm_sq_le
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (q v j j' : ℝ → E) (r C D V : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hΓ : ∀ s ∈ Icc 0 1, ‖Γ (q s)‖ ≤ C)
    (hΓ' : ∀ s ∈ Icc 0 1, ‖fderiv ℝ Γ (q s)‖ ≤ D)
    (hv : ∀ s ∈ Icc 0 1, ‖v s‖ ≤ V)
    (hΓc : ContinuousOn (fun s => Γ (q s)) (Icc 0 1))
    (hΓ'c : ContinuousOn (fun s => fderiv ℝ Γ (q s)) (Icc 0 1))
    (hvc : ContinuousOn v (Icc 0 1))
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1,
      HasDerivAt j' (-(r^2) • curvatureOperator Γ (q s) (v s) (j s)) s)
    (hsmall : (2*(D+C^2)*V^2)*r^2 ≤ 1) :
    |JacobiIntegral.indexIntegral j j'
      (fun s => -(r^2) • curvatureOperator Γ (q s) (v s) (j s))-‖j 1-j 0‖^2| ≤
      2*(2*(D+C^2)*V^2)*r^2*(JacobiIntegral.endpointSize j)^2 := by
  exact abs_indexIntegral_coordinate_sub_norm_sq_le Γ q v j j' r C D V hC hD hV
    hΓ hΓ' hv (continuousOn_curvatureOperator Γ q v (Icc 0 1) hΓc hΓ'c hvc)
    hj hj' hsmall

noncomputable def transportedCurvatureOperator
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (x v : E) (S T : E →L[ℝ] E) : E →L[ℝ] E :=
  (S.comp (curvatureOperator Γ x v)).comp T

theorem norm_transportedCurvatureOperator_le_of_bounds
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (x v : E) (S T : E →L[ℝ] E)
    (A B C D V : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hS : ‖S‖ ≤ A) (hT : ‖T‖ ≤ B) (hΓ : ‖Γ x‖ ≤ C)
    (hΓ' : ‖fderiv ℝ Γ x‖ ≤ D) (hv : ‖v‖ ≤ V) :
    ‖transportedCurvatureOperator Γ x v S T‖ ≤ (A*(2*(D+C^2)*V^2))*B := by
  have hR := norm_curvatureOperator_le_of_bounds Γ x v C D V hC hD hV hΓ hΓ' hv
  have hSR := (S.opNorm_comp_le (curvatureOperator Γ x v)).trans
    (mul_le_mul hS hR (norm_nonneg _) hA)
  exact ((S.comp (curvatureOperator Γ x v)).opNorm_comp_le T).trans
    (mul_le_mul hSR hT (norm_nonneg _) (by positivity))

theorem continuousOn_transportedCurvatureOperator
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (q v : ℝ → E) (S T : ℝ → E →L[ℝ] E)
    (I : Set ℝ) (hΓc : ContinuousOn (fun s => Γ (q s)) I)
    (hΓ'c : ContinuousOn (fun s => fderiv ℝ Γ (q s)) I) (hvc : ContinuousOn v I)
    (hSc : ContinuousOn S I) (hTc : ContinuousOn T I) :
    ContinuousOn (fun s => transportedCurvatureOperator Γ (q s) (v s) (S s) (T s)) I :=
  (hSc.clm_comp (continuousOn_curvatureOperator Γ q v I hΓc hΓ'c hvc)).clm_comp hTc

theorem abs_indexIntegral_transported_coordinate_sub_norm_sq_le
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (q v j j' : ℝ → E)
    (S T : ℝ → E →L[ℝ] E) (r A B C D V : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hS : ∀ s ∈ Icc 0 1, ‖S s‖ ≤ A) (hT : ∀ s ∈ Icc 0 1, ‖T s‖ ≤ B)
    (hΓ : ∀ s ∈ Icc 0 1, ‖Γ (q s)‖ ≤ C)
    (hΓ' : ∀ s ∈ Icc 0 1, ‖fderiv ℝ Γ (q s)‖ ≤ D)
    (hv : ∀ s ∈ Icc 0 1, ‖v s‖ ≤ V)
    (hΓc : ContinuousOn (fun s => Γ (q s)) (Icc 0 1))
    (hΓ'c : ContinuousOn (fun s => fderiv ℝ Γ (q s)) (Icc 0 1))
    (hvc : ContinuousOn v (Icc 0 1))
    (hSc : ContinuousOn S (Icc 0 1)) (hTc : ContinuousOn T (Icc 0 1))
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j'
      (-(r^2) • transportedCurvatureOperator Γ (q s) (v s) (S s) (T s) (j s)) s)
    (hsmall : ((A*(2*(D+C^2)*V^2))*B)*r^2 ≤ 1) :
    |JacobiIntegral.indexIntegral j j'
      (fun s => -(r^2) • transportedCurvatureOperator Γ (q s) (v s) (S s) (T s) (j s))-
      ‖j 1-j 0‖^2| ≤
      2*((A*(2*(D+C^2)*V^2))*B)*r^2*(JacobiIntegral.endpointSize j)^2 := by
  apply JacobiIntegral.abs_indexIntegral_continuous_operator_sub_norm_sq_le
  · exact hj
  · exact hj'
  · exact continuousOn_transportedCurvatureOperator Γ q v S T (Icc 0 1)
      hΓc hΓ'c hvc hSc hTc
  · positivity
  · exact hsmall
  · intro s hs
    exact norm_transportedCurvatureOperator_le_of_bounds Γ (q s) (v s) (S s) (T s)
      A B C D V hA hB hC hD hV (hS s hs) (hT s hs) (hΓ s hs) (hΓ' s hs) (hv s hs)

#print axioms abs_indexIntegral_transported_coordinate_sub_norm_sq_le

#print axioms abs_indexIntegral_continuous_coordinate_sub_norm_sq_le

#print axioms norm_curvatureOperator_le
#print axioms abs_indexIntegral_coordinate_sub_norm_sq_le
end OAI.AnisotropicCalderon.CoordinateCurvature
