import Calderon.ReferenceCurvature
import Calderon.SphereRotationCore
import Calderon.ProfileCovariantApplications

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.CurvatureRotation
open RadiusProfile ConformalDepth MetricOperator SphereHarmonic AngularPolynomial MvPolynomial

def coordinateCurvatureAction (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (x v w : R3) : R3 →L[ℝ] R3 :=
  (fderiv ℝ Γ x v) w - (fderiv ℝ Γ x w) v +
    (Γ x v).comp (Γ x w) - (Γ x w).comp (Γ x v)

lemma coordinateCurvatureAction_apply (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (x v w Z : R3) : coordinateCurvatureAction Γ x v w Z =
      (fderiv ℝ Γ x v) w Z - (fderiv ℝ Γ x w) v Z +
      Γ x v (Γ x w Z) - Γ x w (Γ x v Z) := by
  simp [coordinateCurvatureAction]

lemma coordinateCurvatureAction_jacobi (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (x v X : R3) : coordinateCurvatureAction Γ x X v v =
      CoordinateCurvature.curvatureOperator Γ x v X := by
  simp [coordinateCurvatureAction_apply, CoordinateCurvature.curvatureOperator_apply]

lemma norm_coordinateCurvatureAction_le (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (x v w : R3) : ‖coordinateCurvatureAction Γ x v w‖ ≤
      2 * (‖fderiv ℝ Γ x‖ + ‖Γ x‖^2) * ‖v‖ * ‖w‖ := by
  have hd1 := ((fderiv ℝ Γ x v).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right ((fderiv ℝ Γ x).le_opNorm v) (norm_nonneg w))
  have hd2 := ((fderiv ℝ Γ x w).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((fderiv ℝ Γ x).le_opNorm w) (norm_nonneg v))
  have hg1 := ((Γ x v).opNorm_comp_le (Γ x w)).trans
    (mul_le_mul ((Γ x).le_opNorm v) ((Γ x).le_opNorm w) (norm_nonneg _) (by positivity))
  have hg2 := ((Γ x w).opNorm_comp_le (Γ x v)).trans
    (mul_le_mul ((Γ x).le_opNorm w) ((Γ x).le_opNorm v) (norm_nonneg _) (by positivity))
  have ht1 := norm_sub_le ((fderiv ℝ Γ x v) w) ((fderiv ℝ Γ x w) v)
  have ht2 := norm_add_le ((fderiv ℝ Γ x v) w - (fderiv ℝ Γ x w) v)
    ((Γ x v).comp (Γ x w))
  have ht3 := norm_sub_le
    ((fderiv ℝ Γ x v) w - (fderiv ℝ Γ x w) v + (Γ x v).comp (Γ x w))
    ((Γ x w).comp (Γ x v))
  unfold coordinateCurvatureAction
  nlinarith

def referenceCurvatureAction (g : MatrixField) (L lam : ℝ) (x v w : R3) : R3 →L[ℝ] R3 :=
  coordinateCurvatureAction (fun y => referenceConnectionFamily g L (lam,y)) x v w

theorem exists_referenceCurvatureAction_uniform_norm_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ v w : R3,
      ‖referenceCurvatureAction g L lam x v w‖ ≤ C * ‖v‖ * ‖w‖ := by
  obtain ⟨C,D,hC,hD,hbounds⟩ := exists_referenceConnection_uniform_bounds g hg L K hK
  refine ⟨2*(D+C^2),by positivity,?_⟩
  intro lam hlam x hx v w
  obtain ⟨hG,hDG⟩ := hbounds lam hlam x hx
  have hsq : ‖referenceConnectionFamily g L (lam,x)‖^2 ≤ C^2 :=
    (sq_le_sq₀ (norm_nonneg _) hC.le).2 hG
  exact (norm_coordinateCurvatureAction_le _ x v w).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v)) (norm_nonneg w))

def referenceCurvatureRotationCoefficient (g : MatrixField) (L lam : ℝ)
    (x : R3) (e : Fin 3 → R3) (a b i j : Fin 3) : ℝ :=
  ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x
    (referenceCurvatureAction g L lam x (e a) (e b) (e j)), e i⟫_ℝ

theorem exists_referenceCurvatureRotationCoefficient_uniform_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ a b i j, |referenceCurvatureRotationCoefficient g L lam x e a b i j| ≤ C := by
  obtain ⟨R,hR,hcurv⟩ := exists_referenceCurvatureAction_uniform_norm_bound g hg L K hK
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (contDiff_referenceMetricOperator_joint g hg L).continuous.continuousOn
  obtain ⟨c,hc,hmetric⟩ := exists_referenceMetric_uniform_quadratic_lower_bound_on_compact g hg L hL K hK
  let D := Real.sqrt (1/c)
  let M' := max M 0+1
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hM' : 0 < M' := by dsimp [M']; positivity
  refine ⟨M'*R*D^4+1,by positivity,?_⟩
  intro lam hlam x hx e he a b i j
  have hn : ∀ i, ‖e i‖ ≤ D := fun i =>
    norm_le_sqrt_inv_of_quadratic_unit _ c hc (hmetric lam x hx) (e i)
      (IsMetricOrthonormalFrame_unit _ _ he i).le
  let T := referenceCurvatureAction g L lam x (e a) (e b)
  have hT : ‖T‖ ≤ R*D*D := (hcurv lam hlam x hx (e a) (e b)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (hn a) hR.le) (hn b) (norm_nonneg _) (by positivity))
  have hMnorm : ‖metricOperatorField (referenceMetric (dilatedMetric g lam) L) x‖ ≤ M' :=
    (hM (lam,x) ⟨hlam,hx⟩).trans (by dsimp [M']; linarith [le_max_left M 0])
  have htj : ‖T (e j)‖ ≤ R*D*D*D := (T.le_opNorm (e j)).trans
    (mul_le_mul hT (hn j) (norm_nonneg _) (by positivity))
  have hMtj : ‖metricOperatorField (referenceMetric (dilatedMetric g lam) L) x (T (e j))‖ ≤
      M'*(R*D*D*D) :=
    ((metricOperatorField (referenceMetric (dilatedMetric g lam) L) x).le_opNorm _).trans
      (mul_le_mul hMnorm htj (norm_nonneg _) hM'.le)
  have hi := (abs_real_inner_le_norm _ (e i)).trans
    (mul_le_mul hMtj (hn i) (norm_nonneg _) (by positivity))
  change |⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x (T (e j)),e i⟫_ℝ| ≤ _
  nlinarith [hi]

def referenceCurvatureRotationPolynomial (g : MatrixField) (L lam : ℝ) (x : R3)
    (e : Fin 3 → R3) (a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  polynomialRotationCombination (referenceCurvatureRotationCoefficient g L lam x e a b) p

theorem referenceCurvatureRotationPolynomial_harmonicHomogeneous
    (g : MatrixField) (L lam : ℝ) (x : R3) (e : Fin 3 → R3) (a b : Fin 3)
    (k : ℕ) (hk : 1 ≤ k) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    referenceCurvatureRotationPolynomial g L lam x e a b p ∈ harmonicHomogeneous k :=
  polynomialRotationCombination_harmonicHomogeneous k hk _ p hp

theorem exists_referenceCurvatureRotationPolynomial_uniform_sphere_norm_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ a b : Fin 3, ∀ k : ℕ, 1 ≤ k → ∀ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous k →
      ‖polynomialSphereL2 (referenceCurvatureRotationPolynomial g L lam x e a b p)‖ ≤
        C * (k : ℝ) * ‖polynomialSphereL2 p‖ := by
  obtain ⟨A,hA,hcoef⟩ := exists_referenceCurvatureRotationCoefficient_uniform_bound g hg L hL K hK
  refine ⟨18*A,by positivity,?_⟩
  intro hF lam hlam x hx e he a b k hk p hp
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
      |referenceCurvatureRotationCoefficient g L lam x e a b i j|) ≤ 9*A := by
    calc
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, A := by
        apply Finset.sum_le_sum; intro i hi
        apply Finset.sum_le_sum; intro j hj
        exact hcoef lam hlam x hx e he a b i j
      _ = _ := by simp; ring
  have ht := polynomialRotationCombination_sphere_norm_le hF k hk
    (referenceCurvatureRotationCoefficient g L lam x e a b) p hp
  change ‖polynomialSphereL2 (referenceCurvatureRotationPolynomial g L lam x e a b p)‖ ≤ _ at ht
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2*(k : ℝ))) (norm_nonneg (polynomialSphereL2 p))
  exact ht.trans (by convert hm using 1 <;> ring)

theorem exists_referenceCurvatureRotationPolynomial_uniform_degree_sphere_norm_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ a b : Fin 3, ∀ k : ℕ, 1 ≤ k → ∀ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous k →
      ‖polynomialSphereL2 ((k : ℝ) • referenceCurvatureRotationPolynomial g L lam x e a b p)‖ ≤
        C * (k : ℝ)^2 * ‖polynomialSphereL2 p‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_referenceCurvatureRotationPolynomial_uniform_sphere_norm_bound g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro hF lam hlam x hx e he a b k hk p hp
  simp only [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h := mul_le_mul_of_nonneg_left (hbound hF lam hlam x hx e he a b k hk p hp)
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  convert h using 1 <;> ring

end OAI.AnisotropicCalderon.CurvatureRotation
