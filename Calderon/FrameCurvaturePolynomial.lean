import Calderon.HorizontalCurvature
import Calderon.GreenRadialTrace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.FrameCurvaturePolynomial
open RadiusProfile CurvatureSkew CurvatureRotation HorizontalCurvature ConformalDepth
  MetricOperator SphereHarmonic AngularPolynomial MvPolynomial

theorem metricFrame_linearIndependent (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : LinearIndependent ℝ e := by
  simp only [IsMetricOrthonormalFrame] at he
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (fun v : R3 => ⟪M v,e j⟫_ℝ) hc
  simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, map_zero,
    inner_zero_left, he] at h
  simpa using h

def metricFrameBasis (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) : Module.Basis (Fin 3) ℝ R3 :=
  basisOfLinearIndependentOfCardEqFinrank (metricFrame_linearIndependent M e he)
    (by simp [R3])

lemma metricFrameBasis_apply (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (i : Fin 3) : metricFrameBasis M e he i = e i := by
  simp [metricFrameBasis]

lemma metricFrameBasis_repr (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (v : R3) (i : Fin 3) :
    (metricFrameBasis M e he).repr v i = ⟪M v,e i⟫_ℝ := by
  simp only [IsMetricOrthonormalFrame] at he
  have hb : (metricFrameBasis M e he : Fin 3 → R3) = e :=
    funext (fun j => metricFrameBasis_apply M e he j)
  have hv : ∑ j : Fin 3, (metricFrameBasis M e he).repr v j • e j = v := by
    simpa only [hb] using (metricFrameBasis M e he).sum_repr v
  have h := congrArg (fun w : R3 => ⟪M w,e i⟫_ℝ) hv
  simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, he] at h
  simpa using h

theorem metricFrame_sum_coordinates (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (v : R3) :
    ∑ i : Fin 3, ⟪M v,e i⟫_ℝ • e i = v := by
  have h := (metricFrameBasis M e he).sum_repr v
  simpa only [metricFrameBasis_apply, metricFrameBasis_repr] using h

def metricFrameCoordinates (M : R3 →L[ℝ] R3) (e : Fin 3 → R3) :
    R3 →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun i => (InnerProductSpace.toDual ℝ R3 (e i)).comp M

lemma metricFrameCoordinates_apply (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (v : R3) (i : Fin 3) : metricFrameCoordinates M e v i = ⟪M v,e i⟫_ℝ := by
  change ⟪e i,M v⟫_ℝ = ⟪M v,e i⟫_ℝ
  exact real_inner_comm _ _

def metricFramePolynomial (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (p : MvPolynomial (Fin 3) ℝ) : R3 → ℝ := fun v => eval (metricFrameCoordinates M e v) p

lemma contDiff_metricFramePolynomial (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (p : MvPolynomial (Fin 3) ℝ) : ContDiff ℝ ∞ (metricFramePolynomial M e p) := by
  unfold metricFramePolynomial
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [metricFramePolynomial, eval_C] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => c))
  | add p q hp hq => simpa only [metricFramePolynomial, map_add] using hp.add hq
  | mul_X p i hp =>
    have hi : ContDiff ℝ ∞ (fun v : R3 => metricFrameCoordinates M e v i) :=
      (ContinuousLinearMap.proj i).contDiff.comp (metricFrameCoordinates M e).contDiff
    simpa only [metricFramePolynomial, map_mul, eval_X] using hp.mul hi

lemma fderiv_metricFramePolynomial_apply (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (p : MvPolynomial (Fin 3) ℝ) (v w : R3) :
    fderiv ℝ (metricFramePolynomial M e p) v w =
      ∑ i : Fin 3, metricFrameCoordinates M e w i *
        eval (metricFrameCoordinates M e v) (pderiv i p) := by
  have h := (GreenRadialTrace.hasFDerivAt_eval p (metricFrameCoordinates M e v)).comp v
    (metricFrameCoordinates M e).hasFDerivAt
  change HasFDerivAt (metricFramePolynomial M e p) _ v at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply, GreenRadialTrace.polynomialFDeriv_apply]

lemma metricFrameCoordinates_operator_apply (M A : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (v : R3) (i : Fin 3) :
    metricFrameCoordinates M e (A v) i =
      ∑ j : Fin 3, ⟪M (A (e j)),e i⟫_ℝ * metricFrameCoordinates M e v j := by
  rw [metricFrameCoordinates_apply]
  nth_rw 1 [← metricFrame_sum_coordinates M e he v]
  simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, metricFrameCoordinates_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fderiv_metricFramePolynomial_operator_apply (M A : R3 →L[ℝ] R3)
    (e : Fin 3 → R3) (he : IsMetricOrthonormalFrame M e)
    (p : MvPolynomial (Fin 3) ℝ) (v : R3) :
    fderiv ℝ (metricFramePolynomial M e p) v (A v) =
      eval (metricFrameCoordinates M e v)
        (polynomialMatrixVectorField (fun i j => ⟪M (A (e j)),e i⟫_ℝ) p) := by
  rw [fderiv_metricFramePolynomial_apply]
  simp only [metricFrameCoordinates_operator_apply M A e he, Finset.sum_mul,
    polynomialMatrixVectorField, map_sum, map_mul, eval_C, eval_X]

def metricFrameAmbientPolynomial (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (p : MvPolynomial (Fin 3) ℝ) : R3 × R3 → ℝ := fun z => metricFramePolynomial M e p z.2

lemma contDiff_metricFrameAmbientPolynomial (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (p : MvPolynomial (Fin 3) ℝ) : ContDiff ℝ ∞ (metricFrameAmbientPolynomial M e p) :=
  (contDiff_metricFramePolynomial M e p).comp contDiff_snd

lemma fderiv_metricFrameAmbientPolynomial_apply (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (p : MvPolynomial (Fin 3) ℝ) (z a : R3 × R3) :
    fderiv ℝ (metricFrameAmbientPolynomial M e p) z a =
      fderiv ℝ (metricFramePolynomial M e p) z.2 a.2 := by
  have h := ((contDiff_metricFramePolynomial M e p).differentiable (by simp) z.2).hasFDerivAt.comp z
    (hasFDerivAt_snd (p := z))
  change HasFDerivAt (metricFrameAmbientPolynomial M e p) _ z at h
  rw [h.fderiv]
  rfl

theorem horizontalVectorField_metricFramePolynomial_commutator
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (hΓ : ContDiff ℝ ∞ Γ)
    (M : R3 →L[ℝ] R3) (e : Fin 3 → R3) (he : IsMetricOrthonormalFrame M e)
    (a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    vectorFieldDeriv (horizontalVectorField Γ (e a))
      (vectorFieldDeriv (horizontalVectorField Γ (e b)) (metricFrameAmbientPolynomial M e p)) (x,v) -
    vectorFieldDeriv (horizontalVectorField Γ (e b))
      (vectorFieldDeriv (horizontalVectorField Γ (e a)) (metricFrameAmbientPolynomial M e p)) (x,v) =
    eval (metricFrameCoordinates M e v)
      (-polynomialMatrixVectorField (fun i j =>
        ⟪M (coordinateCurvatureAction Γ x (e a) (e b) (e j)),e i⟫_ℝ) p) := by
  rw [horizontalVectorField_commutator Γ hΓ _ _ _ (contDiff_metricFrameAmbientPolynomial M e p),
    fderiv_metricFrameAmbientPolynomial_apply, map_neg,
    fderiv_metricFramePolynomial_operator_apply M _ e he, map_neg]

def referenceHorizontalCurvaturePolynomial (g : MatrixField) (L lam : ℝ) (x : R3)
    (e : Fin 3 → R3) (a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := -referenceCurvatureVectorFieldPolynomial g L lam x e a b p

theorem referenceHorizontalCurvaturePolynomial_eq_half_smul (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (e : Fin 3 → R3)
    (a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    referenceHorizontalCurvaturePolynomial g L lam x e a b p =
      (1 / 2 : ℝ) • referenceCurvatureRotationPolynomial g L lam x e a b p := by
  unfold referenceHorizontalCurvaturePolynomial
  rw [referenceCurvatureVectorFieldPolynomial_eq_neg_half_smul g hg]
  simp only [neg_smul, neg_neg]

theorem reference_horizontal_metricFramePolynomial_commutator (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x v : R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e)
    (a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    vectorFieldDeriv (horizontalVectorField (fun y => referenceConnectionFamily g L (lam,y)) (e a))
      (vectorFieldDeriv (horizontalVectorField (fun y => referenceConnectionFamily g L (lam,y)) (e b))
        (metricFrameAmbientPolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e p)) (x,v) -
    vectorFieldDeriv (horizontalVectorField (fun y => referenceConnectionFamily g L (lam,y)) (e b))
      (vectorFieldDeriv (horizontalVectorField (fun y => referenceConnectionFamily g L (lam,y)) (e a))
        (metricFrameAmbientPolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e p)) (x,v) =
    eval (metricFrameCoordinates (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e v)
      (referenceHorizontalCurvaturePolynomial g L lam x e a b p) := by
  have hpair : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  exact horizontalVectorField_metricFramePolynomial_commutator _
    ((contDiff_referenceConnectionFamily g hg L).comp hpair) _ e he a b p x v

theorem referenceHorizontalCurvaturePolynomial_harmonicHomogeneous (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (e : Fin 3 → R3)
    (a b : Fin 3) (k : ℕ) (hk : 1 ≤ k) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    referenceHorizontalCurvaturePolynomial g L lam x e a b p ∈ harmonicHomogeneous k := by
  rw [referenceHorizontalCurvaturePolynomial_eq_half_smul g hg]
  exact (harmonicHomogeneous k).smul_mem _
    (referenceCurvatureRotationPolynomial_harmonicHomogeneous g L lam x e a b k hk p hp)

theorem exists_referenceHorizontalCurvaturePolynomial_uniform_sphere_norm_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ a b : Fin 3, ∀ k : ℕ, 1 ≤ k → ∀ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous k →
      ‖polynomialSphereL2 (referenceHorizontalCurvaturePolynomial g L lam x e a b p)‖ ≤
        C * (k : ℝ) * ‖polynomialSphereL2 p‖ := by
  obtain ⟨B,hB,hbound⟩ := exists_referenceCurvatureRotationPolynomial_uniform_sphere_norm_bound g hg L hL K hK
  refine ⟨B/2,by positivity,?_⟩
  intro hF lam hlam x hx e he a b k hk p hp
  have hb := mul_le_mul_of_nonneg_left (hbound hF lam hlam x hx e he a b k hk p hp)
    (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [referenceHorizontalCurvaturePolynomial_eq_half_smul g hg, map_smul, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  convert hb using 1 <;> ring

theorem exists_referenceHorizontalCurvaturePolynomial_uniform_degree_sphere_norm_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ a b : Fin 3, ∀ k : ℕ, 1 ≤ k → ∀ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous k →
      ‖polynomialSphereL2 ((k : ℝ) • referenceHorizontalCurvaturePolynomial g L lam x e a b p)‖ ≤
        C * (k : ℝ)^2 * ‖polynomialSphereL2 p‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_referenceHorizontalCurvaturePolynomial_uniform_sphere_norm_bound g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro hF lam hlam x hx e he a b k hk p hp
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
  convert mul_le_mul_of_nonneg_left (hbound hF lam hlam x hx e he a b k hk p hp)
    (Nat.cast_nonneg k) using 1 <;> ring

end OAI.AnisotropicCalderon.FrameCurvaturePolynomial
