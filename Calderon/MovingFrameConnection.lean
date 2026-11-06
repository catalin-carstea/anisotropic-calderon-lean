import Calderon.SmoothMetricFrame
import Calderon.FrameCurvaturePolynomial

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.MovingFrameConnection
open PrincipalCommutator ConnectionError MetricOperator ConformalDepth RadiusProfile
  AngularPolynomial SphereHarmonic CurvatureRotation CurvatureSkew
  FrameCurvaturePolynomial SmoothMetricFrame MvPolynomial

def covariantFrameDerivative (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (x X : R3) (j : Fin 3) : R3 :=
  fderiv ℝ (fun y => e y j) x X + Γ x X (e x j)

def frameConnectionCoefficient (M : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (x X : R3) (i j : Fin 3) : ℝ :=
  ⟪M x (covariantFrameDerivative Γ e x X j),e x i⟫_ℝ

theorem covariantFrameDerivative_eq_sum (M : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (x X : R3) (he : IsMetricOrthonormalFrame (M x) (e x)) (j : Fin 3) :
    covariantFrameDerivative Γ e x X j =
      ∑ i : Fin 3, frameConnectionCoefficient M Γ e x X i j • e x i := by
  exact (metricFrame_sum_coordinates (M x) (e x) he _).symm

theorem frameConnectionCoefficient_skew (M : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (hM : ContDiff ℝ ∞ M) (hE : ∀ j, ContDiff ℝ ∞ (fun y => e y j))
    (hsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (he : ∀ y, IsMetricOrthonormalFrame (M y) (e y))
    (hcomp : ∀ y X U V, ⟪M y (Γ y X U),V⟫_ℝ + ⟪M y U,Γ y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ) (x X : R3) (i j : Fin 3) :
    frameConnectionCoefficient M Γ e x X i j =
      -frameConnectionCoefficient M Γ e x X j i := by
  have hg : (fun y => ⟪M y (e y j),e y i⟫_ℝ) =
      fun _ : R3 => if j = i then (1:ℝ) else 0 := by
    funext y
    exact he y j i
  have hd := directionalFDeriv_metric_pairing X M (fun y => e y j)
    (fun y => e y i) hM (hE j) (hE i) x
  rw [hg] at hd
  have hz : directionalFDeriv X (fun _ : R3 => if j = i then (1:ℝ) else 0) x = 0 := by
    by_cases h : j = i <;> simp [h, directionalFDeriv]
  rw [hz] at hd
  simp only [directionalFDeriv] at hd
  simp only [inner_add_left] at hd
  rw [← hcomp x X (e x j) (e x i)] at hd
  have hs1 := hsym x (e x j) (fderiv ℝ (fun y => e y i) x X)
  have hs2 := hsym x (e x j) (Γ x X (e x i))
  simp only [frameConnectionCoefficient, covariantFrameDerivative, map_add, inner_add_left]
  linarith

def movingFrameCoordinate (M : R3 → R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (i : Fin 3) (z : R3 × R3) : ℝ :=
  ⟪M z.1 z.2,e z.1 i⟫_ℝ

lemma contDiff_movingFrameCoordinate (M : R3 → R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ i, ContDiff ℝ ∞ (fun y => e y i)) (i : Fin 3) :
    ContDiff ℝ ∞ (movingFrameCoordinate M e i) :=
  ((hM.comp contDiff_fst).clm_apply contDiff_snd).inner ℝ ((hE i).comp contDiff_fst)

lemma fderiv_movingFrameCoordinate_apply (M : R3 → R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ i, ContDiff ℝ ∞ (fun y => e y i)) (i : Fin 3) (z a : R3 × R3) :
    fderiv ℝ (movingFrameCoordinate M e i) z a =
      ⟪fderiv ℝ M z.1 a.1 z.2 + M z.1 a.2,e z.1 i⟫_ℝ +
      ⟪M z.1 z.2,fderiv ℝ (fun y => e y i) z.1 a.1⟫_ℝ := by
  have hm := ((hM.differentiable (by simp) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (p := z)))
  have he := ((hE i).differentiable (by simp) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (p := z))
  have hp := (hm.clm_apply (hasFDerivAt_snd (p := z))).inner ℝ he
  change HasFDerivAt (movingFrameCoordinate M e i) _ z at hp
  rw [hp.fderiv]
  change ⟪M z.1 z.2,fderiv ℝ (fun y => e y i) z.1 a.1⟫_ℝ +
    ⟪M z.1 a.2 + fderiv ℝ M z.1 a.1 z.2,e z.1 i⟫_ℝ = _
  simp only [inner_add_left]
  ring

lemma fderiv_movingFrameCoordinate_horizontal (M : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (hM : ContDiff ℝ ∞ M) (hE : ∀ j, ContDiff ℝ ∞ (fun y => e y j))
    (hcomp : ∀ y X U V, ⟪M y (Γ y X U),V⟫_ℝ + ⟪M y U,Γ y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ) (x v X : R3) (i : Fin 3) :
    fderiv ℝ (movingFrameCoordinate M e i) (x,v) (X,-Γ x X v) =
      ⟪M x v,covariantFrameDerivative Γ e x X i⟫_ℝ := by
  rw [fderiv_movingFrameCoordinate_apply M e hM hE]
  simp only [map_neg, inner_add_left, inner_neg_left, covariantFrameDerivative,
    inner_add_right]
  rw [← hcomp x X v (e x i)]
  ring

lemma fderiv_movingFrameCoordinate_horizontal_eq_sum
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ j, ContDiff ℝ ∞ (fun y => e y j))
    (he : ∀ y, IsMetricOrthonormalFrame (M y) (e y))
    (hcomp : ∀ y X U V, ⟪M y (Γ y X U),V⟫_ℝ + ⟪M y U,Γ y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ) (x v X : R3) (i : Fin 3) :
    fderiv ℝ (movingFrameCoordinate M e i) (x,v) (X,-Γ x X v) =
      ∑ j : Fin 3, frameConnectionCoefficient M Γ e x X j i *
        movingFrameCoordinate M e j (x,v) := by
  rw [fderiv_movingFrameCoordinate_horizontal M Γ e hM hE hcomp,
    covariantFrameDerivative_eq_sum M Γ e x X (he x) i]
  simp only [inner_sum, real_inner_smul_right, movingFrameCoordinate]

lemma fderiv_movingFrameCoordinate_horizontal_eq_neg_sum
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ j, ContDiff ℝ ∞ (fun y => e y j))
    (hsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (he : ∀ y, IsMetricOrthonormalFrame (M y) (e y))
    (hcomp : ∀ y X U V, ⟪M y (Γ y X U),V⟫_ℝ + ⟪M y U,Γ y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ) (x v X : R3) (i : Fin 3) :
    fderiv ℝ (movingFrameCoordinate M e i) (x,v) (X,-Γ x X v) =
      -∑ j : Fin 3, frameConnectionCoefficient M Γ e x X i j *
        movingFrameCoordinate M e j (x,v) := by
  rw [fderiv_movingFrameCoordinate_horizontal_eq_sum M Γ e hM hE he hcomp]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [frameConnectionCoefficient_skew M Γ e hM hE hsym he hcomp x X j i, neg_mul]

def movingFramePolynomial (M : R3 → R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (p : MvPolynomial (Fin 3) ℝ) (z : R3 × R3) : ℝ :=
  eval (fun i => movingFrameCoordinate M e i z) p

lemma contDiff_movingFramePolynomial (M : R3 → R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ i, ContDiff ℝ ∞ (fun y => e y i)) (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (movingFramePolynomial M e p) := by
  unfold movingFramePolynomial
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [movingFramePolynomial, eval_C] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 × R3 => c))
  | add p q hp hq => simpa only [movingFramePolynomial, map_add] using hp.add hq
  | mul_X p i hp =>
      simpa only [map_mul, eval_X] using
        hp.mul (contDiff_movingFrameCoordinate M e hM hE i)

lemma fderiv_movingFramePolynomial_apply (M : R3 → R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (p : MvPolynomial (Fin 3) ℝ) (z a : R3 × R3) :
    fderiv ℝ (movingFramePolynomial M e p) z a =
      ∑ i : Fin 3, fderiv ℝ (movingFrameCoordinate M e i) z a *
        eval (fun j => movingFrameCoordinate M e j z) (pderiv i p) := by
  have hc := hasFDerivAt_pi.mpr (fun i =>
    ((contDiff_movingFrameCoordinate M e hM hE i).differentiable (by simp) z).hasFDerivAt)
  have hp := (GreenRadialTrace.hasFDerivAt_eval p
    (fun i => movingFrameCoordinate M e i z)).comp z hc
  change HasFDerivAt (movingFramePolynomial M e p) _ z at hp
  rw [hp.fderiv, ContinuousLinearMap.comp_apply, GreenRadialTrace.polynomialFDeriv_apply]
  rfl

lemma fderiv_movingFramePolynomial_horizontal (M : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (hM : ContDiff ℝ ∞ M) (hE : ∀ j, ContDiff ℝ ∞ (fun y => e y j))
    (hsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (he : ∀ y, IsMetricOrthonormalFrame (M y) (e y))
    (hcomp : ∀ y X U V, ⟪M y (Γ y X U),V⟫_ℝ + ⟪M y U,Γ y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ)
    (p : MvPolynomial (Fin 3) ℝ) (x v X : R3) :
    fderiv ℝ (movingFramePolynomial M e p) (x,v) (X,-Γ x X v) =
      eval (fun i => movingFrameCoordinate M e i (x,v))
        (-polynomialMatrixVectorField (frameConnectionCoefficient M Γ e x X) p) := by
  rw [fderiv_movingFramePolynomial_apply M e hM hE]
  simp only [fderiv_movingFrameCoordinate_horizontal_eq_neg_sum M Γ e hM hE
    hsym he hcomp, neg_mul, Finset.sum_mul, Finset.sum_neg_distrib,
    polynomialMatrixVectorField, map_neg, map_sum, map_mul, eval_C, eval_X]

lemma fderiv_movingFramePolynomial_horizontal_rotation (M : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (hM : ContDiff ℝ ∞ M) (hE : ∀ j, ContDiff ℝ ∞ (fun y => e y j))
    (hsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (he : ∀ y, IsMetricOrthonormalFrame (M y) (e y))
    (hcomp : ∀ y X U V, ⟪M y (Γ y X U),V⟫_ℝ + ⟪M y U,Γ y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ)
    (p : MvPolynomial (Fin 3) ℝ) (x v X : R3) :
    fderiv ℝ (movingFramePolynomial M e p) (x,v) (X,-Γ x X v) =
      eval (fun i => movingFrameCoordinate M e i (x,v))
        ((1/2:ℝ) • polynomialRotationCombination (frameConnectionCoefficient M Γ e x X) p) := by
  rw [fderiv_movingFramePolynomial_horizontal M Γ e hM hE hsym he hcomp,
    polynomialMatrixVectorField_eq_neg_half_smul _
      (fun i j => frameConnectionCoefficient_skew M Γ e hM hE hsym he hcomp x X i j)]
  simp

def referenceFrameConnectionCoefficient (g : MatrixField) (L lam : ℝ)
    (x X : R3) : Fin 3 → Fin 3 → ℝ :=
  frameConnectionCoefficient (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
    (fun y => referenceConnectionFamily g L (lam,y))
    (fun y => referenceMetricGramFrame g L (lam,y)) x X

theorem referenceFrameConnectionCoefficient_skew (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x X : R3) (i j : Fin 3) :
    referenceFrameConnectionCoefficient g L lam x X i j =
      -referenceFrameConnectionCoefficient g L lam x X j i := by
  exact frameConnectionCoefficient_skew _ _ _
    ((contDiff_referenceMetricOperator_joint g hg L).comp (contDiff_const.prodMk contDiff_id))
    (fun a => contDiff_referenceMetricGramFrame_slice g hg L lam a)
    (fun y U V => referenceMetricOperator_symmetric g hg L lam y U V)
    (fun y => referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,y))
    (fun y Y U V => referenceConnectionFamily_metric_compatible g hg L lam y Y U V)
    x X i j

def referenceMovingFramePolynomial (g : MatrixField) (L lam : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) : R3 × R3 → ℝ :=
  movingFramePolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
    (fun y => referenceMetricGramFrame g L (lam,y)) p

theorem contDiff_referenceMovingFramePolynomial (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (referenceMovingFramePolynomial g L lam p) :=
  contDiff_movingFramePolynomial _ _
    ((contDiff_referenceMetricOperator_joint g hg L).comp (contDiff_const.prodMk contDiff_id))
    (fun a => contDiff_referenceMetricGramFrame_slice g hg L lam a) p

def referenceFrameAngularPolynomial (g : MatrixField) (L lam : ℝ)
    (x X : R3) (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  -polynomialMatrixVectorField (referenceFrameConnectionCoefficient g L lam x X) p

theorem referenceFrameAngularPolynomial_eq_half_smul (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x X : R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    referenceFrameAngularPolynomial g L lam x X p =
      (1/2:ℝ) • polynomialRotationCombination (referenceFrameConnectionCoefficient g L lam x X) p := by
  unfold referenceFrameAngularPolynomial
  rw [polynomialMatrixVectorField_eq_neg_half_smul _
    (fun i j => referenceFrameConnectionCoefficient_skew g hg L lam x X i j)]
  simp

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric

set_option diagnostics true in
theorem fderiv_referenceMovingFramePolynomial_horizontal (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x v X : R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    fderiv ℝ (movingFramePolynomial
      (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
      (fun y => referenceMetricGramFrame g L (lam,y)) p) (x,v)
      (X,-referenceConnectionFamily g L (lam,x) X v) =
    eval (fun i => movingFrameCoordinate
      (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
      (fun y => referenceMetricGramFrame g L (lam,y)) i (x,v))
      (-polynomialMatrixVectorField
        (frameConnectionCoefficient
          (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
          (fun y => referenceConnectionFamily g L (lam,y))
          (fun y => referenceMetricGramFrame g L (lam,y)) x X) p) := by
  have hpair : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hM : ContDiff ℝ ∞ (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) :=
    (contDiff_referenceMetricOperator_joint g hg L).comp hpair
  exact fderiv_movingFramePolynomial_horizontal _ _ _ hM
    (fun a => contDiff_referenceMetricGramFrame_slice g hg L lam a)
    (fun y U V => referenceMetricOperator_symmetric g hg L lam y U V)
    (fun y => referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,y))
    (fun y Y U V => referenceConnectionFamily_metric_compatible g hg L lam y Y U V) p x v X

theorem referenceFrameAngularPolynomial_harmonicHomogeneous (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x X : R3)
    (k : ℕ) (hk : 1 ≤ k) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    referenceFrameAngularPolynomial g L lam x X p ∈ harmonicHomogeneous k := by
  rw [referenceFrameAngularPolynomial_eq_half_smul g hg L lam x X p]
  exact (harmonicHomogeneous k).smul_mem _
    (polynomialRotationCombination_harmonicHomogeneous k hk _ p hp)

theorem referenceFrameAngularPolynomial_eq_zero_of_isHomogeneous_zero
    (g : MatrixField) (L lam : ℝ) (x X : R3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous 0) :
    referenceFrameAngularPolynomial g L lam x X p = 0 := by
  simp only [referenceFrameAngularPolynomial, polynomialMatrixVectorField,
    CurvatureContraction.pderiv_eq_zero_of_isHomogeneous_zero p hp,
    mul_zero, Finset.sum_const_zero, neg_zero]

end OAI.AnisotropicCalderon.MovingFrameConnection
