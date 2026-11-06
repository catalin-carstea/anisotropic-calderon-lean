import Calderon.CurvatureRotation
import Calderon.PrincipalDirectional
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.CurvatureSkew
open PrincipalCommutator ConnectionError MetricOperator ConformalDepth RadiusProfile
  AngularPolynomial SphereHarmonic CurvatureRotation MvPolynomial

lemma directionalFDeriv_const (v Z x : R3) :
    directionalFDeriv v (fun _ : R3 => Z) x = 0 := by
  simp [directionalFDeriv]

lemma directionalFDeriv_inner (v : R3) (U V : R3 → R3)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (x : R3) :
    directionalFDeriv v (fun y => ⟪U y,V y⟫_ℝ) x =
      ⟪directionalFDeriv v U x,V x⟫_ℝ + ⟪U x,directionalFDeriv v V x⟫_ℝ := by
  unfold directionalFDeriv
  rw [fderiv_inner_apply ℝ (hU.differentiable (by simp) x)
    (hV.differentiable (by simp) x)]
  exact add_comm _ _

lemma directionalFDeriv_metric_pairing (v : R3) (M : R3 → R3 →L[ℝ] R3)
    (U V : R3 → R3) (hM : ContDiff ℝ ∞ M)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (x : R3) :
    directionalFDeriv v (fun y => ⟪M y (U y),V y⟫_ℝ) x =
      ⟪directionalFDeriv v M x (U x) + M x (directionalFDeriv v U x),V x⟫_ℝ +
        ⟪M x (U x),directionalFDeriv v V x⟫_ℝ := by
  rw [directionalFDeriv_inner v _ V (hM.clm_apply hU) hV,
    directionalFDeriv_clm_apply v M U hM hU]

lemma directionalFDeriv_connection_apply (v w Z x : R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (hΓ : ContDiff ℝ ∞ Γ) :
    directionalFDeriv v (fun y => Γ y w Z) x = (fderiv ℝ Γ x v) w Z := by
  rw [directionalFDeriv_clm_apply v _ _ (hΓ.clm_apply contDiff_const) contDiff_const,
    directionalFDeriv_clm_apply v Γ _ hΓ contDiff_const]
  simp [directionalFDeriv_const, directionalFDeriv]

lemma directionalFDeriv_fixed_metric_pairing (v Z W x : R3)
    (M : R3 → R3 →L[ℝ] R3) (hM : ContDiff ℝ ∞ M) :
    directionalFDeriv v (fun y => ⟪M y Z,W⟫_ℝ) x =
      ⟪fderiv ℝ M x v Z,W⟫_ℝ := by
  rw [directionalFDeriv_metric_pairing v M _ _ hM contDiff_const contDiff_const]
  simp [directionalFDeriv_const, directionalFDeriv]

lemma differentiated_metric_compatibility
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (hM : ContDiff ℝ ∞ M) (hΓ : ContDiff ℝ ∞ Γ)
    (hcomp : ∀ x v Z W, ⟪M x (Γ x v Z),W⟫_ℝ + ⟪M x Z,Γ x v W⟫_ℝ =
      ⟪fderiv ℝ M x v Z,W⟫_ℝ) (x v w Z W : R3) :
    directionalFDeriv v (directionalFDeriv w (fun y => ⟪M y Z,W⟫_ℝ)) x =
      ⟪M x (Γ x v (Γ x w Z)),W⟫_ℝ + ⟪M x (Γ x w Z),Γ x v W⟫_ℝ +
      ⟪M x ((fderiv ℝ Γ x v) w Z),W⟫_ℝ +
      ⟪M x (Γ x v Z),Γ x w W⟫_ℝ + ⟪M x Z,Γ x v (Γ x w W)⟫_ℝ +
      ⟪M x Z,(fderiv ℝ Γ x v) w W⟫_ℝ := by
  have he : directionalFDeriv w (fun y => ⟪M y Z,W⟫_ℝ) =
      fun y => ⟪M y (Γ y w Z),W⟫_ℝ + ⟪M y Z,Γ y w W⟫_ℝ := by
    funext y
    rw [directionalFDeriv_fixed_metric_pairing w Z W y M hM]
    exact (hcomp y w Z W).symm
  have hGZ : ContDiff ℝ ∞ (fun y => Γ y w Z) :=
    (hΓ.clm_apply contDiff_const).clm_apply contDiff_const
  have hGW : ContDiff ℝ ∞ (fun y => Γ y w W) :=
    (hΓ.clm_apply contDiff_const).clm_apply contDiff_const
  rw [he, directionalFDeriv_add v _ _
    ((hM.clm_apply hGZ).inner ℝ contDiff_const)
    ((hM.clm_apply contDiff_const).inner ℝ hGW)]
  rw [directionalFDeriv_metric_pairing v M _ _ hM hGZ contDiff_const,
    directionalFDeriv_metric_pairing v M _ _ hM contDiff_const hGW,
    directionalFDeriv_connection_apply v w Z x Γ hΓ,
    directionalFDeriv_connection_apply v w W x Γ hΓ]
  simp only [directionalFDeriv_const, map_zero, add_zero, inner_zero_right,
    inner_add_left, zero_add]
  change ⟪(fderiv ℝ M x v) (Γ x w Z),W⟫_ℝ +
      ⟪M x ((fderiv ℝ Γ x v) w Z),W⟫_ℝ +
      (⟪(fderiv ℝ M x v) Z,Γ x w W⟫_ℝ +
        ⟪M x Z,(fderiv ℝ Γ x v) w W⟫_ℝ) = _
  rw [← hcomp x v (Γ x w Z) W, ← hcomp x v Z (Γ x w W)]
  ring

theorem coordinateCurvatureAction_metric_skew
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (hM : ContDiff ℝ ∞ M) (hΓ : ContDiff ℝ ∞ Γ)
    (hcomp : ∀ x v Z W, ⟪M x (Γ x v Z),W⟫_ℝ + ⟪M x Z,Γ x v W⟫_ℝ =
      ⟪fderiv ℝ M x v Z,W⟫_ℝ) (x v w Z W : R3) :
    ⟪M x (coordinateCurvatureAction Γ x v w Z),W⟫_ℝ +
      ⟪M x Z,coordinateCurvatureAction Γ x v w W⟫_ℝ = 0 := by
  have hp : ContDiff ℝ ∞ (fun y => ⟪M y Z,W⟫_ℝ) :=
    (hM.clm_apply contDiff_const).inner ℝ contDiff_const
  have hc := directionalFDeriv_commute v w _ hp x
  rw [differentiated_metric_compatibility M Γ hM hΓ hcomp,
    differentiated_metric_compatibility M Γ hM hΓ hcomp] at hc
  simp only [coordinateCurvatureAction_apply, map_sub, map_add, inner_sub_left,
    inner_add_left, inner_sub_right, inner_add_right]
  linarith

theorem coordinateConnectionField_metric_compatible
    (M : R3 → R3 →L[ℝ] R3) (hM : ContDiff ℝ ∞ M)
    (hunit : ∀ x, IsUnit (M x))
    (hsym : ∀ x Y Z, ⟪M x Y,Z⟫_ℝ = ⟪M x Z,Y⟫_ℝ) (x X Y Z : R3) :
    ⟪M x (coordinateConnectionField (inverseMetricField M) M x X Y),Z⟫_ℝ +
      ⟪M x Y,coordinateConnectionField (inverseMetricField M) M x X Z⟫_ℝ =
      ⟪fderiv ℝ M x X Y,Z⟫_ℝ := by
  have hk (U V W : R3) := coordinateConnection_koszul (inverseMetricField M x) (M x)
    (fderiv ℝ M x) (fun T => metric_apply_inverseMetricField M hunit x T) U V W
  have h1 := hk X Y Z
  have h2 := hk X Z Y
  have hs := hsym x Y (coordinateConnection (inverseMetricField M x) (fderiv ℝ M x) X Z)
  have hd := inverse_metric_derivative_symmetric M (fderiv ℝ M x) x
    (hM.differentiable (by simp) x).hasFDerivAt
    (Filter.Eventually.of_forall hsym) X Y Z
  simp only [coordinateConnectionField_apply]
  nlinarith

lemma referenceMetricOperator_symmetric (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x Y Z : R3) :
    ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x Y,Z⟫_ℝ =
      ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x Z,Y⟫_ℝ := by
  have hp := EnergyBridge.conformalMatrix_posDef (dilatedMetric g lam)
    (fun y => -L * referenceCoordinateDepth y) (dilatedMetric_posDef g hg lam) x
  have h := Matrix.isSymmetric_toEuclideanLin_iff.mpr hp.isHermitian
  exact (h Y Z).trans (real_inner_comm _ _)

theorem referenceConnectionFamily_metric_compatible (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x X Y Z : R3) :
    ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x
      (referenceConnectionFamily g L (lam,x) X Y),Z⟫_ℝ +
    ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x Y,
      referenceConnectionFamily g L (lam,x) X Z⟫_ℝ =
    ⟪fderiv ℝ (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x X Y,Z⟫_ℝ := by
  let M := metricOperatorField (referenceMetric (dilatedMetric g lam) L)
  have hpair : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) :=
    contDiff_const.prodMk contDiff_id
  have hM := (contDiff_referenceMetricOperator_joint g hg L).comp hpair
  have hu : ∀ y, IsUnit (M y) := by
    intro y
    have hp := EnergyBridge.conformalMatrix_posDef (dilatedMetric g lam)
      (fun z => -L * referenceCoordinateDepth z) (dilatedMetric_posDef g hg lam) y
    exact hp.isUnit.map matrixOperatorAlgEquiv.toMonoidHom
  exact coordinateConnectionField_metric_compatible M hM hu
    (fun y V W => referenceMetricOperator_symmetric g hg L lam y V W) x X Y Z

theorem referenceCurvatureAction_metric_skew (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x v w Z W : R3) :
    ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x
      (referenceCurvatureAction g L lam x v w Z),W⟫_ℝ +
    ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x Z,
      referenceCurvatureAction g L lam x v w W⟫_ℝ = 0 := by
  let M := metricOperatorField (referenceMetric (dilatedMetric g lam) L)
  let Γ := fun y => referenceConnectionFamily g L (lam,y)
  have hpair : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) :=
    contDiff_const.prodMk contDiff_id
  have hM := (contDiff_referenceMetricOperator_joint g hg L).comp hpair
  have hΓ := (contDiff_referenceConnectionFamily g hg L).comp hpair
  exact coordinateCurvatureAction_metric_skew M Γ hM hΓ
    (fun y U V W => referenceConnectionFamily_metric_compatible g hg L lam y U V W)
    x v w Z W

theorem referenceCurvatureRotationCoefficient_skew (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (e : Fin 3 → R3)
    (a b i j : Fin 3) :
    referenceCurvatureRotationCoefficient g L lam x e a b i j =
      -referenceCurvatureRotationCoefficient g L lam x e a b j i := by
  have h := referenceCurvatureAction_metric_skew g hg L lam x (e a) (e b) (e j) (e i)
  rw [referenceMetricOperator_symmetric g hg L lam x (e j)] at h
  unfold referenceCurvatureRotationCoefficient
  linarith

def polynomialMatrixVectorField (c : Fin 3 → Fin 3 → ℝ)
    (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, C (c i j) * X j * pderiv i p

lemma polynomialRotationCombination_eq_neg_two_smul
    (c : Fin 3 → Fin 3 → ℝ) (hc : ∀ i j, c i j = -c j i)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialRotationCombination c p = (-2 : ℝ) • polynomialMatrixVectorField c p := by
  have hd (i : Fin 3) : c i i = 0 := by have h := hc i i; linarith
  simp only [polynomialRotationCombination, polynomialRotation, polynomialMatrixVectorField,
    Fin.sum_univ_three, smul_eq_C_mul]
  rw [hd 0, hd 1, hd 2, hc 1 0, hc 2 0, hc 2 1]
  simp only [map_neg, map_zero, map_ofNat]
  ring

lemma polynomialMatrixVectorField_eq_neg_half_smul
    (c : Fin 3 → Fin 3 → ℝ) (hc : ∀ i j, c i j = -c j i)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialMatrixVectorField c p =
      (- (1 / 2) : ℝ) • polynomialRotationCombination c p := by
  rw [polynomialRotationCombination_eq_neg_two_smul c hc p, smul_smul]
  norm_num

def referenceCurvatureVectorFieldPolynomial (g : MatrixField) (L lam : ℝ) (x : R3)
    (e : Fin 3 → R3) (a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  polynomialMatrixVectorField (referenceCurvatureRotationCoefficient g L lam x e a b) p

theorem referenceCurvatureVectorFieldPolynomial_eq_neg_half_smul (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (e : Fin 3 → R3)
    (a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    referenceCurvatureVectorFieldPolynomial g L lam x e a b p =
      (- (1 / 2) : ℝ) • referenceCurvatureRotationPolynomial g L lam x e a b p := by
  exact polynomialMatrixVectorField_eq_neg_half_smul _
    (fun i j => referenceCurvatureRotationCoefficient_skew g hg L lam x e a b i j) p

end OAI.AnisotropicCalderon.CurvatureSkew
