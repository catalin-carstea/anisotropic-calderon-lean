import Calderon.ActualScalarPrincipalSelfCommutator
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualScalarPrincipalSelfFormBound
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds PerturbedDensityAdjoint
  ConformalDepth ActualScalarPrincipalAdjoint ActualPerturbedDefect
  ActualPrincipalErrorCoefficient ActualPrincipalAdjointDerivative
  ActualPrincipalAdjointHigherJets NaturalAngularAdjoint ActualScalarPrincipalSelfCommutator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def coordinateEnergyDensity (v : Fin 3 → R3) (beta : ℝ) (u : R3 → E) (x : R3) : ℝ :=
  beta⁻¹*(∑ i, ‖directionalFDeriv (v i) u x‖^2)+beta*‖u x‖^2

def coordinateEnergy (v : Fin 3 → R3) (mu beta : R3 → ℝ) (u : R3 → E) : ℝ :=
  ∫ x, mu x*coordinateEnergyDensity v (beta x) u x

lemma coordinateEnergyDensity_nonneg (v : Fin 3 → R3) (beta : ℝ)
    (u : R3 → E) (x : R3) (hb : 0 ≤ beta) :
    0 ≤ coordinateEnergyDensity v beta u x := by
  unfold coordinateEnergyDensity
  positivity

lemma coordinate_gradient_pair_le (v : Fin 3 → R3) (u : R3 → E) (x : R3) (i j : Fin 3) :
    ‖directionalFDeriv (v i) u x‖*‖directionalFDeriv (v j) u x‖ ≤
      ∑ k, ‖directionalFDeriv (v k) u x‖^2 := by
  have hi := Finset.single_le_sum (f := fun k : Fin 3 => ‖directionalFDeriv (v k) u x‖^2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have hj := Finset.single_le_sum (f := fun k : Fin 3 => ‖directionalFDeriv (v k) u x‖^2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [sq_nonneg (‖directionalFDeriv (v i) u x‖-‖directionalFDeriv (v j) u x‖)]

lemma coordinate_gradient_square_le (v : Fin 3 → R3) (u : R3 → E) (x : R3) (i : Fin 3) :
    ‖directionalFDeriv (v i) u x‖^2 ≤ ∑ k, ‖directionalFDeriv (v k) u x‖^2 :=
  Finset.single_le_sum (f := fun k : Fin 3 => ‖directionalFDeriv (v k) u x‖^2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ i)

lemma inv_sq_le_inv_of_one_le (beta : ℝ) (hb : 1 ≤ beta) : beta⁻¹^2 ≤ beta⁻¹ := by
  have hp : 0 < beta := by linarith
  have ht : beta⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr hb
  nlinarith [inv_nonneg.mpr hp.le]

lemma inv_le_beta_of_one_le (beta : ℝ) (hb : 1 ≤ beta) : beta⁻¹ ≤ beta := by
  have hp : 0 < beta := by linarith
  exact ((inv_le_one₀ hp).mpr hb).trans hb

lemma coordinate_mixed_square_le (v : Fin 3 → R3) (u : R3 → E) (x : R3)
    (beta : ℝ) (hb : 1 ≤ beta) (i : Fin 3) :
    beta⁻¹*(‖directionalFDeriv (v i) u x‖^2+‖u x‖^2) ≤
      coordinateEnergyDensity v beta u x := by
  have hp : 0 ≤ beta⁻¹ := inv_nonneg.mpr (by linarith)
  have h1 := mul_le_mul_of_nonneg_left (coordinate_gradient_square_le v u x i) hp
  have h2 := mul_le_mul_of_nonneg_right (inv_le_beta_of_one_le beta hb) (sq_nonneg ‖u x‖)
  unfold coordinateEnergyDensity
  nlinarith

lemma norm_sum_three_sq_le (U : Fin 3 → E) : ‖∑ i, U i‖^2 ≤ 3*∑ i, ‖U i‖^2 := by
  have hn := norm_sum_le Finset.univ U
  have hn0 : 0 ≤ ∑ i, ‖U i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 => (1 : ℝ)) (fun i => ‖U i‖)
  have hs' : (∑ i, ‖U i‖)^2 ≤ 3*∑ i, ‖U i‖^2 := by simpa using hs
  exact ((sq_le_sq₀ (norm_nonneg _) hn0).mpr hn).trans hs'

lemma norm_add_sq_le_twice (u w : E) : ‖u+w‖^2 ≤ 2*‖u‖^2+2*‖w‖^2 := by
  rw [norm_add_sq_real]
  nlinarith [real_inner_le_norm u w,sq_nonneg (‖u‖-‖w‖)]

lemma directional_triple_mul (X : R3) (mu a b : R3 → ℝ)
    (hm : ContDiff ℝ ∞ mu) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (x : R3) :
    directionalFDeriv X (fun y => mu y*a y*b y) x =
      directionalFDeriv X mu x*a x*b x+mu x*directionalFDeriv X a x*b x+
        mu x*a x*directionalFDeriv X b x := by
  rw [directional_mul X _ b (hm.mul ha) hb,directional_mul X mu a hm ha]
  ring

lemma abs_ab_product_derivative_le (mu dmu a da b db M A0 A1 B Bd eps t : ℝ)
    (hm : 0 ≤ mu) (hM : 0 ≤ M) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hB : 0 ≤ B) (hBd : 0 ≤ Bd) (heps : 0 ≤ eps) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hdmu : |dmu| ≤ M*mu) (ha : |a| ≤ A0*eps*t^2) (hda : |da| ≤ A1*eps*t)
    (hb : |b| ≤ B*eps*t) (hdb : |db| ≤ Bd*eps) :
    |dmu*a*b+mu*da*b+mu*a*db| ≤ mu*(M*A0*B+A1*B+A0*Bd)*eps^2*t^2 := by
  have h1 : |dmu*a*b| ≤ mu*M*A0*B*eps^2*t^2 := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ ((M*mu)*(A0*eps*t^2))*(B*eps*t) :=
        mul_le_mul (mul_le_mul hdmu ha (abs_nonneg _) (by positivity)) hb (abs_nonneg _) (by positivity)
      _ = (mu*M*A0*B*eps^2*t^2)*t := by ring
      _ ≤ (mu*M*A0*B*eps^2*t^2)*1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ = _ := by ring
  have h2 : |mu*da*b| ≤ mu*A1*B*eps^2*t^2 := by
    rw [abs_mul,abs_mul,abs_of_nonneg hm]
    have hv := mul_le_mul (mul_le_mul_of_nonneg_left hda hm) hb (abs_nonneg _) (by positivity)
    convert hv using 1 <;> ring
  have h3 : |mu*a*db| ≤ mu*A0*Bd*eps^2*t^2 := by
    rw [abs_mul,abs_mul,abs_of_nonneg hm]
    have hv := mul_le_mul (mul_le_mul_of_nonneg_left ha hm) hdb (abs_nonneg _) (by positivity)
    convert hv using 1 <;> ring
  exact (abs_three_add_le _ _ _).trans (by nlinarith)

/-- Numerical inputs to the form mechanics, all discharged for the actual coefficients below. -/
def ScalarCoefficientBudget (mu : R3 → ℝ) (a : MatrixField) (b : Fin 3 → R3 → ℝ)
    (c : R3 → ℝ) (x : R3) (M A0 A1 B Bd Z Zd eps beta : ℝ) : Prop :=
  (∀ k, |directionalFDeriv (coordinateDirection k) mu x| ≤ M*mu x) ∧
  (∀ i j, |a x i j| ≤ A0*eps*beta⁻¹^2) ∧
  (∀ i j k, |directionalFDeriv (coordinateDirection k) (fun y => a y i j) x| ≤ A1*eps*beta⁻¹) ∧
  (∀ l, |b l x| ≤ B*eps*beta⁻¹) ∧
  (∀ l k, |directionalFDeriv (coordinateDirection k) (b l) x| ≤ Bd*eps) ∧
  |c x| ≤ Z*eps ∧
  ∀ k, |directionalFDeriv (coordinateDirection k) c x| ≤ Zd*eps*beta

/-- All scalar self-commutator coefficient jets come from actual fixed geometry and radius jets. -/
theorem exists_actual_scalar_coefficient_budget (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ M A0 A1 B Bd Z Zd : ℝ,
      0 < M ∧ 0 < A0 ∧ 0 < A1 ∧ 0 < B ∧ 0 < Bd ∧ 0 < Z ∧ 0 < Zd ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j, CoordinateThreeJetBound (fun y => h y i j) x
        (eps*referenceRadius δ R p L x)) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x*beta^2 ≤ eps →
      ScalarCoefficientBudget (fun y => referenceDensityFamily g L (lam,y))
        (actualPrincipalMatrix g L lam δ R p h)
        (fun l y => adjointFirstCoefficient coordinateDirection
          (fun z => referenceDensityFamily g L (lam,z)) (actualPrincipalMatrix g L lam δ R p h) y l)
        (adjointZeroCoefficient coordinateDirection (fun z => referenceDensityFamily g L (lam,z))
          (actualPrincipalMatrix g L lam δ R p h)) x M A0 A1 B Bd Z Zd eps beta := by
  obtain ⟨A0,A1,A2,hA0,hA1,hA2,hajet⟩ := exists_actual_principal_uniform_two_jet_bound g hg L hL K hK
  obtain ⟨B,Z,hB,hZ,hbc⟩ := exists_actual_adjoint_coefficients_uniform_bounds g hg L hL K hK
  obtain ⟨Bd,hBd,hbd⟩ := exists_actual_adjoint_first_derivative_uniform_bound g hg L hL K hK
  obtain ⟨Bdd,Zd,hBdd,hZd,hczd⟩ := exists_actual_adjoint_higher_derivatives_uniform_bounds g hg L hL K hK
  obtain ⟨M,hM,hbackground⟩ := exists_referenceBackground_uniform_three_jet_bound g hg L K hK
  refine ⟨M^2,A0,A1,B,Bd,Z,Zd,by positivity,hA0,hA1,hB,hBd,hZ,hZd,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall
  have htwo (i j k l : Fin 3) := coordinateThreeJetBound_twoJetBound _ _ _ (hhjet i j) k l
  have ha' := hajet lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh htwo hb hsmall
  obtain ⟨hb',hc'⟩ := hbc lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh htwo hb hsmall
  have hbd' := hbd lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh htwo hb hsmall
  obtain ⟨_,hcd'⟩ := hczd lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall
  let mu : R3 → ℝ := fun y => referenceDensityFamily g L (lam,y)
  have hmpos : 0 < mu x := referenceDensityFamily_pos g hg L (lam,x)
  have hmjet : CoordinateThreeJetBound mu x M := by
    simpa [mu,referenceBackgroundFamily] using hbackground lam hlam x hx (.inl 0)
  have hnjet : CoordinateThreeJetBound (fun y => (mu y)⁻¹) x M := by
    simpa [mu,referenceBackgroundFamily] using hbackground lam hlam x hx (.inl 1)
  have hMn : 1 ≤ M*mu x := by
    have hn : (mu x)⁻¹ ≤ M := by simpa [abs_of_pos (inv_pos.mpr hmpos)] using hnjet.1
    have ht := mul_le_mul_of_nonneg_right hn hmpos.le
    rw [inv_mul_cancel₀ hmpos.ne'] at ht
    exact ht
  refine ⟨?_,?_,?_,?_,?_,hc',hcd'⟩
  · intro k
    have ht := mul_le_mul_of_nonneg_left hMn (show 0 ≤ M by linarith)
    exact (hmjet.2.1 k).trans (by nlinarith)
  · intro i j
    simpa only [div_eq_mul_inv,inv_pow] using (ha' i j 0 0).1
  · intro i j k
    simpa only [div_eq_mul_inv] using (ha' i j k k).2.1
  · intro l
    simpa only [div_eq_mul_inv] using hb' l
  · exact hbd'

lemma continuous_actual_profile_beta (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Continuous (metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
      (fun y => Real.log (referenceRadius δ R p L y))) :=
  continuous_metricDifferentialNorm _ (dilatedReferenceMetric_smooth_entries g hg lam L)
    (dilatedReferenceMetric_posDef g hg lam L)
    _ (contDiff_log_referenceRadius_profile δ R L p hδ hR)

lemma actual_profile_beta_pos (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R) (hp : 1 ≤ p)
    (x : R3) : 0 < metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
      (fun y => Real.log (referenceRadius δ R p L y)) x := by
  rw [log_referenceRadius δ R p L hδ hR,
    metricDifferentialNorm_logProfile _ δ (Real.log R) p (referenceDepth L) x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
  have ht := metricDifferentialNorm_pos _ (dilatedReferenceMetric_posDef g hg lam L)
    (referenceDepth L) x (fderiv_referenceDepth_ne_zero L (ne_of_gt hL) x)
  have hp0 : 0 < p := by omega
  exact mul_pos (mul_pos (by exact_mod_cast hp0 : (0 : ℝ) < (p : ℝ))
    (RadiusProfile.logSlope_pos δ _ hδ)) ht

lemma abs_ac_product_derivative_le (mu dmu a da c dc M A0 A1 Z Zd eps beta t : ℝ)
    (hm : 0 ≤ mu) (hM : 0 ≤ M) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hZ : 0 ≤ Z) (hZd : 0 ≤ Zd) (heps : 0 ≤ eps)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (htbeta : t*beta = 1)
    (hdmu : |dmu| ≤ M*mu) (ha : |a| ≤ A0*eps*t^2) (hda : |da| ≤ A1*eps*t)
    (hc : |c| ≤ Z*eps) (hdc : |dc| ≤ Zd*eps*beta) :
    |dmu*a*c+mu*da*c+mu*a*dc| ≤ mu*(M*A0*Z+A1*Z+A0*Zd)*eps^2*t := by
  have h1 : |dmu*a*c| ≤ mu*M*A0*Z*eps^2*t := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ ((M*mu)*(A0*eps*t^2))*(Z*eps) :=
        mul_le_mul (mul_le_mul hdmu ha (abs_nonneg _) (by positivity)) hc (abs_nonneg _) (by positivity)
      _ = (mu*M*A0*Z*eps^2*t)*t := by ring
      _ ≤ (mu*M*A0*Z*eps^2*t)*1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ = _ := by ring
  have h2 : |mu*da*c| ≤ mu*A1*Z*eps^2*t := by
    rw [abs_mul,abs_mul,abs_of_nonneg hm]
    have hv := mul_le_mul (mul_le_mul_of_nonneg_left hda hm) hc (abs_nonneg _) (by positivity)
    convert hv using 1 <;> ring
  have h3 : |mu*a*dc| ≤ mu*A0*Zd*eps^2*t := by
    rw [abs_mul,abs_mul,abs_of_nonneg hm]
    calc
      _ ≤ ((mu*(A0*eps*t^2))*(Zd*eps*beta)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha hm) hdc (abs_nonneg _) (by positivity)
      _ = (mu*A0*Zd*eps^2*t)*(t*beta) := by ring
      _ = _ := by rw [htbeta,mul_one]
  exact (abs_three_add_le _ _ _).trans (by nlinarith)

lemma coordinate_gradient_weight_le (v : Fin 3 → R3) (u : R3 → E) (x : R3)
    (beta : ℝ) (hb : 1 ≤ beta) (i j : Fin 3) :
    beta⁻¹^2*(‖directionalFDeriv (v i) u x‖*‖directionalFDeriv (v j) u x‖) ≤
      coordinateEnergyDensity v beta u x := by
  have hS : 0 ≤ ∑ k, ‖directionalFDeriv (v k) u x‖^2 := by positivity
  calc
    _ ≤ beta⁻¹^2*(∑ k, ‖directionalFDeriv (v k) u x‖^2) :=
      mul_le_mul_of_nonneg_left (coordinate_gradient_pair_le v u x i j) (sq_nonneg _)
    _ ≤ beta⁻¹*(∑ k, ‖directionalFDeriv (v k) u x‖^2) :=
      mul_le_mul_of_nonneg_right (inv_sq_le_inv_of_one_le beta hb) hS
    _ ≤ _ := by
      unfold coordinateEnergyDensity
      exact le_add_of_nonneg_right (by positivity)

lemma coordinate_zero_square_le (v : Fin 3 → R3) (u : R3 → E) (x : R3)
    (beta : ℝ) (hb : 1 ≤ beta) : ‖u x‖^2 ≤ coordinateEnergyDensity v beta u x := by
  have h0 := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖u x‖)
  have ht : 0 ≤ beta⁻¹*(∑ k, ‖directionalFDeriv (v k) u x‖^2) := by positivity
  unfold coordinateEnergyDensity
  nlinarith

lemma abs_weighted_gradient_pair_le (v : Fin 3 → R3) (u : R3 → E) (x : R3)
    (mu w Q eps beta : ℝ) (hm : 0 ≤ mu) (hQ : 0 ≤ Q) (heps : 0 ≤ eps)
    (hb : 1 ≤ beta) (i j : Fin 3) (hw : |w| ≤ mu*Q*eps^2*beta⁻¹^2) :
    |w*⟪directionalFDeriv (v i) u x,directionalFDeriv (v j) u x⟫_ℝ| ≤
      mu*Q*eps^2*coordinateEnergyDensity v beta u x := by
  rw [abs_mul]
  calc
    _ ≤ (mu*Q*eps^2*beta⁻¹^2)*
        (‖directionalFDeriv (v i) u x‖*‖directionalFDeriv (v j) u x‖) :=
      mul_le_mul hw (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity)
    _ = (mu*Q*eps^2)*(beta⁻¹^2*
        (‖directionalFDeriv (v i) u x‖*‖directionalFDeriv (v j) u x‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (coordinate_gradient_weight_le v u x beta hb i j)
      (by positivity)

lemma abs_twice_weighted_mixed_pair_le (v : Fin 3 → R3) (u : R3 → E) (x : R3)
    (mu w Q eps beta : ℝ) (hm : 0 ≤ mu) (hQ : 0 ≤ Q) (heps : 0 ≤ eps)
    (hb : 1 ≤ beta) (i : Fin 3) (hw : |w| ≤ mu*Q*eps^2*beta⁻¹) :
    |2*(w*⟪directionalFDeriv (v i) u x,u x⟫_ℝ)| ≤
      mu*Q*eps^2*coordinateEnergyDensity v beta u x := by
  have hnorm : 2*(‖directionalFDeriv (v i) u x‖*‖u x‖) ≤
      ‖directionalFDeriv (v i) u x‖^2+‖u x‖^2 := by
    nlinarith [sq_nonneg (‖directionalFDeriv (v i) u x‖-‖u x‖)]
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2),abs_mul]
  calc
    _ ≤ 2*((mu*Q*eps^2*beta⁻¹)*
        (‖directionalFDeriv (v i) u x‖*‖u x‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hw (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity)) (by norm_num)
    _ = (mu*Q*eps^2*beta⁻¹)*(2*(‖directionalFDeriv (v i) u x‖*‖u x‖)) := by ring
    _ ≤ (mu*Q*eps^2*beta⁻¹)*(‖directionalFDeriv (v i) u x‖^2+‖u x‖^2) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (mu*Q*eps^2)*(beta⁻¹*(‖directionalFDeriv (v i) u x‖^2+‖u x‖^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (coordinate_mixed_square_le v u x beta hb i)
      (by positivity)

lemma norm_scalarFirstZeroBase_sq_le (v : Fin 3 → R3) (b : Fin 3 → R3 → ℝ)
    (c : R3 → ℝ) (u : R3 → E) (x : R3) (B Z eps beta : ℝ)
    (hB : 0 ≤ B) (hZ : 0 ≤ Z) (heps : 0 ≤ eps) (hb : 1 ≤ beta)
    (hbs : ∀ l, |b l x| ≤ B*eps*beta⁻¹) (hcs : |c x| ≤ Z*eps) :
    ‖scalarFirstZeroBase v b c u x‖^2 ≤
      (6*B^2+2*Z^2)*eps^2*coordinateEnergyDensity v beta u x := by
  have hcn : ‖c x • u x‖^2 ≤ Z^2*eps^2*‖u x‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow]
    have hs : |c x|^2 ≤ (Z*eps)^2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hcs
    have ht := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖u x‖)
    convert ht using 1 <;> ring
  have hbn (l : Fin 3) : ‖b l x • directionalFDeriv (v l) u x‖^2 ≤
      B^2*eps^2*beta⁻¹^2*‖directionalFDeriv (v l) u x‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow]
    have hs : |b l x|^2 ≤ (B*eps*beta⁻¹)^2 :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hbs l)
    have ht := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖directionalFDeriv (v l) u x‖)
    convert ht using 1 <;> ring
  have hsum : ‖∑ l, b l x • directionalFDeriv (v l) u x‖^2 ≤
      3*B^2*eps^2*beta⁻¹^2*(∑ l, ‖directionalFDeriv (v l) u x‖^2) := by
    calc
      _ ≤ 3*∑ l, ‖b l x • directionalFDeriv (v l) u x‖^2 := norm_sum_three_sq_le _
      _ ≤ 3*∑ l, B^2*eps^2*beta⁻¹^2*‖directionalFDeriv (v l) u x‖^2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun l _ => hbn l)) (by norm_num)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hgrad : beta⁻¹^2*(∑ l, ‖directionalFDeriv (v l) u x‖^2) ≤
      coordinateEnergyDensity v beta u x := by
    have hs : 0 ≤ ∑ l, ‖directionalFDeriv (v l) u x‖^2 := by positivity
    have ht := mul_le_mul_of_nonneg_right (inv_sq_le_inv_of_one_le beta hb) hs
    exact ht.trans (by
      unfold coordinateEnergyDensity
      exact le_add_of_nonneg_right (by positivity))
  have hcenergy := mul_le_mul_of_nonneg_left (coordinate_zero_square_le v u x beta hb)
    (show 0 ≤ Z^2*eps^2 by positivity)
  have hbenergy := mul_le_mul_of_nonneg_left hgrad (show 0 ≤ 3*B^2*eps^2 by positivity)
  have hadd := norm_add_sq_le_twice (c x • u x) (∑ l, b l x • directionalFDeriv (v l) u x)
  unfold scalarFirstZeroBase
  nlinarith

lemma coefficient_budget_product_bounds (mu : R3 → ℝ) (a : MatrixField)
    (b : Fin 3 → R3 → ℝ) (c : R3 → ℝ) (x : R3)
    (M A0 A1 B Bd Z Zd eps beta : ℝ) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hb : ∀ l, ContDiff ℝ ∞ (b l)) (hc : ContDiff ℝ ∞ c)
    (hmu : 0 ≤ mu x) (hM : 0 ≤ M) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hB : 0 ≤ B) (hBd : 0 ≤ Bd) (hZ : 0 ≤ Z) (hZd : 0 ≤ Zd)
    (heps : 0 ≤ eps) (hbeta : 1 ≤ beta)
    (hbudget : ScalarCoefficientBudget mu a b c x M A0 A1 B Bd Z Zd eps beta) :
    (∀ i j l k, |directionalFDeriv (coordinateDirection k)
      (fun y => mu y*a y i j*b l y) x| ≤
        mu x*(M*A0*B+A1*B+A0*Bd)*eps^2*beta⁻¹^2) ∧
    (∀ i j k, |directionalFDeriv (coordinateDirection k)
      (fun y => mu y*a y i j*c y) x| ≤
        mu x*(M*A0*Z+A1*Z+A0*Zd)*eps^2*beta⁻¹) ∧
    ∀ i j, |mu x*a x i j*c x| ≤ mu x*(A0*Z)*eps^2*beta⁻¹^2 := by
  rcases hbudget with ⟨hdmu,haval,had,hbval,hbd,hcval,hcd⟩
  have hbetapos : 0 < beta := by linarith
  have ht : 0 ≤ beta⁻¹ := inv_nonneg.mpr hbetapos.le
  have ht1 : beta⁻¹ ≤ 1 := (inv_le_one₀ hbetapos).mpr hbeta
  refine ⟨?_,?_,?_⟩
  · intro i j l k
    rw [directional_triple_mul _ mu (fun y => a y i j) (b l) hm (ha i j) (hb l)]
    exact abs_ab_product_derivative_le _ _ _ _ _ _ M A0 A1 B Bd eps beta⁻¹
      hmu hM hA0 hA1 hB hBd heps ht ht1 (hdmu k) (haval i j) (had i j k)
      (hbval l) (hbd l k)
  · intro i j k
    rw [directional_triple_mul _ mu (fun y => a y i j) c hm (ha i j) hc]
    exact abs_ac_product_derivative_le _ _ _ _ _ _ M A0 A1 Z Zd eps beta beta⁻¹
      hmu hM hA0 hA1 hZ hZd heps ht ht1 (inv_mul_cancel₀ hbetapos.ne')
      (hdmu k) (haval i j) (had i j k) hcval (hcd k)
  · intro i j
    rw [abs_mul,abs_mul,abs_of_nonneg hmu]
    have ht' := mul_le_mul (mul_le_mul_of_nonneg_left (haval i j) hmu)
      hcval (abs_nonneg _) (by positivity)
    convert ht' using 1 <;> ring

lemma coordinateEnergy_integrable (v : Fin 3 → R3) (mu beta : R3 → ℝ)
    (u : R3 → E) (hm : Continuous mu) (hb : Continuous beta)
    (hbpos : ∀ x, 0 < beta x) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    Integrable (fun x => mu x*coordinateEnergyDensity v (beta x) u x) := by
  have hbi : Continuous (fun x => (beta x)⁻¹) := hb.inv₀ (fun x => ne_of_gt (hbpos x))
  have hg (i : Fin 3) : Integrable (fun x => (mu x*(beta x)⁻¹)*‖directionalFDeriv (v i) u x‖^2) :=
    compact_weighted_norm_sq_integrable _ _ (hm.mul hbi)
      (contDiff_directionalFDeriv (v i) u hu).continuous (hc.fderiv_apply (𝕜 := ℝ) (v i))
  have hz : Integrable (fun x => (mu x*beta x)*‖u x‖^2) :=
    compact_weighted_norm_sq_integrable _ u (hm.mul hb) hu.continuous hc
  have hs := (integrable_finsetSum Finset.univ (fun i _ => hg i)).add hz
  convert hs using 1
  funext x
  simp only [coordinateEnergyDensity,Finset.sum_apply,Pi.add_apply,Finset.mul_sum,mul_add]
  ring

lemma coordinateEnergy_nonneg (v : Fin 3 → R3) (mu beta : R3 → ℝ)
    (u : R3 → E) (hm : ∀ x, 0 ≤ mu x) (hb : ∀ x, 0 ≤ beta x) :
    0 ≤ coordinateEnergy v mu beta u :=
  integral_nonneg (fun x => mul_nonneg (hm x) (coordinateEnergyDensity_nonneg v _ u x (hb x)))

lemma section_and_first_jets_eq_zero_off (v : Fin 3 → R3) (u : R3 → E)
    (K : Set R3) (hsub : tsupport u ⊆ K) (x : R3) (hx : x ∉ K) :
    u x = 0 ∧ ∀ i, directionalFDeriv (v i) u x = 0 := by
  have hxt : x ∉ tsupport u := fun ht => hx (hsub ht)
  refine ⟨image_eq_zero_of_notMem_tsupport hxt,?_⟩
  intro i
  simp only [directionalFDeriv,fderiv_of_notMem_tsupport ℝ hxt,ContinuousLinearMap.zero_apply]

lemma abs_integral_of_supported_energy_bound (v : Fin 3 → R3) (mu beta : R3 → ℝ)
    (u : R3 → E) (K : Set R3) (F : R3 → ℝ) (q : ℝ)
    (hmu : ∀ x, 0 ≤ mu x) (hbeta : ∀ x, 0 ≤ beta x) (hq : 0 ≤ q)
    (hF : Integrable F)
    (henergy : Integrable (fun x => mu x*coordinateEnergyDensity v (beta x) u x))
    (hlocal : ∀ x ∈ K, |F x| ≤ q*(mu x*coordinateEnergyDensity v (beta x) u x))
    (hoff : ∀ x ∉ K, F x = 0) :
    |∫ x, F x| ≤ q*coordinateEnergy v mu beta u := by
  have hglobal (x : R3) : |F x| ≤ q*(mu x*coordinateEnergyDensity v (beta x) u x) := by
    by_cases hx : x ∈ K
    · exact hlocal x hx
    · rw [hoff x hx,abs_zero]
      exact mul_nonneg hq (mul_nonneg (hmu x) (coordinateEnergyDensity_nonneg v _ u x (hbeta x)))
  calc
    _ ≤ ∫ x, |F x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, q*(mu x*coordinateEnergyDensity v (beta x) u x) :=
      integral_mono hF.abs (henergy.const_mul q) hglobal
    _ = _ := integral_const_mul q _

lemma compact_gradient_pair_integral_bound (mu beta w : R3 → ℝ) (u : R3 → E)
    (K : Set R3) (Q eps : ℝ) (hm : Continuous mu) (hb : Continuous beta)
    (hw : Continuous w) (hmu : ∀ x, 0 < mu x) (hbpos : ∀ x, 0 < beta x)
    (hQ : 0 ≤ Q) (heps : 0 ≤ eps) (hbeta : ∀ x ∈ K, 1 ≤ beta x)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (hsub : tsupport u ⊆ K)
    (i j : Fin 3) (hbound : ∀ x ∈ K, |w x| ≤ mu x*Q*eps^2*(beta x)⁻¹^2) :
    |∫ x, w x*⟪directionalFDeriv (coordinateDirection i) u x,
      directionalFDeriv (coordinateDirection j) u x⟫_ℝ| ≤
      (Q*eps^2)*coordinateEnergy coordinateDirection mu beta u := by
  apply abs_integral_of_supported_energy_bound coordinateDirection mu beta u K
    (fun x => w x*⟪directionalFDeriv (coordinateDirection i) u x,
      directionalFDeriv (coordinateDirection j) u x⟫_ℝ) (Q*eps^2)
    (fun x => (hmu x).le) (fun x => (hbpos x).le) (by positivity)
    (compact_weighted_inner_integrable w _ _ hw
      (contDiff_directionalFDeriv _ u hu).continuous (contDiff_directionalFDeriv _ u hu).continuous
      (hc.fderiv_apply (𝕜 := ℝ) (coordinateDirection i)))
    (coordinateEnergy_integrable coordinateDirection mu beta u hm hb hbpos hu hc)
  · intro x hx
    have ht := abs_weighted_gradient_pair_le coordinateDirection u x (mu x) (w x) Q eps
      (beta x) (hmu x).le hQ heps (hbeta x hx) i j (hbound x hx)
    convert ht using 1 <;> ring
  · intro x hx
    obtain ⟨_,hzero⟩ := section_and_first_jets_eq_zero_off coordinateDirection u K hsub x hx
    simp only [hzero i,inner_zero_left,mul_zero]

lemma compact_twice_mixed_integral_bound (mu beta w : R3 → ℝ) (u : R3 → E)
    (K : Set R3) (Q eps : ℝ) (hm : Continuous mu) (hb : Continuous beta)
    (hw : Continuous w) (hmu : ∀ x, 0 < mu x) (hbpos : ∀ x, 0 < beta x)
    (hQ : 0 ≤ Q) (heps : 0 ≤ eps) (hbeta : ∀ x ∈ K, 1 ≤ beta x)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (hsub : tsupport u ⊆ K)
    (i : Fin 3) (hbound : ∀ x ∈ K, |w x| ≤ mu x*Q*eps^2*(beta x)⁻¹) :
    |2*(∫ x, w x*⟪directionalFDeriv (coordinateDirection i) u x,u x⟫_ℝ)| ≤
      (Q*eps^2)*coordinateEnergy coordinateDirection mu beta u := by
  rw [← integral_const_mul]
  apply abs_integral_of_supported_energy_bound coordinateDirection mu beta u K
    (fun x => 2*(w x*⟪directionalFDeriv (coordinateDirection i) u x,u x⟫_ℝ)) (Q*eps^2)
    (fun x => (hmu x).le) (fun x => (hbpos x).le) (by positivity)
    ((compact_weighted_inner_integrable w _ u hw
      (contDiff_directionalFDeriv _ u hu).continuous hu.continuous
      (hc.fderiv_apply (𝕜 := ℝ) (coordinateDirection i))).const_mul 2)
    (coordinateEnergy_integrable coordinateDirection mu beta u hm hb hbpos hu hc)
  · intro x hx
    have ht := abs_twice_weighted_mixed_pair_le coordinateDirection u x (mu x) (w x) Q eps
      (beta x) (hmu x).le hQ heps (hbeta x hx) i (hbound x hx)
    convert ht using 1 <;> ring
  · intro x hx
    obtain ⟨hzero,_⟩ := section_and_first_jets_eq_zero_off coordinateDirection u K hsub x hx
    simp only [hzero,inner_zero_right,mul_zero]

lemma compact_first_zero_square_integral_bound (mu beta : R3 → ℝ)
    (b : Fin 3 → R3 → ℝ) (c : R3 → ℝ) (u : R3 → E) (K : Set R3) (B Z eps : ℝ)
    (hm : ContDiff ℝ ∞ mu) (hb : Continuous beta)
    (hbs : ∀ l, ContDiff ℝ ∞ (b l)) (hcs : ContDiff ℝ ∞ c)
    (hmu : ∀ x, 0 < mu x) (hbpos : ∀ x, 0 < beta x)
    (hB : 0 ≤ B) (hZ : 0 ≤ Z) (heps : 0 ≤ eps) (hbeta : ∀ x ∈ K, 1 ≤ beta x)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (hsub : tsupport u ⊆ K)
    (hboundb : ∀ x ∈ K, ∀ l, |b l x| ≤ B*eps*(beta x)⁻¹)
    (hboundc : ∀ x ∈ K, |c x| ≤ Z*eps) :
    |∫ x, mu x*‖scalarFirstZeroBase coordinateDirection b c u x‖^2| ≤
      ((6*B^2+2*Z^2)*eps^2)*coordinateEnergy coordinateDirection mu beta u := by
  apply abs_integral_of_supported_energy_bound coordinateDirection mu beta u K
    (fun x => mu x*‖scalarFirstZeroBase coordinateDirection b c u x‖^2)
    ((6*B^2+2*Z^2)*eps^2) (fun x => (hmu x).le) (fun x => (hbpos x).le) (by positivity)
    (compact_weighted_norm_sq_integrable mu _ hm.continuous
      (contDiff_scalarFirstZeroBase coordinateDirection b c u hbs hcs hu).continuous
      (hasCompactSupport_scalarFirstZeroBase coordinateDirection b c u hc))
    (coordinateEnergy_integrable coordinateDirection mu beta u hm.continuous hb hbpos hu hc)
  · intro x hx
    rw [abs_of_nonneg (mul_nonneg (hmu x).le (sq_nonneg _))]
    have ht := mul_le_mul_of_nonneg_left (norm_scalarFirstZeroBase_sq_le coordinateDirection
      b c u x B Z eps (beta x) hB hZ heps (hbeta x hx) (hboundb x hx) (hboundc x hx)) (hmu x).le
    convert ht using 1 <;> ring
  · intro x hx
    obtain ⟨hzero,hfirst⟩ := section_and_first_jets_eq_zero_off coordinateDirection u K hsub x hx
    simp [scalarFirstZeroBase,hzero,hfirst]

lemma abs_sum_fin_three_le (F : Fin 3 → ℝ) (q : ℝ) (hF : ∀ i, |F i| ≤ q) :
    |∑ i, F i| ≤ 3*q := by
  calc
    _ ≤ ∑ i, |F i| := Finset.abs_sum_le_sum_abs F Finset.univ
    _ ≤ ∑ _i : Fin 3, q := Finset.sum_le_sum (fun i _ => hF i)
    _ = _ := by simp

lemma abs_add_sub_le_of_bounds (X Y Z A B C : ℝ)
    (hX : |X| ≤ A) (hY : |Y| ≤ B) (hZ : |Z| ≤ C) :
    |X+Y-Z| ≤ A+B+C := by
  exact (abs_sub (X+Y) Z).trans (by linarith [abs_add_le X Y])

/-- The fixed numerical constant in the first-jet form estimate. -/
def selfFormConstant (M A0 A1 B Bd Z Zd : ℝ) : ℝ :=
  81*(M*A0*B+A1*B+A0*Bd)+9*(M*A0*Z+A1*Z+A0*Zd)+18*A0*Z+6*B^2+2*Z^2

lemma selfFormConstant_pos (M A0 A1 B Bd Z Zd : ℝ)
    (hM : 0 < M) (hA0 : 0 < A0) (hA1 : 0 < A1) (hB : 0 < B)
    (hBd : 0 < Bd) (hZ : 0 < Z) (hZd : 0 < Zd) :
    0 < selfFormConstant M A0 A1 B Bd Z Zd := by
  unfold selfFormConstant
  positivity

/-- The form mechanics require only actual first/zero adjoint jets and scalar principal first jets.
The conditional budget here is discharged by `exists_actual_scalar_coefficient_budget`. -/
theorem compact_scalarReducedSelfForm_bound (mu beta : R3 → ℝ) (a : MatrixField)
    (b : Fin 3 → R3 → ℝ) (c : R3 → ℝ) (u : R3 → E) (K : Set R3)
    (M A0 A1 B Bd Z Zd eps : ℝ) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hb : ∀ l, ContDiff ℝ ∞ (b l)) (hc : ContDiff ℝ ∞ c)
    (hbetacont : Continuous beta) (hmupos : ∀ x, 0 < mu x) (hbetapos : ∀ x, 0 < beta x)
    (hM : 0 ≤ M) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hB : 0 ≤ B)
    (hBd : 0 ≤ Bd) (hZ : 0 ≤ Z) (hZd : 0 ≤ Zd) (heps : 0 ≤ eps)
    (hbeta : ∀ x ∈ K, 1 ≤ beta x)
    (hbudget : ∀ x ∈ K, ScalarCoefficientBudget mu a b c x M A0 A1 B Bd Z Zd eps (beta x))
    (hu : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u) (hsub : tsupport u ⊆ K) :
    |scalarReducedSelfForm coordinateDirection mu a b c u| ≤
      (selfFormConstant M A0 A1 B Bd Z Zd*eps^2)*coordinateEnergy coordinateDirection mu beta u := by
  let Qa := M*A0*B+A1*B+A0*Bd
  let Qc := M*A0*Z+A1*Z+A0*Zd
  let energy := coordinateEnergy coordinateDirection mu beta u
  have hQa : 0 ≤ Qa := by dsimp [Qa]; positivity
  have hQc : 0 ≤ Qc := by dsimp [Qc]; positivity
  have hprod (x : R3) (hx : x ∈ K) := coefficient_budget_product_bounds mu a b c x
    M A0 A1 B Bd Z Zd eps (beta x) hm ha hb hc (hmupos x).le
    hM hA0 hA1 hB hBd hZ hZd heps (hbeta x hx) (hbudget x hx)
  have hab (i j l k m n : Fin 3) :
      |∫ x, directionalFDeriv (coordinateDirection k) (fun y => mu y*a y i j*b l y) x *
        ⟪directionalFDeriv (coordinateDirection m) u x,
          directionalFDeriv (coordinateDirection n) u x⟫_ℝ| ≤ (Qa*eps^2)*energy :=
    compact_gradient_pair_integral_bound mu beta _ u K Qa eps hm.continuous hbetacont
      (contDiff_directionalFDeriv _ _ ((hm.mul (ha i j)).mul (hb l))).continuous
      hmupos hbetapos hQa heps hbeta hu hcompact hsub m n
      (fun x hx => (hprod x hx).1 i j l k)
  have hac (i j : Fin 3) :
      |2*(∫ x, directionalFDeriv (coordinateDirection i) (fun y => mu y*a y i j*c y) x *
        ⟪directionalFDeriv (coordinateDirection j) u x,u x⟫_ℝ)| ≤ (Qc*eps^2)*energy :=
    compact_twice_mixed_integral_bound mu beta _ u K Qc eps hm.continuous hbetacont
      (contDiff_directionalFDeriv _ _ ((hm.mul (ha i j)).mul hc)).continuous
      hmupos hbetapos hQc heps hbeta hu hcompact hsub j
      (fun x hx => (hprod x hx).2.1 i j i)
  have hz (i j : Fin 3) :
      |2*(∫ x, mu x*a x i j*c x *
        ⟪directionalFDeriv (coordinateDirection i) u x,
          directionalFDeriv (coordinateDirection j) u x⟫_ℝ)| ≤ 2*((A0*Z*eps^2)*energy) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left
      (compact_gradient_pair_integral_bound mu beta _ u K (A0*Z) eps hm.continuous hbetacont
        (((hm.mul (ha i j)).mul hc).continuous) hmupos hbetapos (by positivity) heps
        hbeta hu hcompact hsub i j (fun x hx => (hprod x hx).2.2 i j)) (by norm_num)
  have hdef : |∫ x, mu x*‖scalarFirstZeroBase coordinateDirection b c u x‖^2| ≤
      ((6*B^2+2*Z^2)*eps^2)*energy :=
    compact_first_zero_square_integral_bound mu beta b c u K B Z eps hm hbetacont hb hc
      hmupos hbetapos hB hZ heps hbeta hu hcompact hsub
      (fun x hx => (hbudget x hx).2.2.2.1) (fun x hx => (hbudget x hx).2.2.2.2.2.1)
  let F (i j l : Fin 3) : ℝ :=
    (∫ x, directionalFDeriv (coordinateDirection i) (fun y => mu y*a y i j*b l y) x *
      ⟪directionalFDeriv (coordinateDirection j) u x,directionalFDeriv (coordinateDirection l) u x⟫_ℝ)+
    (∫ x, directionalFDeriv (coordinateDirection j) (fun y => mu y*a y i j*b l y) x *
      ⟪directionalFDeriv (coordinateDirection i) u x,directionalFDeriv (coordinateDirection l) u x⟫_ℝ)-
    (∫ x, directionalFDeriv (coordinateDirection l) (fun y => mu y*a y i j*b l y) x *
      ⟪directionalFDeriv (coordinateDirection i) u x,directionalFDeriv (coordinateDirection j) u x⟫_ℝ)
  let G (i j : Fin 3) : ℝ :=
    2*(∫ x, directionalFDeriv (coordinateDirection i) (fun y => mu y*a y i j*c y) x *
      ⟪directionalFDeriv (coordinateDirection j) u x,u x⟫_ℝ)+
    2*(∫ x, mu x*a x i j*c x *
      ⟪directionalFDeriv (coordinateDirection i) u x,directionalFDeriv (coordinateDirection j) u x⟫_ℝ)
  have hF (i j l : Fin 3) : |F i j l| ≤ 3*((Qa*eps^2)*energy) := by
    have ht := abs_add_sub_le_of_bounds _ _ _ _ _ _
      (hab i j l i j l) (hab i j l j i l) (hab i j l l i j)
    convert ht using 1 <;> ring
  have hG (i j : Fin 3) : |G i j| ≤ (Qc*eps^2)*energy+2*((A0*Z*eps^2)*energy) := by
    exact (abs_add_le _ _).trans (add_le_add (hac i j) (hz i j))
  have hFsum : |∑ i, ∑ j, ∑ l, F i j l| ≤ 81*((Qa*eps^2)*energy) := by
    have ht := abs_sum_fin_three_le _ _ (fun i => abs_sum_fin_three_le _ _
      (fun j => abs_sum_fin_three_le _ _ (hF i j)))
    convert ht using 1 <;> ring
  have hGsum : |∑ i, ∑ j, G i j| ≤ 9*((Qc*eps^2)*energy+2*((A0*Z*eps^2)*energy)) := by
    have ht := abs_sum_fin_three_le _ _ (fun i => abs_sum_fin_three_le _ _ (hG i))
    convert ht using 1 <;> ring
  have ht := abs_add_sub_le_of_bounds _ _ _ _ _ _ hFsum hGsum hdef
  change |(∑ i, ∑ j, ∑ l, F i j l)+(∑ i, ∑ j, G i j)-
    (∫ x, mu x*‖scalarFirstZeroBase coordinateDirection b c u x‖^2)| ≤ _
  convert ht using 1 <;> dsimp [selfFormConstant,Qa,Qc] <;> ring

/-- A uniform bound for the genuine actual scalar-principal self-commutator. The constant is
selected from fixed geometry before every dilation, profile, perturbation, or test section.
The sole perturbation-size premise is the literal finite coordinate three-jet condition. -/
theorem exists_actual_scalar_principal_self_commutator_form_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ h : MatrixField, (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ x, (h x).IsHermitian) →
      (∀ x ∈ K, ∀ i j, CoordinateThreeJetBound (fun y => h y i j) x
        (eps*referenceRadius δ R p L x)) →
      let beta : R3 → ℝ := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y))
      (∀ x ∈ K, 1 ≤ beta x) →
      (∀ x ∈ K, referenceRadius δ R p L x*(beta x)^2 ≤ eps) →
      ∀ u : R3 → E, ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u ⊆ K →
      |∫ x, referenceDensityFamily g L (lam,x)*
        ⟪scalarPrincipalSelfCommutator coordinateDirection
          (fun y => referenceDensityFamily g L (lam,y))
          (actualPrincipalMatrix g L lam δ R p h) u x,u x⟫_ℝ| ≤
        (C*eps)*coordinateEnergy coordinateDirection
          (fun y => referenceDensityFamily g L (lam,y)) beta u := by
  obtain ⟨M,A0,A1,B,Bd,Z,Zd,hM,hA0,hA1,hB,hBd,hZ,hZd,hactual⟩ :=
    exists_actual_scalar_coefficient_budget g hg L hL K hK
  let C := selfFormConstant M A0 A1 B Bd Z Zd
  have hC : 0 < C := selfFormConstant_pos M A0 A1 B Bd Z Zd hM hA0 hA1 hB hBd hZ hZd
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hs hhjet beta hbeta hsmall u hu hc hsub
  let mu : R3 → ℝ := fun y => referenceDensityFamily g L (lam,y)
  let a : MatrixField := actualPrincipalMatrix g L lam δ R p h
  let b : Fin 3 → R3 → ℝ := fun l y => adjointFirstCoefficient coordinateDirection mu a y l
  let c : R3 → ℝ := adjointZeroCoefficient coordinateDirection mu a
  have hslice : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hm : ContDiff ℝ ∞ mu := (contDiff_referenceDensityFamily g hg L).comp hslice
  have hmu : ∀ x, 0 < mu x := fun x => referenceDensityFamily_pos g hg L (lam,x)
  have hmu0 : ∀ x, mu x ≠ 0 := fun x => ne_of_gt (hmu x)
  have ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j) :=
    contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh
  have hbc : ∀ l, ContDiff ℝ ∞ (b l) := ActualScalarPrincipalSelfCommutator.contDiff_adjointFirstCoefficient coordinateDirection mu a hm ha hmu0
  have hcc : ContDiff ℝ ∞ c := ActualScalarPrincipalSelfCommutator.contDiff_adjointZeroCoefficient coordinateDirection mu a hm ha hmu0
  have hasym : ∀ x, (a x).IsHermitian :=
    fun x => actualPrincipalMatrix_isHermitian g hg L lam δ R p h x (hs x)
  have hbetacont : Continuous beta := continuous_actual_profile_beta g hg L lam δ R p hδ hR
  have hbetapos : ∀ x, 0 < beta x := actual_profile_beta_pos g hg L lam δ R p hL hδ hR hp
  have hbudget (x : R3) (hx : x ∈ K) :
      ScalarCoefficientBudget mu a b c x M A0 A1 B Bd Z Zd eps (beta x) :=
    hactual lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh (hhjet x hx)
      (hbeta x hx) (hsmall x hx)
  have hbound := compact_scalarReducedSelfForm_bound mu beta a b c u K M A0 A1 B Bd Z Zd eps
    hm ha hbc hcc hbetacont hmu hbetapos hM.le hA0.le hA1.le hB.le hBd.le hZ.le hZd.le heps
    hbeta hbudget hu hc hsub
  have hidentity := compact_scalarPrincipalSelfCommutator_reduced_form coordinateDirection mu a u
    hm ha hu hc hmu hasym
  change |∫ x, mu x*⟪scalarPrincipalSelfCommutator coordinateDirection mu a u x,u x⟫_ℝ| ≤
    (C*eps)*coordinateEnergy coordinateDirection mu beta u
  rw [hidentity]
  have hepssq : eps^2 ≤ eps := by nlinarith
  have henergy : 0 ≤ coordinateEnergy coordinateDirection mu beta u :=
    coordinateEnergy_nonneg coordinateDirection mu beta u (fun x => (hmu x).le) (fun x => (hbetapos x).le)
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hepssq hC.le) henergy)

end OAI.AnisotropicCalderon.ActualScalarPrincipalSelfFormBound
