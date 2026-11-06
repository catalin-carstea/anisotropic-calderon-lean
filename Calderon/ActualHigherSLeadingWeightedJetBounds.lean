import Calderon.ActualHigherSCoordinateWeightBounds
import Calderon.ActualHigherSAdjointLeadingCoordinate
import Calderon.ActualHigherSScalarCommutatorForm
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLeadingWeightedJetBounds
section Generic
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_fderiv_scalar_smul_le (c : R3 → ℝ) (f : R3 → V) (x : R3)
    (hc : DifferentiableAt ℝ c x) (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (fun y => c y • f y) x‖ ≤
      ‖c x‖*‖fderiv ℝ f x‖+‖fderiv ℝ c x‖*‖f x‖ := by
  rw [fderiv_fun_smul hc hf]
  exact (norm_add_le _ _).trans (by rw [norm_smul,ContinuousLinearMap.norm_smulRight_apply])

theorem norm_double_sum_le (v : Fin 3 → Fin 3 → V) (C : ℝ)
    (hv : ∀ i j, ‖v i j‖ ≤ C) : ‖∑ i : Fin 3, ∑ j : Fin 3, v i j‖ ≤ 9*C := by
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, v i j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, C := Finset.sum_le_sum (fun i _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hv i j)))
    _ = _ := by simp only [Fin.sum_univ_three]; ring

/-- Both ordered scalar weights are retained in all nine genuine gained rows. -/
theorem weighted_family_first_caps
    (a b : Fin 3 → R3 → ℝ) (G : Fin 3 → Fin 3 → R3 → V) (x : R3)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hb : ∀ j, DifferentiableAt ℝ (b j) x)
    (hG : ∀ i j, DifferentiableAt ℝ (G i j) x)
    (M B0 B1 : ℝ) (hM : 0 ≤ M) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (h0a : ∀ i, ‖a i x‖ ≤ M) (h1a : ∀ i, ‖fderiv ℝ (a i) x‖ ≤ M)
    (h0b : ∀ j, ‖b j x‖ ≤ M) (h1b : ∀ j, ‖fderiv ℝ (b j) x‖ ≤ M)
    (h0G : ∀ i j, ‖G i j x‖ ≤ B0) (h1G : ∀ i j, ‖fderiv ℝ (G i j) x‖ ≤ B1) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, (a i x*b j x) • G i j x‖ ≤ 9*M^2*B0 ∧
    ‖fderiv ℝ (fun y => ∑ i : Fin 3, ∑ j : Fin 3, (a i y*b j y) • G i j y) x‖ ≤
      9*(2*M^2*B0+M^2*B1) := by
  let row := fun i j y => (a i y*b j y) • G i j y
  have hd (i j : Fin 3) : DifferentiableAt ℝ (row i j) x := ((ha i).mul (hb j)).smul (hG i j)
  have hprod0 (i j : Fin 3) : ‖a i x*b j x‖ ≤ M^2 := by
    rw [norm_mul,pow_two]
    exact mul_le_mul (h0a i) (h0b j) (norm_nonneg _) hM
  have hprod1 (i j : Fin 3) : ‖fderiv ℝ (fun y => a i y*b j y) x‖ ≤ 2*M^2 := by
    have hh := norm_fderiv_scalar_smul_le (a i) (b j) x (ha i) (hb j)
    change ‖fderiv ℝ (fun y => a i y*b j y) x‖ ≤ _ at hh
    calc
      _ ≤ ‖a i x‖*‖fderiv ℝ (b j) x‖+‖fderiv ℝ (a i) x‖*‖b j x‖ := hh
      _ ≤ M*M+M*M := add_le_add
        (mul_le_mul (h0a i) (h1b j) (norm_nonneg _) hM)
        (mul_le_mul (h1a i) (h0b j) (norm_nonneg _) hM)
      _ = _ := by ring
  have hrow0 (i j : Fin 3) : ‖row i j x‖ ≤ M^2*B0 := by
    rw [show row i j x=(a i x*b j x) • G i j x from rfl,norm_smul]
    exact mul_le_mul (hprod0 i j) (h0G i j) (norm_nonneg _) (sq_nonneg M)
  have hrow1 (i j : Fin 3) : ‖fderiv ℝ (row i j) x‖ ≤ 2*M^2*B0+M^2*B1 := by
    have hh := norm_fderiv_scalar_smul_le (fun y => a i y*b j y) (G i j) x
      ((ha i).mul (hb j)) (hG i j)
    calc
      _ ≤ ‖a i x*b j x‖*‖fderiv ℝ (G i j) x‖+
        ‖fderiv ℝ (fun y => a i y*b j y) x‖*‖G i j x‖ := hh
      _ ≤ M^2*B1+(2*M^2)*B0 := add_le_add
        (mul_le_mul (hprod0 i j) (h1G i j) (norm_nonneg _) (sq_nonneg M))
        (mul_le_mul (hprod1 i j) (h0G i j) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hdf : fderiv ℝ (fun y => ∑ i : Fin 3, ∑ j : Fin 3, row i j y) x =
      ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (row i j) x := by
    calc
      _ = fderiv ℝ (∑ i : Fin 3, ∑ j : Fin 3, row i j) x := by
        congr 1
      _ = ∑ i : Fin 3, fderiv ℝ (∑ j : Fin 3, row i j) x :=
        fderiv_sum (fun i _ => DifferentiableAt.sum (fun j _ => hd i j))
      _ = _ := Finset.sum_congr rfl (fun i _ => fderiv_sum (fun j _ => hd i j))
  refine ⟨?_,?_⟩
  · exact (norm_double_sum_le (fun i j => row i j x) (M^2*B0) hrow0).trans (by ring_nf; rfl)
  · change ‖fderiv ℝ (fun y => ∑ i : Fin 3, ∑ j : Fin 3, row i j y) x‖ ≤ _
    rw [hdf]
    exact norm_double_sum_le _ _ hrow1

/-- The literal minus-radius-four factor keeps its full physical derivative. -/
theorem negative_radius_four_first_caps (R : R3 → ℝ) (F : R3 → V) (x : R3)
    (hR : DifferentiableAt ℝ R x) (hF : DifferentiableAt ℝ F x)
    (A B J beta : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hr : 0 ≤ R x) (hb : 1 ≤ beta)
    (h0 : ‖F x‖ ≤ A) (h1 : ‖fderiv ℝ F x‖ ≤ B)
    (hjet : ‖fderiv ℝ R x‖ ≤ J*R x*beta) :
    ‖(-(R x)^4) • F x‖ ≤ A*(R x)^4 ∧
      ‖fderiv ℝ (fun y => (-(R y)^4) • F y) x‖ ≤ (B+4*J*A)*(R x)^4*beta := by
  have hb0 : 0 ≤ beta := by linarith
  have hc0 : ‖-(R x)^4‖ = (R x)^4 := by rw [norm_neg,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr 4)]
  have hdc := ((hR.hasFDerivAt.pow 4).neg).fderiv
  have hneg : (-(fun y : R3 => (R y)^4)) = (fun y : R3 => -(R y)^4) := by funext y; rfl
  rw [hneg] at hdc
  have hdcEq : fderiv ℝ (fun y => -(R y)^4) x = -((4*(R x)^3) • fderiv ℝ R x) := by
    simpa only [Nat.reduceSub,nsmul_eq_mul,Nat.cast_ofNat] using hdc
  have hc1 : ‖fderiv ℝ (fun y => -(R y)^4) x‖ ≤ 4*J*(R x)^4*beta := by
    calc
      _ = (4*(R x)^3)*‖fderiv ℝ R x‖ := by rw [hdcEq,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      _ ≤ (4*(R x)^3)*(J*R x*beta) := mul_le_mul_of_nonneg_left hjet (by positivity)
      _ = _ := by ring
  have hc : DifferentiableAt ℝ (fun y => -(R y)^4) x := (hR.pow 4).neg
  refine ⟨?_,?_⟩
  · rw [norm_smul,hc0]
    exact (mul_le_mul_of_nonneg_left h0 (pow_nonneg hr 4)).trans (by ring_nf; rfl)
  · calc
      _ ≤ ‖-(R x)^4‖*‖fderiv ℝ F x‖+
        ‖fderiv ℝ (fun y => -(R y)^4) x‖*‖F x‖ := norm_fderiv_scalar_smul_le _ _ x hc hF
      _ ≤ (R x)^4*B+(4*J*(R x)^4*beta)*A := by
        rw [hc0]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (pow_nonneg hr 4))
          (mul_le_mul hc1 h0 (norm_nonneg _) (by positivity))
      _ ≤ (R x)^4*(B*beta)+(4*J*(R x)^4*beta)*A := by
        gcongr
        exact le_mul_of_one_le_right hB hb
      _ = _ := by ring

/-- Exactly the attenuation required by the existing one-base integration-by-parts estimate. -/
theorem radius_four_absorption (r beta eps : ℝ) (hr : 0 ≤ r) (hb : 1 ≤ beta)
    (heps : eps ≤ 1) (hsmall : r*beta^2 ≤ eps) :
    r^4 ≤ eps/beta ∧ r^4*beta ≤ eps := by
  have hb0 : 0 ≤ beta := by linarith
  have hbpos : 0 < beta := by linarith
  have hb2 : 1 ≤ beta^2 := by nlinarith
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hb2)]
  have hr2 : r^2 ≤ r := by nlinarith
  have hr42 : r^4 ≤ r^2 := by nlinarith [mul_le_mul hr2 hr2 (sq_nonneg r) hr]
  have hr4 : r^4 ≤ r := hr42.trans hr2
  have hb12 : beta ≤ beta^2 := by nlinarith
  have h4 : r^4*beta ≤ eps :=
    (mul_le_mul hr4 hb12 hb0 hr).trans hsmall
  exact ⟨(le_div_iff₀ hbpos).mpr h4,h4⟩
end Generic
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLeadingWeightedJetBounds
