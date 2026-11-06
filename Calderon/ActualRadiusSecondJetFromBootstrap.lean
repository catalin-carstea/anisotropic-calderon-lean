import Calderon.ActualScalarPrincipalAdjoint
import Calderon.FixedProfileBounds
import Calderon.ReferenceWeightedApproximation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

private lemma fderiv_positive_eq_self_smul_log
    (R : R3 → ℝ) (hR : Differentiable ℝ R) (hPos : ∀ x, 0 < R x) (x : R3) :
    fderiv ℝ R x = R x • fderiv ℝ (fun y => Real.log (R y)) x := by
  rw [((hR x).hasFDerivAt.log (hPos x).ne').fderiv,smul_smul]
  simp only [mul_inv_cancel₀ (hPos x).ne',one_smul]

theorem norm_fderiv_fderiv_positive_le_log_jets
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (hPos : ∀ x, 0 < R x) (x : R3) :
    ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ R x *
      (‖fderiv ℝ (fderiv ℝ (fun y => Real.log (R y))) x‖ +
        ‖fderiv ℝ (fun y => Real.log (R y)) x‖^2) := by
  have hDiff := hR.differentiable (by simp)
  have hLog : ContDiff ℝ ∞ (fun y => Real.log (R y)) := hR.log (fun y => (hPos y).ne')
  have hLogDer : Differentiable ℝ (fderiv ℝ (fun y => Real.log (R y))) :=
    (contDiff_infty_iff_fderiv.mp hLog).2.differentiable (by simp)
  have hEq : fderiv ℝ R = fun y => R y • fderiv ℝ (fun z => Real.log (R z)) y :=
    funext (fderiv_positive_eq_self_smul_log R hDiff hPos)
  have hD := congrArg (fun F : R3 → R3 →L[ℝ] ℝ => fderiv ℝ F x) hEq
  rw [fderiv_fun_smul (hDiff x) (hLogDer x)] at hD
  rw [hD]
  calc
    _ ≤ ‖R x • fderiv ℝ (fderiv ℝ (fun y => Real.log (R y))) x‖ +
        ‖(fderiv ℝ R x).smulRight (fderiv ℝ (fun y => Real.log (R y)) x)‖ := norm_add_le _ _
    _ = R x * ‖fderiv ℝ (fderiv ℝ (fun y => Real.log (R y))) x‖ +
        ‖fderiv ℝ R x‖ * ‖fderiv ℝ (fun y => Real.log (R y)) x‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hPos x),ContinuousLinearMap.norm_smulRight_apply]
    _ = _ := by
      rw [fderiv_positive_eq_self_smul_log R hDiff hPos x,norm_smul,Real.norm_eq_abs,abs_of_pos (hPos x)]
      ring

theorem exists_uniform_referenceRadius_second_derivative_bound_of_bootstrap
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K)
    (L : ℝ) (hL : 0 < L) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ q ∈ Icc (0:ℝ) 1,
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ Rstar : ℝ, 0 < Rstar →
      ∀ p : ℕ, 1 ≤ p → ∀ (eps : ℝ), 0 ≤ eps → ∀ y ∈ K,
      referenceRadius delta Rstar p L y *
        (ReferenceWeightedApproximation.actualReferenceBeta g L q delta Rstar p y)^2 ≤ eps →
      ‖fderiv ℝ (fderiv ℝ (referenceRadius delta Rstar p L)) y‖ ≤ C0*eps := by
  obtain ⟨J1,J2,hJ1,hJ2,hJets⟩ :=
    exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at g hg K hK L hL
  have hC : 0 ≤ J2+J1^2 := by nlinarith [sq_nonneg J1]
  refine ⟨J2+J1^2+1,by nlinarith [sq_nonneg J1],?_⟩
  intro q hq delta hdelta hdelta1 Rstar hRstar p hp eps heps y hy hBootstrap
  let R := referenceRadius delta Rstar p L
  let beta := ReferenceWeightedApproximation.actualReferenceBeta g L q delta Rstar p y
  have hPos (z : R3) : 0 < R z := referenceRadius_pos delta Rstar p L z hdelta hRstar
  have hSmooth : ContDiff ℝ ∞ R := by
    exact OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar
  have hJ := hJets q hq delta hdelta hdelta1 Rstar hRstar p hp y hy
  change ‖fderiv ℝ (fun z => Real.log (R z)) y‖ ≤ J1*beta ∧
    ‖fderiv ℝ (fderiv ℝ (fun z => Real.log (R z))) y‖ ≤ J2*beta^2 at hJ
  have hSq := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ (fun z => Real.log (R z)) y)) hJ.1 2
  calc
    _ ≤ R y * (‖fderiv ℝ (fderiv ℝ (fun z => Real.log (R z))) y‖ +
      ‖fderiv ℝ (fun z => Real.log (R z)) y‖^2) :=
      norm_fderiv_fderiv_positive_le_log_jets R hSmooth hPos y
    _ ≤ R y * (J2*beta^2+(J1*beta)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add hJ.2 hSq) (hPos y).le
    _ = (J2+J1^2)*(R y*beta^2) := by ring
    _ ≤ (J2+J1^2)*eps := mul_le_mul_of_nonneg_left hBootstrap hC
    _ ≤ (J2+J1^2+1)*eps := by nlinarith only [heps]

end OAI.AnisotropicCalderon.ConformalDepth
