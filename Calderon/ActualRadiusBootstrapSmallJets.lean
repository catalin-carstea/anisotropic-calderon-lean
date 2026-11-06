import Calderon.ActualRadiusSecondJetFromBootstrap
import Calderon.ReferenceWeightedApproximation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile ReferenceWeightedApproximation

theorem exists_uniform_actualReferenceBeta_ge_one_for_large_p
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K)
    (L : ℝ) (hL : 0 < L) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p → ∀ q ∈ Icc (0:ℝ) 1,
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ Rstar : ℝ, 0 < Rstar → ∀ y ∈ K,
      1 ≤ actualReferenceBeta g L q delta Rstar p y := by
  obtain ⟨m,C,T,hm,hC,hBounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  let a0 : ℝ := 1/(1+Real.log (1+Real.exp T))
  have ha0 : 0 < a0 := by
    dsimp [a0]
    apply one_div_pos.mpr
    have hl : 0 < Real.log (1+Real.exp T) := Real.log_pos (by linarith [Real.exp_pos T])
    linarith
  obtain ⟨n,hn⟩ := exists_nat_ge (1/(a0*m))
  refine ⟨max n 1,le_max_right _ _,?_⟩
  intro p hp q hq delta hdelta hdelta1 Rstar hRstar y hy
  have hp1 : 1 ≤ p := (le_max_right n 1).trans hp
  have hnR : (n:ℝ) ≤ (p:ℝ) := by exact_mod_cast ((le_max_left n 1).trans hp)
  have hpR : 1/(a0*m) ≤ (p:ℝ) := hn.trans hnR
  obtain ⟨hmin,hmax,ht⟩ := hBounds q hq y hy
  have hSlope : a0 ≤ logSlope delta (referenceDepth L y) :=
    logSlope_uniform_lower_bound delta _ T hdelta hdelta1 ht
  rw [actualReferenceBeta_eq g L q delta Rstar p hdelta hRstar y]
  have h1 : 1 ≤ (p:ℝ)*(a0*m) := (div_le_iff₀ (mul_pos ha0 hm)).mp hpR
  calc
    1 ≤ (p:ℝ)*a0*m := by nlinarith only [h1]
    _ ≤ (p:ℝ)*logSlope delta (referenceDepth L y)*m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSlope (Nat.cast_nonneg p)) hm.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hmin
      (mul_nonneg (Nat.cast_nonneg p) (logSlope_pos delta _ hdelta).le)

theorem exists_uniform_referenceRadius_small_ordinary_jets_of_bootstrap
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K)
    (L : ℝ) (hL : 0 < L) (d : ℝ) (hd : 0 < d) :
    ∃ p0 : ℕ, 1 ≤ p0 ∧ ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ q ∈ Icc (0:ℝ) 1,
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ Rstar : ℝ, 0 < Rstar →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 → ∀ y ∈ K,
      referenceRadius delta Rstar p L y*(actualReferenceBeta g L q delta Rstar p y)^2 ≤ eps →
      |referenceRadius delta Rstar p L y| ≤ d ∧
      ‖fderiv ℝ (referenceRadius delta Rstar p L) y‖ ≤ 1 ∧
      ‖fderiv ℝ (fderiv ℝ (referenceRadius delta Rstar p L)) y‖ ≤ 1 := by
  obtain ⟨p0,hp0,hBeta⟩ := exists_uniform_actualReferenceBeta_ge_one_for_large_p g hg K hK L hL
  obtain ⟨J1,J2,hJ1,hJ2,hJets⟩ :=
    exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at g hg K hK L hL
  obtain ⟨C2,hC2,hSecond⟩ := exists_uniform_referenceRadius_second_derivative_bound_of_bootstrap
    g hg K hK L hL
  let eps0 := min d (min 1 (min (1/J1) (1/C2)))
  have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
  have heps0 : 0 < eps0 := lt_min hd (lt_min one_pos (lt_min (one_div_pos.mpr hJ1) (one_div_pos.mpr hC2pos)))
  have hepsd : eps0 ≤ d := min_le_left _ _
  have heps1 : eps0 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hepsJ : eps0 ≤ 1/J1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsC : eps0 ≤ 1/C2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨p0,hp0,eps0,heps0,heps1,?_⟩
  intro p hp q hq delta hdelta hdelta1 Rstar hRstar eps heps hepsSmall y hy hBootstrap
  let R := referenceRadius delta Rstar p L
  let beta := actualReferenceBeta g L q delta Rstar p y
  have hRpos : 0 < R y := referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hbeta : 1 ≤ beta := hBeta p hp q hq delta hdelta hdelta1 Rstar hRstar y hy
  have hp1 : 1 ≤ p := hp0.trans hp
  have hRsmall : R y ≤ eps := by
    have hsq : 1 ≤ beta^2 := by nlinarith only [hbeta]
    calc R y ≤ R y*beta^2 := by nlinarith only [hsq,hRpos]
         _ ≤ eps := hBootstrap
  have hRbeta : R y*beta ≤ eps := by
    have hbSq : beta ≤ beta^2 := by nlinarith only [hbeta]
    calc R y*beta ≤ R y*beta^2 := mul_le_mul_of_nonneg_left hbSq hRpos.le
         _ ≤ eps := hBootstrap
  have hSmooth : ContDiff ℝ ∞ R := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual
    delta Rstar p L hdelta hRstar
  have hEq : fderiv ℝ R y = R y • fderiv ℝ (fun z => Real.log (R z)) y := by
    rw [((hSmooth.differentiable (by simp) y).hasFDerivAt.log hRpos.ne').fderiv,smul_smul]
    simp only [mul_inv_cancel₀ hRpos.ne',one_smul]
  have hLog := (hJets q hq delta hdelta hdelta1 Rstar hRstar p hp1 y hy).1
  change ‖fderiv ℝ (fun z => Real.log (R z)) y‖ ≤ J1*beta at hLog
  have hFirst : ‖fderiv ℝ R y‖ ≤ J1*eps := by
    rw [hEq,norm_smul,Real.norm_eq_abs,abs_of_pos hRpos]
    calc R y*‖fderiv ℝ (fun z => Real.log (R z)) y‖ ≤ R y*(J1*beta) := mul_le_mul_of_nonneg_left hLog hRpos.le
         _ = J1*(R y*beta) := by ring
         _ ≤ J1*eps := mul_le_mul_of_nonneg_left hRbeta hJ1.le
  have hJeps : J1*eps ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_left (hepsSmall.trans hepsJ) hJ1.le
    simpa only [mul_one_div_cancel hJ1.ne'] using ht
  have hCeps : C2*eps ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_left (hepsSmall.trans hepsC) hC2pos.le
    simpa only [mul_one_div_cancel hC2pos.ne'] using ht
  refine ⟨?_,hFirst.trans hJeps,?_⟩
  · rw [abs_of_pos hRpos]
    exact hRsmall.trans (hepsSmall.trans hepsd)
  · exact (hSecond q hq delta hdelta hdelta1 Rstar hRstar p hp1 eps heps y hy hBootstrap).trans hCeps

end OAI.AnisotropicCalderon.ConformalDepth
