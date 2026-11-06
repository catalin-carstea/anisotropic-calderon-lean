import Calderon.ActualMiddleSuperlinearHalfBootstrap
import Calderon.ActualReferenceRadiusCompactContinuation
import Calderon.ActualPositiveDepthStrictCurrentRadius
import Calderon.ActualKnownSideNormalizedH8Zero
import Calderon.ActualNormalizedPrincipalH8InitialSmallness
import MixedKernelUniformLowerSide
import MixedKernelCylinderBoundary

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth RadiusProfile CoordinateBootstrapJets
  ReferenceWeightedApproximation
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ActualNormalizedPrincipalH8InitialSmallness

/-- The fixed middle gain and the actual beta profile yield one dilation for
all softplus radii. The `hGain` input is the conditional result of the actual
five-source factory and still needs its exact same-cutoff angular density bound. -/
theorem exists_one_dilation_current_radius_bootstrap_of_middle_three_halves
    (S : KnownSideSourceData) (L Rstar eps C rho0 tb eta : ℝ) (p : ℕ)
    (hL : 0 < L) (hRstar : 0 < Rstar) (heps : 0 < eps)
    (hC : 0 ≤ C) (hrho0 : 0 < rho0) (htb : 0 < tb)
    (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hKcompact : IsCompact {y : R3 | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
      referenceDepth L y ≤ 2 * tb})
    (hBeta : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ y ∈ cylinder,
        referenceRadius delta Rstar p L y *
          (actualReferenceBeta S.g1 L lam delta Rstar p y)^2 ≤ eps)
    (hGain : ∀ lam : ℝ, 0 < lam → lam ≤ eta →
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        CurrentRadiusBootstrap S L lam delta Rstar eps p →
        ∀ y ∈ {y : R3 | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
          referenceDepth L y ≤ 2 * tb},
          referenceRadius delta Rstar p L y < rho0 →
          coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
            C * (referenceRadius delta Rstar p L y)^(3/2 : ℝ)) :
    ∃ rho lam : ℝ, 0 < rho ∧ rho < rho0 ∧ C * rho^((1 : ℝ)/2) ≤ eps/2 ∧
      0 < lam ∧ lam ≤ eta ∧
      (let K : Set R3 := {y | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
        referenceDepth L y ≤ 2 * tb}
       (∀ y ∈ K, coordinateH8
          (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
            eps * referenceRadius 1 Rstar p L y) ∧
       (∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ y ∈ cylinder, y ∉ K →
          coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
            (eps/2) * referenceRadius delta Rstar p L y) ∧
       (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
          (∀ y ∈ K, coordinateH8
            (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
              eps * referenceRadius delta Rstar p L y) →
          ∀ y ∈ K, coordinateH8
            (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
              (eps/2) * referenceRadius delta Rstar p L y) ∧
       (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
          CurrentRadiusBootstrap S L lam delta Rstar eps p)) := by
  let K : Set R3 := {y | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
    referenceDepth L y ≤ 2 * tb}
  let q : ℝ := eps / (2 * (C+1))
  have hC1 : 0 < C+1 := by linarith
  have hq : 0 < q := div_pos heps (by positivity)
  let rho : ℝ := min (rho0/2) (q^2)
  have hrho : 0 < rho := lt_min (by positivity) (sq_pos_of_pos hq)
  have hrho0lt : rho < rho0 := (min_le_left _ _).trans_lt (by linarith)
  have hrhoq : rho ≤ q^2 := min_le_right _ _
  have hsqrt : rho^((1 : ℝ)/2) ≤ q := by
    rw [← Real.sqrt_eq_rpow]
    calc
      Real.sqrt rho ≤ Real.sqrt (q^2) := Real.sqrt_le_sqrt hrhoq
      _ = q := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
  have hChoice : C * rho^((1 : ℝ)/2) ≤ eps/2 := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt hC
    have hqeq : 2*(C+1)*q = eps := by
      dsimp [q]
      field_simp
    nlinarith only [hmul,hqeq,hq]
  have hRadiusCont : Continuous (referenceRadius 1 Rstar p L) :=
    (ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual
      1 Rstar p L (by norm_num) hRstar).continuous
  obtain ⟨m,hm,hMin⟩ := hKcompact.exists_forall_le' hRadiusCont.continuousOn
    (a := (0 : ℝ)) (fun y _ => referenceRadius_pos 1 Rstar p L y (by norm_num) hRstar)
  let A : ℝ := min ((eps/2)*rho) (eps*m)
  have hA : 0 < A := lt_min (mul_pos (by linarith) hrho) (mul_pos heps hm)
  obtain ⟨lamSmall,hlamSmall,hlamSmallOne,hSmall⟩ :=
    exists_referenceNormalizedPrincipalDifference_coordinateH8_small
      S.g1 S.g2 S.g1_admissible S.g2_admissible S.g1_origin S.g2_origin
      L cylinder isCompact_native_center_cylinder A hA
  obtain ⟨lamUpper,hlamUpper,hlamUpperOne,hUpper⟩ :=
    exists_positive_depth_strict_current_radius_bound
      S L eps Rstar (2*tb) p hL heps hRstar (by positivity)
  obtain ⟨lamLower,hlamLower,hLower⟩ :=
    exists_uniform_scaled_lower_strip S 2 (1/2) (by norm_num) (by norm_num)
  let lam : ℝ := min (min eta lamUpper) (min lamLower lamSmall)
  have hlam : 0 < lam := lt_min (lt_min heta hlamUpper) (lt_min hlamLower hlamSmall)
  have hlamEta : lam ≤ eta := (min_le_left _ _).trans (min_le_left _ _)
  have hlamOne : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.le, hlamEta.trans hetaOne⟩
  have hlamUpper' : lam ≤ lamUpper := (min_le_left _ _).trans (min_le_right _ _)
  have hlamLower' : lam ≤ lamLower := (min_le_right _ _).trans (min_le_left _ _)
  have hlamSmall' : lam ≤ lamSmall := (min_le_right _ _).trans (min_le_right _ _)
  have hGlobalSmall : ∀ y ∈ cylinder,
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤ A :=
    hSmall lam ⟨hlam.le,hlamSmall'⟩
  have hInitial : ∀ y ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
        eps * referenceRadius 1 Rstar p L y := by
    intro y hy
    calc
      _ ≤ A := hGlobalSmall y hy.1
      _ ≤ eps*m := min_le_right _ _
      _ ≤ eps*referenceRadius 1 Rstar p L y :=
        mul_le_mul_of_nonneg_left (hMin y hy) heps.le
  have hOff : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ y ∈ cylinder, y ∉ K →
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
        (eps/2) * referenceRadius delta Rstar p L y := by
    intro delta hdelta hdeltaOne y hy hNotK
    by_cases hLow : y 2 ≤ -(1/2 : ℝ)
    · have hKnown : lam • y ∈ S.W :=
        hLower lam hlam hlamLower' y (norm_le_two_of_mem_cylinder y hy) hLow
      rw [coordinateH8_referenceNormalizedPrincipalDifference_zero_of_known_side
        S L lam y hKnown]
      exact mul_nonneg (by linarith)
        (referenceRadius_pos delta Rstar p L y hdelta hRstar).le
    · have hDepth : 2*tb ≤ referenceDepth L y := by
        by_contra hnot
        have hHeight : -(1/2 : ℝ) ≤ y 2 := le_of_not_ge hLow
        exact hNotK ⟨hy,hHeight,le_of_not_ge hnot⟩
      exact hUpper lam ⟨hlam.le,hlamUpper'⟩
        delta hdelta hdeltaOne y hy hDepth
  have hImprove : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      (∀ y ∈ K, coordinateH8
        (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
          eps * referenceRadius delta Rstar p L y) →
      ∀ y ∈ K, coordinateH8
        (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
          (eps/2) * referenceRadius delta Rstar p L y := by
    intro delta hdelta hdeltaOne hOnK
    have hFirst : ∀ y ∈ cylinder,
        coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
          eps * referenceRadius delta Rstar p L y := by
      intro y hy
      by_cases hmem : y ∈ K
      · exact hOnK y hmem
      · exact (hOff delta hdelta hdeltaOne y hy hmem).trans
          (mul_le_mul_of_nonneg_right (by linarith : eps/2 ≤ eps)
            (referenceRadius_pos delta Rstar p L y hdelta hRstar).le)
    have hSecond : ∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
        referenceRadius delta' Rstar p L y *
          (actualReferenceBeta S.g1 L lam delta' Rstar p y)^2 ≤ eps := by
      intro delta' hd' y hy
      exact hBeta lam hlamOne delta' (hdelta.trans_le hd'.1) hd'.2 y hy
    have hBoot : CurrentRadiusBootstrap S L lam delta Rstar eps p :=
      ⟨hFirst,hSecond⟩
    have hSmallGain : ∀ y ∈ K,
        referenceRadius delta Rstar p L y < rho →
          coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
            C * (referenceRadius delta Rstar p L y)^(3/2 : ℝ) := by
      intro y hy hr
      exact hGain lam hlam hlamEta delta hdelta hdeltaOne hBoot y hy (hr.trans hrho0lt)
    have hLarge : ∀ y ∈ K, rho ≤ referenceRadius delta Rstar p L y →
        coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
          (eps/2)*rho := by
      intro y hy _
      exact (hGlobalSmall y hy.1).trans (min_le_left _ _)
    exact actual_middle_half_bootstrap_of_superlinear_and_one_dilation
      S L lam delta Rstar eps C rho tb p hdelta hRstar heps hC hrho hChoice
      hSmallGain hLarge
  have hAllK : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ y ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
        eps * referenceRadius delta Rstar p L y :=
    coordinateH8_le_referenceRadius_forall_delta_of_strict_improvement
      S.g1 S.g2 S.g1_admissible S.g2_admissible L lam Rstar eps p K hKcompact
      hRstar heps hInitial hImprove
  have hAllBoot : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      CurrentRadiusBootstrap S L lam delta Rstar eps p := by
    intro delta hdelta hdeltaOne
    constructor
    · intro y hy
      by_cases hmem : y ∈ K
      · exact hAllK delta hdelta hdeltaOne y hmem
      · exact (hOff delta hdelta hdeltaOne y hy hmem).trans
          (mul_le_mul_of_nonneg_right (by linarith : eps/2 ≤ eps)
            (referenceRadius_pos delta Rstar p L y hdelta hRstar).le)
    · intro delta' hd' y hy
      exact hBeta lam hlamOne delta' (hdelta.trans_le hd'.1) hd'.2 y hy
  exact ⟨rho,lam,hrho,hrho0lt,hChoice,hlam,hlamEta,
    hInitial,hOff,hImprove,hAllBoot⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
