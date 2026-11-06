import Calderon.ActualRadiusTwoUniformHigherGreenJets
import Calderon.CollaboratorFixedSobolevCalculusOct17
import Calderon.CollaboratorFixedDirichletRegularityOct17
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open EnergyBridge DirichletFamily

-- BEFORE-only exact public type. No Lean proof/source authorization.
theorem exists_uniform_dilated_metric_buffered_harmonic_jet_bound
    (a : MatrixField) (ha : IsAdmissibleMetric a) (B : ℝ) (hB : 0 < B) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧
      ∀ (n : ℕ) (d : ℝ), 0 < d →
      ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, lambda ∈ Icc (0 : ℝ) lambda0 →
      ∀ D : Set R3, IsOpen D → D ⊆ ball (0 : R3) B →
      ∀ f : R3 → ℝ, ContDiffOn ℝ ∞ f D →
      (∀ x ∈ D,
        divCoeffGrad (principalCoefficient (fun y : R3 => a (lambda • y))) f x = 0) →
      MemLp f 2 ((volume : Measure R3).restrict D) →
      ∀ z : R3, closedBall z d ⊆ D →
        ‖iteratedFDeriv ℝ n f z‖ ≤
          C * (eLpNorm f 2 ((volume : Measure R3).restrict D)).toReal := by
  classical
  -- B1: the spatial cutoff precedes every derivative order and buffer.
  let lambda0 : ℝ := min 1 (1 / (B + 1))
  have hBp : 0 < B + 1 := by linarith
  have hLambda0 : 0 < lambda0 :=
    lt_min zero_lt_one (div_pos zero_lt_one hBp)
  have hLambda0One : lambda0 ≤ 1 := min_le_left _ _
  have hLambda0B : lambda0 * B < 1 := by
    have hSmall : lambda0 * (B + 1) ≤ 1 :=
      (le_div_iff₀ hBp).mp (min_le_right 1 (1 / (B + 1)))
    nlinarith only [hSmall, hLambda0]
  refine ⟨lambda0, hLambda0, hLambda0One, ?_⟩
  intro n d hd
  let rho : ℝ := min (d / 4) (1 / 8)
  have hRho : 0 < rho := lt_min (by linarith only [hd]) (by norm_num)
  have hRhoD : rho ≤ d / 4 := min_le_left _ _
  have hRhoMax : rho ≤ (1 / 8 : ℝ) := min_le_right _ _
  have hTwoRho : 2 * rho < d := by linarith only [hRhoD, hd]
  obtain ⟨Cn, hCn, hNative⟩ :=
    ExteriorSource.exists_uniform_radiusTwoScaledMetric_harmonic_jet_bound
      fixedSobolevCalculus fixedDirichletRegularity a ha n
  let s : ℝ := Real.sqrt (rho ^ 3)
  have hRhoPow : 0 < rho ^ n := pow_pos hRho n
  have hRhoCube : 0 < rho ^ 3 := pow_pos hRho 3
  have hs : 0 < s := Real.sqrt_pos.mpr hRhoCube
  let C : ℝ := Cn / (rho ^ n * s)
  have hC : 0 < C := div_pos hCn (mul_pos hRhoPow hs)
  refine ⟨C, hC, ?_⟩
  intro lambda hLambda D hD hDB f hSmooth hPDE hMem z hBuffer
  -- B2: positive affine normalization inside the original open domain.
  have hzD : z ∈ D := hBuffer (mem_closedBall_self hd.le)
  have hzB : ‖z‖ < B := mem_ball_zero_iff.mp (hDB hzD)
  have hRoom : ball z (2 * rho) ⊆ D := by
    intro x hx
    apply hBuffer
    exact mem_closedBall.mpr ((mem_ball.mp hx).le.trans hTwoRho.le)
  let U : R3 → ℝ := fun w => f (z + rho • w)
  have hMaps (w : R3) (hw : w ∈ ball (0 : R3) 2) : z + rho • w ∈ D := by
    apply hRoom
    change dist (z + rho • w) z < 2 * rho
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hRho]
    simpa only [mul_comm] using
      mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hw) hRho
  have hAffine : ContDiff ℝ ∞ (fun w : R3 => z + rho • w) :=
    (contDiff_const (c := z)).add (contDiff_const_smul rho)
  have hU : ContDiffOn ℝ ∞ U (ball (0 : R3) 2) :=
    hSmooth.comp hAffine.contDiffOn hMaps
  have hCenter : ‖lambda • z‖ ≤ (5 / 4 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hLambda.1]
    have hBound : lambda * ‖z‖ ≤ lambda0 * B :=
      mul_le_mul hLambda.2 hzB.le (norm_nonneg z) hLambda0.le
    exact hBound.trans (hLambda0B.le.trans (by norm_num))
  have hScaleLo : 0 ≤ lambda * rho := mul_nonneg hLambda.1 hRho.le
  have hScaleHi : lambda * rho ≤ (1 / 4 : ℝ) := by
    have hLambdaOne : lambda ≤ 1 := hLambda.2.trans hLambda0One
    have hBound : lambda * rho ≤ rho := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hLambdaOne hRho.le
    exact hBound.trans (hRhoMax.trans (by norm_num))
  have ht : (lambda • z, lambda * rho) ∈
      closedBall (0 : R3) (5 / 4 : ℝ) ×ˢ Icc (0 : ℝ) (1 / 4 : ℝ) :=
    ⟨mem_closedBall_zero_iff.mpr hCenter, hScaleLo, hScaleHi⟩
  -- B3: exact raw coefficient composition and total affine divergence.
  let A : MatrixField := principalCoefficient (fun y : R3 => a (lambda • y))
  have hCoeff :
      (fun w : R3 => principalCoefficient a (lambda • z + (lambda * rho) • w)) =
        (fun w : R3 => A (z + rho • w)) := by
    funext w
    change principalCoefficient a (lambda • z + (lambda * rho) • w) =
      principalCoefficient a (lambda • (z + rho • w))
    rw [smul_add, mul_smul]
  have hUnitPDE (w : R3) (hw : w ∈ (ballOpens : Set R3)) :
      divCoeffGrad
        (fun x => principalCoefficient a ((lambda • z) + (lambda * rho) • x)) U w = 0 := by
    have hw2 : w ∈ ball (0 : R3) 2 :=
      (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hw
    rw [hCoeff]
    change divCoeffGrad (fun x => A (z + rho • x))
      (fun x => f (z + rho • x)) w = 0
    rw [Jets.divCoeffGrad_comp_affine A f z hRho.ne', hPDE _ (hMaps w hw2), mul_zero]
  -- B4: apply the already proved all-solution cap at the native origin.
  have hPoint := hNative (lambda • z, lambda * rho) ht U hU hUnitPDE
    (0 : R3) (mem_closedBall_self (by norm_num))
  -- B5: identify exactly the same ordinary L2 norm and affine rho^3 factor.
  let nu : Measure R3 := (volume : Measure R3).restrict D
  let N : ℝ := (eLpNorm f 2 nu).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  let q : Lp ℝ 2 nu := hMem.toLp f
  have hqNorm : ‖q‖ = N := by
    simpa only [q, N] using (Lp.norm_toLp f hMem)
  have hqAE : (q : R3 → ℝ) =ᵐ[nu] f := hMem.coeFn_toLp
  have hIntegral : (∫ x in D, f x ^ 2) = N ^ 2 := by
    calc
      (∫ x in D, f x ^ 2) = ∫ x, (q x) ^ 2 ∂nu := by
        apply integral_congr_ae
        filter_upwards [hqAE] with x hx
        exact congrArg (fun t : ℝ => t ^ 2) hx.symm
      _ = ‖q‖ ^ 2 := by
        simpa only [L2.inner_def, Real.inner_apply, ← pow_two] using
          (real_inner_self_eq_norm_sq q)
      _ = N ^ 2 := by rw [hqNorm]
  have hChange : rho ^ 3 * (∫ w in (ballOpens : Set R3), U w ^ 2) =
      ∫ x in ball z rho, f x ^ 2 := by
    have hc := (Affine.mp_restrict hRho (Affine.isAff_ball z hRho)).integral_comp
      (Affine.measurableEmbedding_aff z hRho) (fun x => f x ^ 2)
    rw [integral_smul_measure] at hc
    have hBallO : (Affine.ballO z rho : Set R3) = ball z rho := rfl
    simpa only [U, Affine.aff, hBallO, Affine.sc,
      ENNReal.toReal_ofReal (pow_nonneg hRho.le 3), smul_eq_mul] using hc
  have hBallD : ball z rho ⊆ D := by
    intro x hx
    apply hBuffer
    exact mem_closedBall.mpr ((mem_ball.mp hx).le.trans (by linarith only [hRhoD, hd]))
  have hMeasure : (volume : Measure R3).restrict (ball z rho) ≤ nu :=
    Measure.restrict_mono_set volume hBallD
  have hLocalIntegral : (∫ x in ball z rho, f x ^ 2) ≤ N ^ 2 := by
    rw [← hIntegral]
    exact integral_mono_measure hMeasure (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
      hMem.integrable_sq
  have hIU : 0 ≤ ∫ w in (ballOpens : Set R3), U w ^ 2 :=
    integral_nonneg fun w => sq_nonneg (U w)
  have hSqrtMul : Real.sqrt (∫ w in (ballOpens : Set R3), U w ^ 2) * s ≤ N := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hs.le) hN).mp
    rw [mul_pow, Real.sq_sqrt hIU, show s ^ 2 = rho ^ 3 from Real.sq_sqrt hRhoCube.le]
    calc
      (∫ w in (ballOpens : Set R3), U w ^ 2) * rho ^ 3 =
          rho ^ 3 * (∫ w in (ballOpens : Set R3), U w ^ 2) := mul_comm _ _
      _ = ∫ x in ball z rho, f x ^ 2 := hChange
      _ ≤ N ^ 2 := hLocalIntegral
  -- B6: the same finite Frechet operator norm scales only by positive rho^n.
  have hJet := iteratedFDeriv_comp_positive_affine_dilation n rho hRho z (0 : R3) f
    (by simpa only [smul_zero, add_zero] using
      hSmooth.contDiffAt (hD.mem_nhds hzD))
  have hNormJet : ‖iteratedFDeriv ℝ n U (0 : R3)‖ =
      rho ^ n * ‖iteratedFDeriv ℝ n f z‖ := by
    simpa only [U, smul_zero, add_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos hRhoPow] using congrArg norm hJet
  rw [hNormJet] at hPoint
  have hFinal : ‖iteratedFDeriv ℝ n f z‖ * (rho ^ n * s) ≤ Cn * N := by
    calc
      ‖iteratedFDeriv ℝ n f z‖ * (rho ^ n * s) =
          (rho ^ n * ‖iteratedFDeriv ℝ n f z‖) * s := by ring
      _ ≤ (Cn * Real.sqrt (∫ w in (ballOpens : Set R3), U w ^ 2)) * s :=
        mul_le_mul_of_nonneg_right hPoint hs.le
      _ = Cn * (Real.sqrt (∫ w in (ballOpens : Set R3), U w ^ 2) * s) := mul_assoc _ _ _
      _ ≤ Cn * N := mul_le_mul_of_nonneg_left hSqrtMul hCn.le
  calc
    ‖iteratedFDeriv ℝ n f z‖ ≤ (Cn * N) / (rho ^ n * s) :=
      (le_div_iff₀ (mul_pos hRhoPow hs)).mpr hFinal
    _ = C * (eLpNorm f 2 ((volume : Measure R3).restrict D)).toReal := by
      dsimp only [C, N, nu]
      ring


end OAI.AnisotropicCalderon.Regularity
