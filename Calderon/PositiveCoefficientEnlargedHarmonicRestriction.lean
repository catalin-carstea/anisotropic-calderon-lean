import Calderon.RawCoefficientHarmonicDilation
import Calderon.NativeInwardValuePullback

/-! EXPANSION.json precedes this actual fixed-datum enlarged harmonic realization.
The neighborhood lies in the common double-ball room. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Gradient Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem exists_positiveCoefficient_enlarged_harmonic_restriction
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData)
    (R : ℝ) (hR : 1 < R) (hR2 : R ≤ 2) :
    let AR : MatrixField := fun x => A (R • x)
    let hAR : ContDiff ℝ ∞ AR := hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff
    let hPosR : ∀ x, (AR x).PosDef := fun x => hPos (R • x)
    ∃ b' : ℝ, ∃ w : SmoothData, ∃ O : Set R3,
      R⁻¹ < b' ∧ b' < 1 ∧ 1 < R*b' ∧ HasCompactSupport w.1 ∧ IsOpen O ∧
      closedBall (0 : R3) 1 ⊆ O ∧ O ⊆ ball (0 : R3) (R*b') ∧ O ⊆ ball (0 : R3) 2 ∧
      (∀ x ∈ O, ConnectionError.coordinateFluxDivergence
        (fun y => MetricOperator.matrixOperatorMap (A y) (gradient w.1 y : R3)) x = 0) ∧
      nativeH1InwardDilation R⁻¹ (positiveCoefficientDirichletSolution AR hAR hPosR f) =
        smoothSobolev w := by
  classical
  dsimp only
  let q : ℝ := R⁻¹
  let AR : MatrixField := fun x => A (R • x)
  have hAR : ContDiff ℝ ∞ AR := hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff
  have hPosR : ∀ x, (AR x).PosDef := fun x => hPos (R • x)
  have hR0 : 0 < R := lt_trans (by norm_num) hR
  have hq0 : 0 < q := inv_pos.mpr hR0
  have hq1 : q < 1 := by
    dsimp only [q]
    rw [← one_div]
    exact (div_lt_one hR0).mpr hR
  have hqHalf : (1/2 : ℝ) ≤ q := by
    have h := one_div_le_one_div_of_le hR0 hR2
    simpa only [one_div,q] using h
  have hRq : R*q = 1 := mul_inv_cancel₀ hR0.ne'
  have hqR : q*R = 1 := inv_mul_cancel₀ hR0.ne'
  let b : ℝ := (q+1)/2
  let b' : ℝ := (q+b)/2
  have hqb : q < b := by dsimp only [b]; linarith
  have hb1 : b < 1 := by dsimp only [b]; linarith
  have hb0 : 0 < b := lt_trans hq0 hqb
  have hqb' : q < b' := by dsimp only [b']; linarith
  have hb'b : b' < b := by dsimp only [b']; linarith
  have hb'1 : b' < 1 := lt_trans hb'b hb1
  have hRoom : 1 < R*b' := by
    have h := mul_lt_mul_of_pos_left hqb' hR0
    simpa only [hRq] using h
  have hRoom2 : R*b' < 2 := by
    have h := mul_lt_mul_of_pos_left hb'1 hR0
    exact lt_of_lt_of_le (by simpa only [mul_one] using h) hR2
  obtain ⟨F,hF,hSmooth,hValue,hPDE⟩ :=
    exists_positiveCoefficientDirichletSolution_pointwise_equation_innerBall
      hcalc hreg τ0 AR hAR hPosR f b hb0 hb1
  let S : Set R3 := ball 0 (R*b')
  let U : R3 → ℝ := fun x => F (q • x)
  have hMaps : MapsTo (fun x : R3 => q • x) S (ball (0 : R3) b) := by
    intro x hx
    have hxN : ‖x‖ < R*b' := by simpa only [S,mem_ball,dist_zero_right] using hx
    have hSmall : q * ‖x‖ < b' := by
      have h := mul_lt_mul_of_pos_left hxN hq0
      simpa only [← mul_assoc,hqR,one_mul] using h
    simpa only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hq0] using
      hSmall.trans hb'b
  have hUSmooth : ContDiffOn ℝ ∞ U S :=
    hSmooth.comp (q • ContinuousLinearMap.id ℝ R3).contDiff.contDiffOn hMaps
  have hKS : closedBall (0 : R3) 1 ⊆ S := by
    intro x hx
    have hxN : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
    simpa only [S,mem_ball,dist_zero_right] using hxN.trans_lt hRoom
  have hCoeff : (fun y : R3 => AR (q • y)) = A := by
    funext y
    dsimp only [AR]
    rw [smul_smul,hRq,one_smul]
  have hCoeffPoint (y : R3) : AR (q • y) = A y := congrFun hCoeff y
  have hUPDE : ∀ x ∈ S, ConnectionError.coordinateFluxDivergence
      (fun y => MetricOperator.matrixOperatorMap (A y) (gradient U y : R3)) x = 0 := by
    intro x hx
    have h := ConnectionError.coordinateFluxDivergence_rawGradient_dilation_of_contDiffOn
      AR hAR q (ball (0 : R3) b) isOpen_ball F hSmooth x (hMaps hx)
    have hp : ConnectionError.coordinateFluxDivergence
        (fun y => MetricOperator.matrixOperatorMap (AR y) (gradient F y : R3)) (q • x) = 0 :=
      hPDE (q • x) (hMaps hx)
    rw [hp,mul_zero] at h
    simpa only [hCoeffPoint,U] using h
  obtain ⟨w,hCompact,hNear⟩ := DirichletFamily.exists_smoothData_eq_near_compact
    (closedBall (0 : R3) 1) S (isCompact_closedBall 0 1) isOpen_ball hKS U hUSmooth
  let G : Set R3 := {x | w.1 =ᶠ[𝓝 x] U}
  let O : Set R3 := S ∩ G
  have hGOpen : IsOpen G := isOpen_setOfPred_eventually_nhds
  have hKO : closedBall (0 : R3) 1 ⊆ O := fun x hx => ⟨hKS hx,hNear x hx⟩
  have hwEq : EqOn w.1 U (ballOpens : Set R3) := by
    intro x hx
    have hxK : x ∈ closedBall (0 : R3) 1 := by
      apply ball_subset_closedBall
      simpa only [coe_ballOpens,B] using hx
    exact (hNear x hxK).eq_of_nhds
  refine ⟨b',w,O,hqb',hb'1,hRoom,hCompact,isOpen_ball.inter hGOpen,hKO,
    (fun _ hx => hx.1),?_,?_,?_⟩
  · intro x hx
    have hxN : ‖x‖ < R*b' := by simpa only [S,mem_ball,dist_zero_right] using hx.1
    simpa only [mem_ball,dist_zero_right] using hxN.trans hRoom2
  · intro x hx
    exact (ConnectionError.coordinateFluxDivergence_rawGradient_congr_of_eventuallyEq
      A w.1 U x hx.2).trans (hUPDE x hx.1)
  · exact nativeH1InwardDilation_eq_smoothSobolev_of_innerRepresentative
      q b hqHalf hq1.le hqb (positiveCoefficientDirichletSolution AR hAR hPosR f)
      F hValue w hwEq

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_positiveCoefficient_enlarged_harmonic_restriction
