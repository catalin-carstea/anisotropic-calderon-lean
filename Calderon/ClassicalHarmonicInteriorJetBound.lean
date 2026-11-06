import Calderon.SmoothHarmonicNativeWeak
import Calderon.CollaboratorInteriorEstimateOct17
import Calderon.CollaboratorSmoothRepOct17

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ContDiff Distributions Gradient Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE EnergyBridge
open _root_.OAI.AnisotropicCalderon.Affine

/-- For a fixed coefficient the interior jet constant is chosen before the classical solution. -/
theorem exists_classical_harmonic_interior_jet_bound
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (hpos : ∀ z, (A z).PosDef) (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ U : R3 → ℝ,
      ContDiffOn ℝ ∞ U (ball (0 : R3) 2) →
      (∀ z ∈ (ballOpens : Set R3), divCoeffGrad A U z = 0) →
      ∀ x ∈ closedBall (0 : R3) (1/4 : ℝ),
        ‖iteratedFDeriv ℝ n U x‖ ≤
          Cn * Real.sqrt (∫ z in (ballOpens : Set R3), U z ^ 2) := by
  obtain ⟨CI, hCI, hInterior⟩ := interior_estimate (0 : R3)
    (r₁ := (3/4 : ℝ)) (r₂ := 1) (by norm_num) (by norm_num) hA hpos (n + 2)
  have hUnitDomain : ballO (0 : R3) (1 : ℝ) = ballOpens := rfl
  rw [hUnitDomain] at hInterior
  obtain ⟨CS, hSobolev⟩ := SmoothRepAux.deriv_bound n (1/8 : ℝ) (by norm_num)
  let Ω : Opens R3 := ballO (0 : R3) (3/4 : ℝ)
  let V : Opens R3 := ballO (0 : R3) (1/2 : ℝ)
  have hVΩ : V ≤ Ω := ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 3/4)
  let T : Wkp (volume : Measure R3) Ω 2 (n + 2) →L[ℝ]
      Wkp (volume : Measure R3) V 2 (n + 2) := Wkp.restrictL hVΩ (n + 2)
  let CR : ℝ := ‖T‖
  let Cn : ℝ := (|CS| + 1) * (CR + 1) * (CI + 1)
  have hCR : 0 ≤ CR := norm_nonneg T
  have hCn : 0 < Cn := mul_pos
    (mul_pos (by positivity) (by dsimp only [CR]; positivity)) (by linarith)
  refine ⟨Cn, hCn, ?_⟩
  intro U hU hPDE x hx
  obtain ⟨v, hv, _hgrad, hTest, _hEnergy⟩ :=
    exists_native_weak_solution_of_contDiffOn hA (by norm_num : 1 < (2 : ℝ)) hU hPDE
  obtain ⟨W, hW, hWn⟩ := hInterior v hTest
  let vValue : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    W1p.value (Omega := ballOpens) v
  have hvValue : (vValue : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] U := hv
  have hWValue : (Wkp.value (n + 2) W : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict Ω] (vValue : R3 → ℝ) := hW
  have hWNorm : ‖W‖ ≤ CI * ‖vValue‖ := hWn
  let χ : ContDiffBump (0 : R3) := ⟨(1/2 : ℝ), (5/8 : ℝ), by norm_num, by norm_num⟩
  have hχSupp : tsupport (χ : R3 → ℝ) ⊆ ball (0 : R3) 2 := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by norm_num : (5/8 : ℝ) < 2)
  let h : R3 → ℝ := fun z => χ z * U z
  have hh : ContDiff ℝ ∞ h := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ ball (0 : R3) 2
    · exact χ.contDiff.contDiffAt.mul (hU.contDiffAt (isOpen_ball.mem_nhds hz))
    · have hzχ : z ∉ tsupport (χ : R3 → ℝ) := fun hs => hz (hχSupp hs)
      have he : h =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzχ] with t ht
        change χ t = 0 at ht
        exact (congrArg (fun a : ℝ => a * U t) ht).trans (zero_mul _)
      have hZero : ContDiffAt ℝ ∞ (fun _ : R3 => (0 : ℝ)) z := contDiffAt_const
      exact hZero.congr_of_eventuallyEq he
  have hVunit : (V : Set R3) ⊆ (ballOpens : Set R3) :=
    ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)
  have hValue : (Wkp.value (n + 2) (T W) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict V] h := by
    have hTv := Wkp.value_restrictL_ae hVΩ (n + 2) W
    have hWv := ae_restrict_of_ae_restrict_of_subset
      (show (V : Set R3) ⊆ (Ω : Set R3) from hVΩ) hWValue
    have hvV := ae_restrict_of_ae_restrict_of_subset hVunit hvValue
    filter_upwards [hTv, hWv, hvV, ae_restrict_mem V.isOpen.measurableSet] with z htz hwz hvz hz
    rw [htz, hwz, hvz]
    exact ((congrArg (fun a : ℝ => a * U z)
      (χ.one_of_mem_closedBall (ball_subset_closedBall hz))).trans (one_mul _)).symm
  have hRoom : ball x (1/8 : ℝ) ⊆ (V : Set R3) := by
    intro z hz
    have hxNorm : ‖x‖ ≤ (1/4 : ℝ) := mem_closedBall_zero_iff.mp hx
    have hzDist : dist z x < (1/8 : ℝ) := mem_ball.mp hz
    apply mem_ball_zero_iff.mpr
    have hTriangle : ‖z‖ ≤ dist z x + ‖x‖ := by
      simpa only [dist_zero_right] using dist_triangle z x (0 : R3)
    linarith
  have hJet := hSobolev (n + 2) (by omega) V (T W) h hh hValue x hRoom
  have hxInner : x ∈ ball (0 : R3) (1/2 : ℝ) :=
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) (by norm_num))
  have hGerm : h =ᶠ[𝓝 x] U := by
    filter_upwards [isOpen_ball.mem_nhds hxInner] with z hz
    exact (congrArg (fun a : ℝ => a * U z)
      (χ.one_of_mem_closedBall (ball_subset_closedBall hz))).trans (one_mul _)
  have hDerivative : iteratedFDeriv ℝ n h x = iteratedFDeriv ℝ n U x :=
    (hGerm.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
  have hNorm : ‖vValue‖ =
      Real.sqrt (∫ z in (ballOpens : Set R3), U z ^ 2) := by
    have hIntegral : (∫ z in (ballOpens : Set R3), U z ^ 2) = ‖vValue‖ ^ 2 := by
      calc
        _ = ∫ z in (ballOpens : Set R3), (vValue z) ^ 2 := by
          apply integral_congr_ae
          filter_upwards [hvValue] with z hz
          exact congrArg (fun a : ℝ => a ^ 2) hz.symm
        _ = _ := W1p.integral_value_sq_eq_norm_value_sq v
    rw [hIntegral, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hRestrictNorm : ‖T W‖ ≤ (CR + 1) * (CI + 1) * ‖vValue‖ := by
    calc
      ‖T W‖ ≤ CR * ‖W‖ := T.le_opNorm W
      _ ≤ CR * (CI * ‖vValue‖) := mul_le_mul_of_nonneg_left hWNorm hCR
      _ = (CR * CI) * ‖vValue‖ := (mul_assoc _ _ _).symm
      _ ≤ ((CR + 1) * (CI + 1)) * ‖vValue‖ := by
        gcongr <;> linarith
  calc
    ‖iteratedFDeriv ℝ n U x‖ = ‖iteratedFDeriv ℝ n h x‖ := congrArg norm hDerivative.symm
    _ ≤ CS * ‖T W‖ := hJet
    _ ≤ (|CS| + 1) * ‖T W‖ :=
      mul_le_mul_of_nonneg_right ((le_abs_self CS).trans (by linarith)) (norm_nonneg _)
    _ ≤ (|CS| + 1) * ((CR + 1) * (CI + 1) * ‖vValue‖) :=
      mul_le_mul_of_nonneg_left hRestrictNorm (by positivity)
    _ = Cn * Real.sqrt (∫ z in (ballOpens : Set R3), U z ^ 2) := by
      rw [← hNorm]
      dsimp only [Cn]
      ring

end OAI.AnisotropicCalderon.Regularity
#print axioms OAI.AnisotropicCalderon.Regularity.exists_classical_harmonic_interior_jet_bound
