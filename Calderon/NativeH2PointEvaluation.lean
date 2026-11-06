import Calderon.NativeH2LocalPointBound
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Full EXPANSION.json precedes this derived native point functional. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem eqOn_ball_of_native_inner_ae_eq
    (a : ℝ) (ha1 : a < 1) (F G : R3 → ℝ) (hF : Continuous F) (hG : Continuous G)
    (hAE : ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
      y ∈ closedBall (0 : R3) a → F y = G y) :
    EqOn F G (ball (0 : R3) a) := by
  have hμ : ∀ᵐ y ∂(volume : Measure R3),
      y ∈ (ballOpens : Set R3) → y ∈ closedBall (0 : R3) a → F y = G y :=
    (ae_restrict_iff' ballOpens.isOpen.measurableSet).mp hAE
  have hBall : F =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] G := by
    change ∀ᵐ y ∂(volume : Measure R3).restrict (ball (0 : R3) a), F y = G y
    rw [ae_restrict_iff' isOpen_ball.measurableSet]
    filter_upwards [hμ] with y hy hyA
    have hyB : y ∈ (ballOpens : Set R3) :=
      ball_subset_ball ha1.le hyA
    exact hy hyB (ball_subset_closedBall hyA)
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3))
    hBall isOpen_ball hF.continuousOn hG.continuousOn

theorem exists_nativeH2_innerPointEvaluation
    (hcalc : FixedSobolevCalculus) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (x : R3) (hx : x ∈ ball (0 : R3) a) :
    ∃ L : BallSobolev 2 →L[ℝ] ℝ, ∀ (U : BallSobolev 2) (F : R3 → ℝ),
      Continuous F →
      (∀ᵐ y ∂(volume : Measure R3).restrict ballOpens, y ∈ closedBall (0 : R3) a →
        F y = TauCeti.Wkp.value 2 U y) → L U = F x := by
  classical
  obtain ⟨C,hC,hRep⟩ :=
    exists_uniform_bound_continuous_representative_on_innerBall_of_nativeH2 hcalc a ha ha1
  choose F hFC hFA hFB using hRep
  let P : BallSobolev 2 →ₗ[ℝ] ℝ :=
    { toFun := fun U => F U x
      map_add' := by
        intro U V
        have hVal : (TauCeti.Wkp.value 2 (U+V) : R3 → ℝ)
            =ᵐ[(volume : Measure R3).restrict ballOpens]
              (fun y : R3 => TauCeti.Wkp.value 2 U y + TauCeti.Wkp.value 2 V y) := by
          rw [TauCeti.Wkp.value_add]
          filter_upwards [Lp.coeFn_add (TauCeti.Wkp.value 2 U) (TauCeti.Wkp.value 2 V)] with y hy
          simpa only [Pi.add_apply] using hy
        have hAE : ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
            y ∈ closedBall (0 : R3) a → F (U+V) y = F U y + F V y := by
          filter_upwards [hVal,hFA (U+V),hFA U,hFA V] with y hy hUV hU hV hyA
          rw [hUV hyA,hU hyA,hV hyA]
          exact hy
        exact eqOn_ball_of_native_inner_ae_eq a ha1 (F (U+V))
          (fun y => F U y + F V y) (hFC (U+V)) ((hFC U).add (hFC V)) hAE hx
      map_smul' := by
        intro c U
        change F (c • U) x = c * F U x
        have hVal : (TauCeti.Wkp.value 2 (c • U) : R3 → ℝ)
            =ᵐ[(volume : Measure R3).restrict ballOpens]
              (fun y : R3 => c * TauCeti.Wkp.value 2 U y) := by
          rw [TauCeti.Wkp.value_smul]
          filter_upwards [Lp.coeFn_smul c (TauCeti.Wkp.value 2 U)] with y hy
          simpa only [Pi.smul_apply,smul_eq_mul] using hy
        have hAE : ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
            y ∈ closedBall (0 : R3) a → F (c • U) y = c * F U y := by
          filter_upwards [hVal,hFA (c • U),hFA U] with y hy hcU hU hyA
          rw [hcU hyA,hU hyA]
          exact hy
        exact eqOn_ball_of_native_inner_ae_eq a ha1 (F (c • U))
          (fun y => c * F U y) (hFC (c • U)) (continuous_const.mul (hFC U)) hAE hx }
  let L : BallSobolev 2 →L[ℝ] ℝ := P.mkContinuous C (fun U => by
    simpa only [P,LinearMap.coe_mk,AddHom.coe_mk,Real.norm_eq_abs] using hFB U x)
  refine ⟨L,?_⟩
  intro U G hG hGA
  have hAE : ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
      y ∈ closedBall (0 : R3) a → F U y = G y := by
    filter_upwards [hFA U,hGA] with y hU hGy hyA
    exact (hU hyA).trans (hGy hyA).symm
  exact eqOn_ball_of_native_inner_ae_eq a ha1 (F U) G (hFC U) hG hAE hx

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
