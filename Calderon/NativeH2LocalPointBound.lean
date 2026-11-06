import Calderon.NativeH2CompactPointBoundTail

/-! EXPANSION.json precedes the actual local H2 point bound. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open MetricVolume
open EnergyBridge
local instance : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ((6 : NNReal) : ENNReal)) := ⟨by
  rw [ENNReal.coe_ofNat]
  norm_num⟩

theorem exists_uniform_bound_continuous_representative_on_innerBall_of_nativeH2
    (hcalc : FixedSobolevCalculus) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : BallSobolev 2,
      ∃ F : R3 → ℝ, Continuous F ∧
        (∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∈ closedBall (0 : R3) a →
          F x = TauCeti.Wkp.value 2 U x) ∧
        ∀ x : R3, |F x| ≤ C * ‖U‖ := by
  let b : ℝ := (a+1)/2
  let χ : ContDiffBump (0 : R3) :=
    ⟨(a+b)/2,b,by dsimp [b]; linarith,by dsimp [b]; linarith⟩
  let Cχ : SmoothCoefficientJets 3 := compactCoefficient 3 χ χ.contDiff χ.hasCompactSupport
  let T : BallSobolev 2 →L[ℝ] BallSobolev 2 := coefficientMultiplier hcalc 2 Cχ
  let S : ℝ := SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal
  let H : ℝ := S + ∑ i : Fin 3, ‖coordinateVector i‖ * (S * ‖unitBallCoordinateDerivativeL hcalc 1 i‖)
  have hS : 0 ≤ S := NNReal.coe_nonneg _
  have hH : 0 ≤ H := add_nonneg hS (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (norm_nonneg _) (mul_nonneg hS (norm_nonneg _))))
  let C : ℝ := ‖nativeSixMorreyL‖ * H * ‖T‖
  refine ⟨C,mul_nonneg (mul_nonneg (norm_nonneg _) hH) (norm_nonneg _),?_⟩
  intro U
  let V : BallSobolev 2 := T U
  let K : Set R3 := tsupport (χ : R3 → ℝ)
  have hK : IsCompact K := χ.hasCompactSupport
  have hKB : K ⊆ (ballOpens : Set R3) := by
    intro x hx
    have hnorm : ‖x‖ ≤ b := by
      simpa only [K,χ.tsupport_eq,mem_closedBall,dist_zero_right] using hx
    change dist x (0 : R3) < 1
    rw [dist_zero_right]
    dsimp only [b] at hnorm
    linarith
  have hValue : (TauCeti.Wkp.value 2 V : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
        (fun x : R3 => χ x * TauCeti.Wkp.value 2 U x) := by
    have hv := coefficientMultiplier_value_ae hcalc 2 Cχ U
    have hCχ : coefficientValue 3 Cχ = (χ : R3 → ℝ) := coefficientValue_compactCoefficient 3 _ _ _
    simpa only [V,T,hCχ] using hv
  have hVK : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 V x = 0 := by
    filter_upwards [hValue] with x hx hxK
    have hχ0 : χ x = (0 : ℝ) := (notMem_tsupport_iff_eventuallyEq.mp hxK).eq_of_nhds
    exact hx.trans ((congrArg (fun q : ℝ => q * TauCeti.Wkp.value 2 U x) hχ0).trans (zero_mul _))
  obtain ⟨F,hF,hRep,hBound⟩ :=
    exists_bounded_continuous_representative_of_nativeCompactH2 hcalc V K hK hKB hVK
  have hFirst : ‖TauCeti.Wkp.firstOrder 1 V‖ ≤ ‖V‖ := by
    change ‖TauCeti.Wkp.lowerOrder 1 V‖ ≤ ‖V‖
    exact TauCeti.Wkp.norm_lowerOrder_le 1 V
  have hSum : (∑ i : Fin 3, ‖coordinateVector i‖ *
      (S * (‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖V‖))) =
      (∑ i : Fin 3, ‖coordinateVector i‖ * (S * ‖unitBallCoordinateDerivativeL hcalc 1 i‖)) * ‖V‖ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hInside : S * ‖TauCeti.Wkp.firstOrder 1 V‖ +
      (∑ i : Fin 3, ‖coordinateVector i‖ * (S * (‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖V‖))) ≤
        H * ‖V‖ := by
    rw [hSum]
    dsimp only [H]
    rw [add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hFirst hS) le_rfl
  refine ⟨F,hF,?_,?_⟩
  · filter_upwards [hRep,hValue] with x hx hv hxA
    have hχ1 : χ x = (1 : ℝ) := χ.one_of_mem_closedBall (by
      change dist x (0 : R3) ≤ (a+b)/2
      have hxnorm : dist x (0 : R3) ≤ a := hxA
      dsimp only [b]
      linarith)
    exact hx.symm.trans (hv.trans ((congrArg (fun q : ℝ => q * TauCeti.Wkp.value 2 U x) hχ1).trans (one_mul _)))
  · intro x
    calc
      |F x| ≤ ‖nativeSixMorreyL‖ *
          (S * ‖TauCeti.Wkp.firstOrder 1 V‖ +
            ∑ i : Fin 3, ‖coordinateVector i‖ * (S * (‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖V‖))) := hBound x
      _ ≤ ‖nativeSixMorreyL‖ * (H * ‖V‖) := mul_le_mul_of_nonneg_left hInside (norm_nonneg _)
      _ ≤ ‖nativeSixMorreyL‖ * (H * (‖T‖ * ‖U‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (T.le_opNorm U) hH) (norm_nonneg _)
      _ = C * ‖U‖ := by dsimp only [C]; ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
