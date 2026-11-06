import Calderon.NativeH2SixComponentBound

/-! EXPANSION.json precedes the actual finite-vector L6 reconstruction estimate. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open MetricVolume
open EnergyBridge
local instance : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩

theorem norm_nativeCompactH2_gradient_six_le
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (K : Set R3)
    (hK : IsCompact K) (hKB : K ⊆ (ballOpens : Set R3))
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 U x = 0) :
    ‖(memLp_nativeCompactH2_gradient_six hcalc U K hK hKB hU).toLp
      (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U))‖ ≤
      ∑ i : Fin 3, ‖coordinateVector i‖ *
        (SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal *
          (‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖U‖)) := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  let c (i : Fin 3) : Lp ℝ 6 μ :=
    (memLp_nativeCompactH2_gradient_coordinate_six hcalc U K hK hKB hU i).toLp
      (fun x : R3 => (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) i)
  let L (i : Fin 3) : ℝ →L[ℝ] R3 := ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector i)
  let v (i : Fin 3) : Lp R3 6 μ := (L i).compLp (c i)
  have hc (i : Fin 3) : (c i : R3 → ℝ) =ᵐ[μ]
      (fun x : R3 => (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) i) :=
    MemLp.coeFn_toLp (memLp_nativeCompactH2_gradient_coordinate_six hcalc U K hK hKB hU i)
  have hv (i : Fin 3) : (v i : R3 → R3) =ᵐ[μ]
      (fun x : R3 => (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) i • coordinateVector i) := by
    filter_upwards [(L i).coeFn_compLp (c i),hc i] with x hx hi
    simpa only [L,ContinuousLinearMap.toSpanSingleton_apply,Function.comp_apply,hi] using hx
  have heq : (memLp_nativeCompactH2_gradient_six hcalc U K hK hKB hU).toLp
      (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U)) = ∑ i : Fin 3, v i := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_nativeCompactH2_gradient_six hcalc U K hK hKB hU),
      Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin 3)) v,
      (Filter.eventually_all_finset (Finset.univ : Finset (Fin 3))).mpr
        (fun i _ => hv i)] with x hx hsum hall
    rw [hx]
    have hpoint : (∑ i : Fin 3, v i) x =
        ∑ i : Fin 3, (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) i • coordinateVector i := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro i hi
      exact hall i hi
    rw [hpoint]
    symm
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,coordinateVector] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x)
  rw [heq]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  calc
    ‖v i‖ ≤ ‖L i‖ * ‖c i‖ := (L i).norm_compLp_le (c i)
    _ ≤ ‖L i‖ *
        (SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal *
          (‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖U‖)) :=
      mul_le_mul_of_nonneg_left
        (norm_nativeCompactH2_gradient_coordinate_six_le hcalc U K hK hKB hU i) (norm_nonneg _)
    _ = _ := by dsimp only [L]; rw [ContinuousLinearMap.norm_toSpanSingleton]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
