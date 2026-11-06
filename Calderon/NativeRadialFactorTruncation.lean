import Calderon.NativeSmoothMultiplicationTrace
import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Expanded before source in EXPANSION-native-radial-factor-specific-dct-author-v002.json. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def nativeRadialFactorSmoothData : SmoothData :=
  ⟨fun x : R3 => 1-‖x‖^2, contDiff_const.sub (contDiff_norm_sq ℝ)⟩

def nativeConstantOneSmoothData : SmoothData := ⟨fun _ => 1, contDiff_const⟩

def nativeRadialFactorTruncation (t : ℝ) : BallH1 :=
  TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))
    (smoothSobolev nativeRadialFactorSmoothData-t • smoothSobolev nativeConstantOneSmoothData)

lemma value_nativeRadialFactorShift_ae (t : ℝ) :
    TauCeti.W1p.value
      (smoothSobolev nativeRadialFactorSmoothData-t • smoothSobolev nativeConstantOneSmoothData)
      =ᵐ[((volume : Measure R3).restrict ballOpens)] fun x => 1-‖x‖^2-t := by
  let u := smoothSobolev nativeRadialFactorSmoothData
  let one := smoothSobolev nativeConstantOneSmoothData
  have he : TauCeti.W1p.value (u-t • one) =
      TauCeti.W1p.value u-t • TauCeti.W1p.value one := by
    simp only [← TauCeti.W1p.valueL_apply,map_sub,map_smul]
  change TauCeti.W1p.value (u-t • one) =ᵐ[_] _
  rw [he]
  filter_upwards [Lp.coeFn_sub (TauCeti.W1p.value u) (t • TauCeti.W1p.value one),
    Lp.coeFn_smul t (TauCeti.W1p.value one),
    value_smoothSobolev_ae nativeRadialFactorSmoothData,
    value_smoothSobolev_ae nativeConstantOneSmoothData] with x hsub hsmul hu hone
  rw [hsub]
  change TauCeti.W1p.value u x-(t • TauCeti.W1p.value one) x = _
  rw [hsmul]
  change TauCeti.W1p.value u x-t * TauCeti.W1p.value one x = _
  rw [hu,hone]
  simp only [nativeRadialFactorSmoothData,nativeConstantOneSmoothData,mul_one]

lemma value_nativeRadialFactorTruncation_ae (t : ℝ) :
    TauCeti.W1p.value (nativeRadialFactorTruncation t)
      =ᵐ[((volume : Measure R3).restrict ballOpens)] fun x => max (1-‖x‖^2-t) 0 := by
  unfold nativeRadialFactorTruncation
  rw [TauCeti.W1p.value_posPart]
  filter_upwards [Lp.coeFn_posPart (TauCeti.W1p.value
    (smoothSobolev nativeRadialFactorSmoothData-t • smoothSobolev nativeConstantOneSmoothData)),
    value_nativeRadialFactorShift_ae t] with x hpos hshift
  exact hpos.trans (congrArg (fun y : ℝ => max y 0) hshift)

lemma nativeRadialFactorTruncation_mem_zero (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    nativeRadialFactorTruncation t ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let K : Set R3 := closedBall (0 : R3) (Real.sqrt (1-t))
  have hs : (Real.sqrt (1-t))^2 = 1-t := Real.sq_sqrt (by linarith)
  have hr : Real.sqrt (1-t) < 1 := by
    nlinarith [Real.sqrt_nonneg (1-t)]
  have hKB : K ⊆ (ballOpens : Set R3) := by
    intro x hx
    change dist x (0 : R3) < 1
    exact (Metric.mem_closedBall.mp hx).trans_lt hr
  apply TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))
    (isCompact_closedBall (0 : R3) (Real.sqrt (1-t))) hKB
  filter_upwards [value_nativeRadialFactorTruncation_ae t] with x hx
  intro hxK
  have hnorm : Real.sqrt (1-t) < ‖x‖ := by
    have hdist : ¬ dist x (0 : R3) ≤ Real.sqrt (1-t) := hxK
    simpa only [dist_zero_right] using lt_of_not_ge hdist
  rw [hx]
  apply max_eq_right
  nlinarith [norm_nonneg x,Real.sqrt_nonneg (1-t)]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeRadialFactorSmoothData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeConstantOneSmoothData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeRadialFactorTruncation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_nativeRadialFactorShift_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_nativeRadialFactorTruncation_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeRadialFactorTruncation_mem_zero
