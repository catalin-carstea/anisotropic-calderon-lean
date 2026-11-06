import Calderon.NativeSmoothBoundaryTruncation
import Calderon.NativePositiveThresholdSequenceLimit
import Calderon.NativePositiveThresholdConstantShift

/-! EXPANSION.json precedes the actual constructive discharge of SmoothBoundaryZeroClosure. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.EnergyBridge
attribute [local irreducible] TauCeti.W1p.posPart

theorem nativeH1_posPart_sub_posPart_neg (u : BallH1) :
    TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) u -
      TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (-u) = u := by
  apply TauCeti.W1p.ext_value
  simp only [← TauCeti.W1p.valueL_apply, map_sub]
  simp only [TauCeti.W1p.valueL_apply, TauCeti.W1p.value_posPart]
  have hNeg : TauCeti.W1p.value (-u) = -TauCeti.W1p.value u :=
    map_neg (TauCeti.W1p.valueL) u
  rw [hNeg]
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (Lp.posPart (TauCeti.W1p.value u))
      (Lp.posPart (-TauCeti.W1p.value u)), Lp.coeFn_posPart (TauCeti.W1p.value u),
    Lp.coeFn_posPart (-TauCeti.W1p.value u), Lp.coeFn_neg (TauCeti.W1p.value u)] with x hSub hP hN hNegX
  rw [hSub,Pi.sub_apply,hP,hN,hNegX]
  simp only [Pi.neg_apply]
  by_cases hx : 0 ≤ TauCeti.W1p.value u x
  · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx)]
    ring
  · rw [max_eq_right (le_of_not_ge hx),max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
    ring

theorem smoothSobolev_posPart_mem_zero_of_sphere_zero
    (f : SmoothData) (hSphere : ∀ x : R3, ‖x‖ = 1 → f.1 x = 0) :
    TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (smoothSobolev f) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  let κ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hκPos : ∀ n, 0 < κ n := fun n => by dsimp only [κ]; positivity
  let U : ℕ → BallH1 := fun n => TauCeti.W1p.posPartAbove hp (hκPos n).le (smoothSobolev f)
  have hLimit : Tendsto U atTop (𝓝 (TauCeti.W1p.posPart hp (smoothSobolev f))) :=
    tendsto_nativeH1_posPartAbove_one_div_add (smoothSobolev f)
  have hMember : ∀ n, U n ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    intro n
    have hShift : U n = TauCeti.W1p.posPart hp
        (smoothSobolev f - κ n • smoothSobolev ⟨fun _ : R3 => (1 : ℝ),contDiff_const⟩) :=
      nativeH1_posPartAbove_eq_posPart_sub_constant (smoothSobolev f) (κ n) (hκPos n).le
    exact hShift.symm ▸ smoothSobolev_positive_boundary_truncation_mem_zero f hSphere (κ n) (hκPos n)
  exact (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).isClosed.mem_of_tendsto
    hLimit (Eventually.of_forall hMember)

theorem smoothBoundaryZeroClosure_constructive : SmoothBoundaryZeroClosure := by
  intro f hSphere
  let hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  let fn : SmoothData := ⟨-f.1,f.2.neg⟩
  have hNeg : smoothSobolev fn = -smoothSobolev f := by
    apply TauCeti.W1p.ext_value
    have hMap : TauCeti.W1p.value (-smoothSobolev f) =
        -TauCeti.W1p.value (smoothSobolev f) :=
      map_neg TauCeti.W1p.valueL (smoothSobolev f)
    rw [hMap]
    apply Lp.ext
    filter_upwards [value_smoothSobolev_ae fn,Lp.coeFn_neg (TauCeti.W1p.value (smoothSobolev f)),
      value_smoothSobolev_ae f] with x hfn hNegX hf
    rw [hfn,hNegX]
    simp only [fn,Pi.neg_apply]
    rw [hf]
  have hFnSphere : ∀ x : R3, ‖x‖ = 1 → fn.1 x = 0 := by
    intro x hx
    simpa only [fn,Pi.neg_apply,hSphere x hx,neg_zero]
  have hPlus := smoothSobolev_posPart_mem_zero_of_sphere_zero f hSphere
  have hMinus : TauCeti.W1p.posPart hp (-smoothSobolev f) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    rw [← hNeg]
    exact smoothSobolev_posPart_mem_zero_of_sphere_zero fn hFnSphere
  have hSub : TauCeti.W1p.posPart hp (smoothSobolev f) -
      TauCeti.W1p.posPart hp (-smoothSobolev f) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).sub_mem hPlus hMinus
  rw [nativeH1_posPart_sub_posPart_neg] at hSub
  exact hSub

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.nativeH1_posPart_sub_posPart_neg
#print axioms OAI.AnisotropicCalderon.EnergyBridge.smoothSobolev_posPart_mem_zero_of_sphere_zero
#print axioms OAI.AnisotropicCalderon.EnergyBridge.smoothBoundaryZeroClosure_constructive
