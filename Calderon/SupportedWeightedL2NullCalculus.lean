import Calderon.SupportedFiniteClmWeightedL2Convergence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ReferenceDensityBounds WeightedBaseSpectral

/-- An error sequence with one compact support and vanishing actual weighted
L2 norm. This is derived data, not a uniform estimate. -/
structure SupportedWeightedL2Null
    {V : Type*} [NormedAddCommGroup V] (g : MatrixField) (L q : ℝ)
    (S : Set R3) (E : ℕ → R3 → V) : Prop where
  continuous : ∀ n, Continuous (E n)
  support : ∀ n, tsupport (E n) ⊆ S
  tendsto : Tendsto (fun n : ℕ => ∫ y, referenceDensityFamily g L (q,y) * ‖E n y‖^2)
    atTop (𝓝 0)

namespace SupportedWeightedL2Null
variable {ι V W : Type*} [Fintype ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {g : MatrixField} (hg : IsAdmissibleMetric g) {L q : ℝ}
  {S : Set R3} (hS : IsCompact S)
include hg hS

/-- The compact coefficient bound is derived on S; it may depend on S. -/
theorem finite_clm (E : ι → ℕ → R3 → V)
    (hE : ∀ i, SupportedWeightedL2Null g L q S (E i))
    (A : ι → R3 → V →L[ℝ] W)
    (hA : ∀ i, ∀ y ∈ S, ContinuousAt (A i) y) :
    SupportedWeightedL2Null g L q S (fun n y => ∑ i, A i y (E i n y)) := by
  let F : ℕ → R3 → W := fun n y => ∑ i, A i y (E i n y)
  have hCont (n : ℕ) : Continuous (F n) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    by_cases hy : y ∈ S
    · apply tendsto_finsetSum
      intro i hi
      exact (hA i y hy).clm_apply ((hE i).continuous n).continuousAt
    · have hZero : F n =ᶠ[𝓝 y] (fun _ => (0 : W)) := by
        have hEach : ∀ᶠ z in 𝓝 y, ∀ i : ι, E i n z = 0 := by
          apply Filter.eventually_all.mpr
          intro i
          exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hy ((hE i).support n h))
        filter_upwards [hEach] with z hz
        simp only [F,hz,map_zero,Finset.sum_const_zero]
      exact continuousAt_const.congr_of_eventuallyEq hZero
  have hSupp (n : ℕ) : tsupport (F n) ⊆ S := by
    apply closure_minimal ?_ hS.isClosed
    intro y hy
    by_contra hOutside
    have hz (i : ι) : E i n y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hOutside ((hE i).support n h))
    exact hy (by simp only [F,hz,map_zero,Finset.sum_const_zero])
  exact ⟨hCont,hSupp,tendsto_integral_supported_finite_clm_of_integral_tendsto
    g hg L q S hS E (fun i => (hE i).continuous) (fun i => (hE i).support)
      A hA (fun i => (hE i).tendsto)⟩

theorem clm {E : ℕ → R3 → V} (hE : SupportedWeightedL2Null g L q S E)
    (A : R3 → V →L[ℝ] W) (hA : ∀ y ∈ S, ContinuousAt A y) :
    SupportedWeightedL2Null g L q S (fun n y => A y (E n y)) := by
  have h := finite_clm hg hS (fun _ : Unit => E) (fun _ => hE)
    (fun _ : Unit => A) (fun _ => hA)
  simpa only [Fintype.sum_unique] using h

theorem add {E F : ℕ → R3 → V}
    (hE : SupportedWeightedL2Null g L q S E) (hF : SupportedWeightedL2Null g L q S F) :
    SupportedWeightedL2Null g L q S (fun n y => E n y + F n y) := by
  let U : Bool → ℕ → R3 → V := fun b => if b then E else F
  have hU : ∀ b, SupportedWeightedL2Null g L q S (U b) := by
    intro b
    cases b
    · exact hF
    · exact hE
  have h := finite_clm hg hS U hU (fun _ _ => ContinuousLinearMap.id ℝ V)
    (fun _ _ _ => continuousAt_const)
  simpa only [U,Fintype.sum_bool,ContinuousLinearMap.id_apply,ite_true,ite_false,Bool.false_eq_true] using h

theorem neg {E : ℕ → R3 → V} (hE : SupportedWeightedL2Null g L q S E) :
    SupportedWeightedL2Null g L q S (fun n y => -E n y) := by
  have h := clm hg hS hE (fun _ => -(ContinuousLinearMap.id ℝ V))
    (fun _ _ => continuousAt_const)
  simpa only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.id_apply] using h

theorem sub {E F : ℕ → R3 → V}
    (hE : SupportedWeightedL2Null g L q S E) (hF : SupportedWeightedL2Null g L q S F) :
    SupportedWeightedL2Null g L q S (fun n y => E n y - F n y) := by
  simpa only [sub_eq_add_neg] using add hg hS hE (neg hg hS hF)

theorem smul {E : ℕ → R3 → V} (hE : SupportedWeightedL2Null g L q S E)
    (a : R3 → ℝ) (ha : ∀ y ∈ S, ContinuousAt a y) :
    SupportedWeightedL2Null g L q S (fun n y => a y • E n y) := by
  have h := clm hg hS hE (fun y => a y • ContinuousLinearMap.id ℝ V)
    (fun y hy => (ha y hy).smul continuousAt_const)
  simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply] using h

theorem sum (E : ι → ℕ → R3 → V)
    (hE : ∀ i, SupportedWeightedL2Null g L q S (E i)) :
    SupportedWeightedL2Null g L q S (fun n y => ∑ i, E i n y) := by
  simpa only [ContinuousLinearMap.id_apply] using
    finite_clm hg hS E hE (fun _ _ => ContinuousLinearMap.id ℝ V)
      (fun _ _ _ => continuousAt_const)

end SupportedWeightedL2Null
end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
