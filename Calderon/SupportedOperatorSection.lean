import Calderon.ActualPhysicalDensityProductsAdjointOperatorCore

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)

set_option Elab.async false

lemma contDiff_comp_clm_apply_of_tsupport_subset
    (U : Set R3) (hU : IsOpen U)
    (u : R3 → Hi) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (hsu : tsupport u ⊆ U)
    (Op : R3 → Hi →L[ℝ] Half) (hOp : ContDiffOn ℝ ∞ Op U)
    (lift : Half →L[ℝ] SphereL2) :
    let v : R3 → SphereL2 := fun x => lift (Op x (u x))
    ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ MemLp v 2 (volume : Measure R3) ∧
      tsupport v ⊆ tsupport u := by
  classical
  intro v
  have hZero (y : R3) (hy : y ∉ tsupport u) : v y = 0 := by
    have hz : u y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp only [v,hz,map_zero]
  have hSupport : tsupport v ⊆ tsupport u := by
    apply closure_minimal ?_ (isClosed_tsupport u)
    intro y hy
    by_contra hn
    exact hy (hZero y hn)
  have hv : ContDiff ℝ ∞ v := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport u
    · have hyU : y ∈ U := hsu hy
      have hAt : ContDiffAt ℝ ∞ (fun x : R3 => Op x (u x)) y :=
        (hOp.contDiffAt (hU.mem_nhds hyU)).clm_apply hu.contDiffAt
      exact lift.contDiff.contDiffAt.comp y hAt
    · have hEq : v =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereL2)) := by
        filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hy] with x hx
        exact hZero x hx
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : R3 => (0 : SphereL2)) y).congr_of_eventuallyEq hEq
  have hc : HasCompactSupport v :=
    hcu.of_isClosed_subset (isClosed_tsupport v) hSupport
  exact ⟨hv,hc,hv.continuous.memLp_of_hasCompactSupport hc,hSupport⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
