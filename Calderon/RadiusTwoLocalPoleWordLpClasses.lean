import Calderon.RadiusTwoCompactDisjointPoleSectionWordBounds
import Calderon.RadiusTwoPoleWordFieldMeasurability
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds
attribute [local instance] Classical.propDecidable

theorem exists_radiusTwo_local_poleWord_Lp_classes
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (hS : IsCompact S) (hSB : S ⊆ (radiusTwoOpens : Set R3))
    (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3) \ S) :
    let ν : Measure R3 := ((volume : Measure R3).restrict radiusTwoOpens).restrict S
    ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ (radiusTwoOpens : Set R3) \ S ∧
      ∃ M : ℕ → ℝ, (∀ n : ℕ, 0 ≤ M n) ∧
        (∀ z : R3, ∀ hz : z ∈ S, ∀ p ∈ ball x (r/2), ∀ w : List (Fin 3),
          |coordinateFieldWordPartial w
            (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) p| ≤ M w.length) ∧
      ∀ p ∈ ball x (r/2), ∀ w : List (Fin 3),
        ∃ D : Lp ℝ 2 ν,
          (D : R3 → ℝ) =ᵐ[ν] (fun z => if hz : z ∈ (radiusTwoOpens : Set R3) then
            coordinateFieldWordPartial w (radiusTwoKernelPoleSection G ⟨z,hz⟩) p else 0) ∧
          ‖D‖ ≤ measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M w.length := by
  classical
  let μB : Measure R3 := (volume : Measure R3).restrict radiusTwoOpens
  let ν : Measure R3 := μB.restrict S
  have hμ : μB ≤ (volume : Measure R3) := Measure.restrict_le_self
  have hFiniteS : μB S < (⊤ : ENNReal) := (hμ S).trans_lt hS.measure_lt_top
  letI radiusTwoLocalPoleWordFiniteMeasure : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (ne_of_lt hFiniteS)
  have hBounds := exists_radiusTwo_compactDisjoint_poleSection_word_bounds
    hreg hcalc g hg K G hData S hS hSB x hx
  rcases hBounds with ⟨r, hr, hClosed, M, hM, hWords⟩
  refine ⟨r, hr, hClosed, M, hM, hWords, ?_⟩
  intro p hp w
  have hRoom : ball x (r/2) ⊆ (radiusTwoOpens : Set R3) \ S := by
    intro q hq
    exact hClosed (closedBall_subset_closedBall (by linarith : r/2 ≤ r)
      (ball_subset_closedBall hq))
  let d : R3 → ℝ := fun z => if hz : z ∈ (radiusTwoOpens : Set R3) then
    coordinateFieldWordPartial w (radiusTwoKernelPoleSection G ⟨z,hz⟩) p else 0
  have hMeasurable : AEStronglyMeasurable d ν :=
    aestronglyMeasurable_radiusTwo_poleSection_coordinateFieldWordPartial
      hreg hcalc g hg K G hData S hS.measurableSet hSB
      (ball x (r/2)) isOpen_ball hRoom w p hp
  have hBound : ∀ᵐ z ∂ν, ‖d z‖ ≤ M w.length := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    have h := hWords z hz p hp w
    simpa only [d, dif_pos (hSB hz), Real.norm_eq_abs] using h
  have hMem : MemLp d 2 ν := MemLp.of_bound hMeasurable (M w.length) hBound
  refine ⟨hMem.toLp d, hMem.coeFn_toLp, ?_⟩
  apply Lp.norm_le_of_ae_bound (hM w.length)
  filter_upwards [hMem.coeFn_toLp, hBound] with z hz hB
  rwa [hz]

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_local_poleWord_Lp_classes
