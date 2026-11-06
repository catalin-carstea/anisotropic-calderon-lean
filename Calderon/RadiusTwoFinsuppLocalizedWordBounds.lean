import Calderon.RadiusTwoFiniteRowLocalizedWordBounds
import Calderon.RadiusTwoNativeRestrictedRowGraphs
import Calderon.LocalCoordinateWordLinearity
import Calderon.ActualTwoMetricSeparatelySmoothSourceKernels
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Module.Basic

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets
  ActualReferenceLocalCoordinateWordJets

theorem exists_radiusTwo_finsupp_localized_word_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (η : ℕ → 𝓓(radiusTwoOpens, ℝ)) (S : Set R3) (hS : MeasurableSet S)
    (hSupp : ∀ j : ℕ, tsupport (η j : R3 → ℝ) ⊆ S)
    (hOne : ∀ j : ℕ, ∀ z ∈ tsupport (η j : R3 → ℝ), η (j+1) z = 1)
    (P : Set R3) (hPB : P ⊆ (radiusTwoOpens : Set R3) \ S)
    (a₀ : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ < 1)
    (Z : Set R3) (hZ : IsOpen Z) (hZBall : Z ⊆ ball (0 : R3) (2*a₀))
    (hEtaOne : ∀ z ∈ Z, η 0 z = 1) :
    let ν : Measure R3 := ((volume : Measure R3).restrict radiusTwoOpens).restrict S
    let R : RadiusTwoL2 →L[ℝ] Lp ℝ 2 ν := MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
      ((volume : Measure R3).restrict radiusTwoOpens) 2 S
    let F : P → Lp ℝ 2 ν := fun p => R (K ⟨p,(hPB p.property).1⟩)
    ∃ C : ℕ → ℝ, (∀ n : ℕ, 0 ≤ C n) ∧
      ∀ (c : P →₀ ℝ) (w : List (Fin 3)) (z : R3), z ∈ Z →
        |Finsupp.linearCombination ℝ
          (fun p : P => coordinateFieldWordPartial w (G ⟨p,(hPB p.property).1⟩) z) c| ≤
          C w.length * ‖Finsupp.linearCombination ℝ F c‖ := by
  classical
  intro ν R F
  have hFinite := exists_radiusTwo_finiteRow_localized_word_bound
    hreg hcalc g hg K G hData η S hS hSupp hOne a₀ ha₀ ha₀1 Z hZ hZBall hEtaOne
  rcases hFinite with ⟨C,hC,hFinite⟩
  have hZB : Z ⊆ (radiusTwoOpens : Set R3) := by
    intro z hz
    change z ∈ ball (0 : R3) 2
    exact ball_subset_ball (by linarith : 2*a₀ ≤ 2) (hZBall hz)
  have hZS : Z ⊆ S := by
    intro z hz
    apply hSupp 0
    apply subset_tsupport (η 0 : R3 → ℝ)
    change η 0 z ≠ 0
    rw [hEtaOne z hz]
    norm_num
  have hSmooth := IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth
    hreg hcalc g hg K G hData
  refine ⟨C,hC,?_⟩
  intro c w z hz
  let m : ℕ := Fintype.card ↥c.support
  let q : Fin m → P := fun i => ((Fintype.equivFin ↥c.support).symm i).val
  let a : Fin m → ℝ := fun i => c (q i)
  let p : Fin m → (radiusTwoOpens : Set R3) := fun i => ⟨q i,(hPB (q i).property).1⟩
  have hEnum {V : Type} [AddCommMonoid V] (f : P → V) :
      (∑ i : Fin m, f (q i)) = ∑ t ∈ c.support, f t := by
    have hIndex : (∑ i : Fin m, f (q i)) = ∑ t : ↥c.support, f t.val := by
      simpa only [q] using
        (Fintype.equivFin ↥c.support).symm.sum_comp (fun t : ↥c.support => f t.val)
    exact hIndex.trans (Finset.sum_coe_sort (f := f) (s := c.support))
  have hPole (i : Fin m) (j : ℕ) : (p i : R3) ∉ tsupport (η j : R3 → ℝ) := by
    intro h
    exact (hPB (q i).property).2 (hSupp j h)
  have hRows (i : Fin m) : ContDiffOn ℝ ∞ (G (p i)) Z := by
    apply (hSmooth.2.1 (p i)).mono
    intro y hy
    refine ⟨hZB hy,?_⟩
    intro hEqual
    have hpS : (p i : R3) ∈ S := (mem_singleton_iff.mp hEqual) ▸ hZS hy
    exact (hPB (q i).property).2 hpS
  have hPoint := hFinite m a p hPole w z hz
  have hWordSum : coordinateFieldWordPartial w
      (fun y => ∑ i : Fin m, a i * G (p i) y) z =
      Finsupp.linearCombination ℝ
        (fun t : P => coordinateFieldWordPartial w (G ⟨t,(hPB t.property).1⟩) z) c := by
    calc
      coordinateFieldWordPartial w (fun y => ∑ i : Fin m, a i * G (p i) y) z =
          ∑ i : Fin m, coordinateFieldWordPartial w (fun y => a i • G (p i) y) z := by
        simpa only [smul_eq_mul] using
          coordinateFieldWordPartial_sum_of_isOpen w (fun i y => a i • G (p i) y)
            Z hZ (fun i => (hRows i).const_smul (a i)) z hz
      _ = ∑ i : Fin m, a i * coordinateFieldWordPartial w (G (p i)) z := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [smul_eq_mul] using congrFun
          (coordinateFieldWordPartial_const_smul w (a i) (G (p i))) z
      _ = ∑ t ∈ c.support, c t • coordinateFieldWordPartial w
          (G ⟨t,(hPB t.property).1⟩) z := by
        simpa only [a, p, smul_eq_mul] using hEnum
          (fun t => c t • coordinateFieldWordPartial w (G ⟨t,(hPB t.property).1⟩) z)
      _ = _ := rfl
  have hRestrict : R (∑ i : Fin m, a i • K (p i)) =
      Finsupp.linearCombination ℝ F c := by
    calc
      R (∑ i : Fin m, a i • K (p i)) = ∑ i : Fin m, a i • F (q i) := by
        simp only [map_sum, map_smul, F, p]
      _ = ∑ t ∈ c.support, c t • F t := by
        simpa only [a] using hEnum (fun t => c t • F t)
      _ = _ := rfl
  have hSquare := norm_sq_radiusTwo_restricted_finiteRow K S hS m a p
  have hRoot : Real.sqrt (∫ y in (radiusTwoOpens : Set R3) ∩ S,
      ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) y)^2 ∂(volume : Measure R3)) =
      ‖Finsupp.linearCombination ℝ F c‖ := by
    calc
      Real.sqrt (∫ y in (radiusTwoOpens : Set R3) ∩ S,
          ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) y)^2 ∂(volume : Measure R3)) =
          Real.sqrt (‖R (∑ i : Fin m, a i • K (p i))‖^2) :=
        congrArg Real.sqrt hSquare.symm
      _ = ‖R (∑ i : Fin m, a i • K (p i))‖ := Real.sqrt_sq (norm_nonneg _)
      _ = ‖Finsupp.linearCombination ℝ F c‖ := congrArg norm hRestrict
  rw [hWordSum, hRoot] at hPoint
  exact hPoint

theorem denseRange_radiusTwo_restrictedRow_linearCombination
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (S P : Set R3) (hPB : P ⊆ (radiusTwoOpens : Set R3)) :
    let ν : Measure R3 := ((volume : Measure R3).restrict radiusTwoOpens).restrict S
    let R : RadiusTwoL2 →L[ℝ] Lp ℝ 2 ν := MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
      ((volume : Measure R3).restrict radiusTwoOpens) 2 S
    let F : P → Lp ℝ 2 ν := fun p => R (K ⟨p,hPB p.property⟩)
    let Y : Submodule ℝ (Lp ℝ 2 ν) :=
      (Submodule.span ℝ (Set.range F)).topologicalClosure
    let liftRows : P → Y := fun p => ⟨F p,
      (Submodule.le_topologicalClosure _)
        (Submodule.subset_span (show F p ∈ Set.range F from ⟨p,rfl⟩))⟩
    DenseRange (Finsupp.linearCombination ℝ liftRows) := by
  classical
  intro ν R F Y liftRows
  let e := Finsupp.linearCombination ℝ liftRows
  let e0 := Finsupp.linearCombination ℝ F
  have hValue : (fun y : Y => (y : Lp ℝ 2 ν)) ∘ e = e0 := by
    funext c
    change Y.subtypeL (e c) = e0 c
    simp only [e, e0, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, Submodule.subtypeL_apply, liftRows]
  have hImage : (fun y : Y => (y : Lp ℝ 2 ν)) '' Set.range e =
      (Submodule.span ℝ (Set.range F) : Set (Lp ℝ 2 ν)) := by
    rw [← Set.range_comp, hValue]
    change (LinearMap.range (Finsupp.linearCombination ℝ F) : Set (Lp ℝ 2 ν)) = _
    exact congrArg (fun Q : Submodule ℝ (Lp ℝ 2 ν) => (Q : Set (Lp ℝ 2 ν)))
      (Finsupp.range_linearCombination ℝ (v := F))
  change Dense (Set.range e)
  apply Subtype.dense_iff.2
  change (Y : Set (Lp ℝ 2 ν)) ⊆
    closure ((fun y : Y => (y : Lp ℝ 2 ν)) '' Set.range e)
  rw [hImage]
  change closure (Submodule.span ℝ (Set.range F) : Set (Lp ℝ 2 ν)) ⊆
    closure (Submodule.span ℝ (Set.range F) : Set (Lp ℝ 2 ν))
  exact subset_rfl

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_finsupp_localized_word_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.denseRange_radiusTwo_restrictedRow_linearCombination
