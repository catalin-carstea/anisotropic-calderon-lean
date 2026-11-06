import Calderon.RadiusTwoLocalPoleWordLpClasses
import Calderon.RadiusTwoNativeWordCoordinateSecant
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds
attribute [local instance] Classical.propDecidable

theorem exists_radiusTwo_local_poleWord_classes_in_closedSpan
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (hS : IsCompact S) (hSB : S ⊆ (radiusTwoOpens : Set R3))
    (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3) \ S) :
    let ν : Measure R3 := ((volume : Measure R3).restrict radiusTwoOpens).restrict S
    ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ hClosed : closedBall x r ⊆ (radiusTwoOpens : Set R3) \ S,
      ∃ M : ℕ → ℝ, (∀ n : ℕ, 0 ≤ M n) ∧
        (∀ z : R3, ∀ hz : z ∈ S, ∀ p ∈ ball x (r/2), ∀ w : List (Fin 3),
          |coordinateFieldWordPartial w
            (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) p| ≤ M w.length) ∧
      let O : Set R3 := ball x (r/2)
      let hOB : O ⊆ (radiusTwoOpens : Set R3) \ S := fun p hp =>
        hClosed (closedBall_subset_closedBall (by linarith : r/2 ≤ r)
          (ball_subset_closedBall hp))
      let R : RadiusTwoL2 →L[ℝ] Lp ℝ 2 ν := MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
        ((volume : Measure R3).restrict radiusTwoOpens) 2 S
      let F : O → Lp ℝ 2 ν := fun p => R (K ⟨p,(hOB p.property).1⟩)
      let Y : Submodule ℝ (Lp ℝ 2 ν) := (Submodule.span ℝ (Set.range F)).topologicalClosure
      ∀ p : O, ∀ w : List (Fin 3),
        ∃ D : Lp ℝ 2 ν,
          (D : R3 → ℝ) =ᵐ[ν] (fun z => if hz : z ∈ (radiusTwoOpens : Set R3) then
            coordinateFieldWordPartial w (radiusTwoKernelPoleSection G ⟨z,hz⟩) p else 0) ∧
          ‖D‖ ≤ measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M w.length ∧ D ∈ Y := by
  intro ν
  have hClasses := exists_radiusTwo_local_poleWord_Lp_classes
    hreg hcalc g hg K G hData S hS hSB x hx
  rcases hClasses with ⟨r,hr,hClosed,M,hM,hWords,hClasses⟩
  refine ⟨r,hr,hClosed,M,hM,hWords,?_⟩
  intro O hOB R F Y
  have hO : IsOpen O := isOpen_ball
  let D : O → List (Fin 3) → Lp ℝ 2 ν :=
    fun p w => Classical.choose (hClasses p p.property w)
  have hD (p : O) (w : List (Fin 3)) := Classical.choose_spec (hClasses p p.property w)
  have hGraphS (p : O) (w : List (Fin 3)) : ∀ᵐ z ∂ν, ∀ hz : z ∈ S,
      D p w z = coordinateFieldWordPartial w
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) p := by
    filter_upwards [(hD p w).1] with z hz hzS
    simpa only [dif_pos (hSB hzS)] using hz
  have hRows (p : O) : F p ∈ Y :=
    (Submodule.le_topologicalClosure _)
      (Submodule.subset_span (show F p ∈ Set.range F from ⟨p,rfl⟩))
  have hY : ∀ w : List (Fin 3), ∀ p : O, D p w ∈ Y := by
    intro w
    induction w with
    | nil =>
      intro p
      have hEq : D p [] = F p := by
        apply Lp.ext
        filter_upwards [hGraphS p [],
          radiusTwo_restricted_inverseSourceRow_value_ae g hg K G hData S
            ⟨p,(hOB p.property).1⟩,
          ae_restrict_mem hS.measurableSet] with z hDz hFz hzS
        rw [hDz hzS]
        change radiusTwoKernelPoleSection G ⟨z,hSB hzS⟩ p =
          (R (K ⟨p,(hOB p.property).1⟩)) z
        change (R (K ⟨p,(hOB p.property).1⟩)) z = G ⟨p,(hOB p.property).1⟩ z at hFz
        rw [hFz]
        simp only [radiusTwoKernelPoleSection, dif_pos (hOB p.property).1]
      rw [hEq]
      exact hRows p
    | cons i w ih =>
      intro p
      let e : R3 := coordinateDirection i
      obtain ⟨ε, hε, hBall⟩ : ∃ ε : ℝ, 0 < ε ∧ ball (p : R3) ε ⊆ O :=
        Metric.mem_nhds_iff.mp (hO.mem_nhds p.property)
      let δ : ℝ := ε / (2 * (1 + ‖e‖))
      have hDen : 0 < 2 * (1 + ‖e‖) := by positivity
      have hδ : 0 < δ := div_pos hε hDen
      have hδEq : δ * (2 * (1 + ‖e‖)) = ε := div_mul_cancel₀ ε (ne_of_gt hDen)
      have hδNorm : δ * ‖e‖ < ε := by nlinarith [mul_nonneg hδ.le (norm_nonneg e)]
      let t : ℕ → ℝ := fun n => δ / ((n : ℝ) + 1)
      have htPos (n : ℕ) : 0 < t n := div_pos hδ (by positivity)
      have htLe (n : ℕ) : t n ≤ δ := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
        nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) n)]
      have hLine (n : ℕ) : ∀ s ∈ Icc (0 : ℝ) (t n), (p : R3) + s • e ∈ O := by
        intro s hs
        apply hBall
        apply mem_ball_iff_norm.mpr
        have hSub : (p : R3) + s • e - p = s • e := by abel
        rw [hSub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        exact (mul_le_mul_of_nonneg_right (hs.2.trans (htLe n)) (norm_nonneg e)).trans_lt hδNorm
      let q (n : ℕ) : O := ⟨(p : R3) + t n • e, hLine n (t n) ⟨(htPos n).le,le_rfl⟩⟩
      let s : ℕ → Lp ℝ 2 ν := fun n => (t n)⁻¹ • (D (q n) w - D p w)
      have hBound (n : ℕ) : ‖s n - D p (i::w)‖ ≤
          measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M (w.length+2) * t n := by
        exact norm_radiusTwo_nativeWord_coordinateSecant_error_le
          hreg hcalc g hg K G hData S hS hSB O isOpen_ball hOB
          w (M (w.length+2)) (hM (w.length+2))
          (fun z hz a ha j => by
            simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
              hWords z hz a ha (j::j::w))
          ⟨p,(hOB p.property).1⟩ ⟨q n,(hOB (q n).property).1⟩ i (t n) (htPos n) rfl
          (hLine n) (D p w) (D (q n) w) (D p (i::w))
          (hGraphS p w) (hGraphS (q n) w) (hGraphS p (i::w))
      have htZero : Tendsto t atTop (𝓝 (0 : ℝ)) := by
        have h := (tendsto_const_nhds (x := δ)).mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa only [t, div_eq_mul_inv, one_div, one_mul, mul_zero] using h
      have hRight : Tendsto
          (fun n => measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M (w.length+2) * t n)
          atTop (𝓝 (0 : ℝ)) := by
        simpa only [mul_zero] using
          (tendsto_const_nhds
            (x := measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M (w.length+2))).mul htZero
      have hLimit : Tendsto s atTop (𝓝 (D p (i::w))) :=
        tendsto_iff_norm_sub_tendsto_zero.2
          (squeeze_zero (fun _ => norm_nonneg _) hBound hRight)
      have hsY (n : ℕ) : s n ∈ Y := Y.smul_mem _ (Y.sub_mem (ih (q n)) (ih p))
      exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
        hLimit (Eventually.of_forall hsY)
  intro p w
  exact ⟨D p w,(hD p w).1,(hD p w).2,hY w p⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_local_poleWord_classes_in_closedSpan
