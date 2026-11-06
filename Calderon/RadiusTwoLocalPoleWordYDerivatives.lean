import Calderon.RadiusTwoLocalPoleWordClosedSpan
import Calderon.RadiusTwoNativeWordFrechetFieldGraphs
import Mathlib.Analysis.Normed.Group.Submodule

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds
attribute [local instance] Classical.propDecidable

theorem exists_radiusTwo_local_poleWord_Y_derivatives
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
      let Frows : O → Lp ℝ 2 ν := fun p => R (K ⟨p,(hOB p.property).1⟩)
      let Y : Submodule ℝ (Lp ℝ 2 ν) :=
        (Submodule.span ℝ (Set.range Frows)).topologicalClosure
      ∃ D : O → List (Fin 3) → Y,
        (∀ p : O, ∀ w : List (Fin 3),
          ((D p w : Y) : Lp ℝ 2 ν) =ᵐ[ν] (fun z =>
            if hz : z ∈ (radiusTwoOpens : Set R3) then
              coordinateFieldWordPartial w (radiusTwoKernelPoleSection G ⟨z,hz⟩) p else 0) ∧
          ‖D p w‖ ≤ measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M w.length) ∧
        (∀ p : O, ((D p [] : Y) : Lp ℝ 2 ν) = Frows p) ∧
        ∀ w : List (Fin 3), ∀ p : O,
          let Dw : R3 → Y := fun q => if hq : q ∈ O then D ⟨q,hq⟩ w else 0
          let A : R3 →L[ℝ] Y :=
            ∑ i : Fin 3, (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).smulRight (D p (i::w))
          HasFDerivAt Dw A (p : R3) ∧
          ‖A‖ ≤ 3 * (measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M (w.length+1)) ∧
          ∀ v : R3, ∀ᵐ z ∂ν, ∀ hz : z ∈ S,
            ((A v : Y) : Lp ℝ 2 ν) z =
              fderiv ℝ (coordinateFieldWordPartial w
                (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩)) (p : R3) v := by
  intro ν
  have hAll := exists_radiusTwo_local_poleWord_classes_in_closedSpan
    hreg hcalc g hg K G hData S hS hSB x hx
  rcases hAll with ⟨r,hr,hClosed,M,hM,hWords,hAll⟩
  refine ⟨r,hr,hClosed,M,hM,hWords,?_⟩
  intro O hOB R Frows Y
  let D : O → List (Fin 3) → Y := fun p w =>
    ⟨Classical.choose (hAll p w), (Classical.choose_spec (hAll p w)).2.2⟩
  have hD (p : O) (w : List (Fin 3)) :
      ((D p w : Y) : Lp ℝ 2 ν) =ᵐ[ν] (fun z =>
        if hz : z ∈ (radiusTwoOpens : Set R3) then
          coordinateFieldWordPartial w (radiusTwoKernelPoleSection G ⟨z,hz⟩) p else 0) ∧
      ‖D p w‖ ≤ measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M w.length :=
    ⟨(Classical.choose_spec (hAll p w)).1, (Classical.choose_spec (hAll p w)).2.1⟩
  have hGraphS (p : O) (w : List (Fin 3)) : ∀ᵐ z ∂ν, ∀ hz : z ∈ S,
      ((D p w : Y) : Lp ℝ 2 ν) z = coordinateFieldWordPartial w
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) p := by
    filter_upwards [(hD p w).1] with z hz hzS
    simpa only [dif_pos (hSB hzS)] using hz
  have hBase (p : O) : ((D p [] : Y) : Lp ℝ 2 ν) = Frows p := by
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
  refine ⟨D,hD,hBase,?_⟩
  intro w p Dw A
  let FX : R3 → Lp ℝ 2 ν := fun q => ((Dw q : Y) : Lp ℝ 2 ν)
  let DX : Fin 3 → Lp ℝ 2 ν := fun i => ((D p (i::w) : Y) : Lp ℝ 2 ν)
  let AX : R3 →L[ℝ] Lp ℝ 2 ν :=
    ∑ i : Fin 3, (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).smulRight (DX i)
  have hIncl : Y.subtypeL.comp A = AX := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, A, AX, _root_.sum_apply,
      ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj, map_sum, map_smul,
      DX, Submodule.subtypeL_apply]
    exact Filter.EventuallyEq.rfl
  have hInput (a : R3) (ha : a ∈ O) : ∀ᵐ z ∂ν, ∀ hz : z ∈ S,
      FX a z = coordinateFieldWordPartial w
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) a := by
    simpa only [FX, Dw, dif_pos ha] using hGraphS ⟨a,ha⟩ w
  have hSecond (z : R3) (hz : z ∈ S) (a : R3) (ha : a ∈ O) (i j : Fin 3) :
      ‖coordinateFieldWordPartial (j::i::w)
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) a‖ ≤ M (w.length+2) := by
    simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd, Real.norm_eq_abs] using
      hWords z hz a ha (j::i::w)
  have hAmbient := hasFDerivAt_radiusTwo_nativeWord_Lp_family
    hreg hcalc g hg K G hData S hS hSB O isOpen_ball (convex_ball x (r/2)) hOB
    w (M (w.length+2)) (hM (w.length+2)) hSecond FX hInput
    (p : R3) p.property DX (fun i => hGraphS p (i::w))
  have hNorm (q : R3) : ‖Dw q - Dw p - A (q-p)‖ =
      ‖FX q - FX p - AX (q-p)‖ := by
    calc
      ‖Dw q - Dw p - A (q-p)‖ =
          ‖Y.subtypeL (Dw q - Dw p - A (q-p))‖ :=
        (Submodule.norm_coe (Dw q - Dw p - A (q-p))).symm
      _ = ‖FX q - FX p - AX (q-p)‖ := by
        rw [map_sub, map_sub]
        change ‖FX q - FX p - (Y.subtypeL.comp A) (q-p)‖ = _
        rw [hIncl]
  have hYDerivative : HasFDerivAt Dw A (p : R3) := by
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    filter_upwards [hAmbient.isLittleO.bound hε] with q hq
    rw [hNorm q]
    exact hq
  have hColumn (i : Fin 3) : A (coordinateDirection i) = D p (i::w) := by
    fin_cases i <;> simp [A, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
      EuclideanSpace.coe_proj, coordinateDirection, Fin.sum_univ_three, Pi.single_apply]
  have hOpNorm : ‖A‖ ≤
      3 * (measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M (w.length+1)) := by
    apply norm_clm_le_three_mul_of_coordinate_bound A _
      (mul_nonneg (by positivity) (hM (w.length+1)))
    intro i
    rw [hColumn i]
    simpa only [List.length_cons] using (hD p (i::w)).2
  refine ⟨hYDerivative,hOpNorm,?_⟩
  intro v
  have hInclValue : ((A v : Y) : Lp ℝ 2 ν) = AX v :=
    congrArg (fun T : R3 →L[ℝ] Lp ℝ 2 ν => T v) hIncl
  have hAXvalue : AX v = ∑ i : Fin 3, v i • DX i := by
    simp only [AX, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
      EuclideanSpace.coe_proj]
  rw [hInclValue, hAXvalue]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin 3 => v i • DX i),
    ae_all_iff.2 (fun i : Fin 3 => Lp.coeFn_smul (v i) (DX i)),
    ae_all_iff.2 (fun i : Fin 3 => hGraphS p (i::w))] with z hSum hSmul hDz hzS
  change (∑ i : Fin 3, v i • DX i) z = ∑ i : Fin 3, (v i • DX i) z at hSum
  rw [hSum]
  calc
    (∑ i : Fin 3, (v i • DX i) z) =
        ∑ i : Fin 3, v i * coordinateFieldWordPartial (i::w)
          (radiusTwoKernelPoleSection G ⟨z,hSB hzS⟩) p := by
      apply Finset.sum_congr rfl
      intro i _
      have h := hSmul i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      rw [h]
      change v i * ((D p (i::w) : Y) : Lp ℝ 2 ν) z = _
      rw [hDz i hzS]
    _ = fderiv ℝ (coordinateFieldWordPartial w
        (radiusTwoKernelPoleSection G ⟨z,hSB hzS⟩)) p v := by
      symm
      simpa only [coordinateFieldWordPartial, smul_eq_mul] using
        ActualReferenceDecomposition.fderiv_apply_eq_coordinate_sum
          (coordinateFieldWordPartial w (radiusTwoKernelPoleSection G ⟨z,hSB hzS⟩)) p v

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_local_poleWord_Y_derivatives
