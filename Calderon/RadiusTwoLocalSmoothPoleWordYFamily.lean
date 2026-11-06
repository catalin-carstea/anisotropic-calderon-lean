import Calderon.RadiusTwoLocalPoleWordYDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds
attribute [local instance] Classical.propDecidable

theorem exists_radiusTwo_local_smooth_poleWord_Y_family
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
        let Dw : List (Fin 3) → R3 → Y :=
          fun w q => if hq : q ∈ O then D ⟨q,hq⟩ w else 0
        (∀ w : List (Fin 3), ContDiffOn ℝ (∞ : ℕ∞ω) (Dw w) O) ∧
        ContDiffOn ℝ (∞ : ℕ∞ω) (fun q =>
          if hq : q ∈ (radiusTwoOpens : Set R3) then R (K ⟨q,hq⟩) else 0) O ∧
        ∀ w : List (Fin 3), ∀ p : O,
          let A : R3 →L[ℝ] Y :=
            ∑ i : Fin 3, (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).smulRight (D p (i::w))
          HasFDerivAt (Dw w) A (p : R3) ∧
          ‖A‖ ≤ 3 * (measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M (w.length+1)) ∧
          ∀ v : R3, ∀ᵐ z ∂ν, ∀ hz : z ∈ S,
            ((A v : Y) : Lp ℝ 2 ν) z =
              fderiv ℝ (coordinateFieldWordPartial w
                (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩)) (p : R3) v := by
  intro ν
  have hFamily := exists_radiusTwo_local_poleWord_Y_derivatives
    hreg hcalc g hg K G hData S hS hSB x hx
  rcases hFamily with ⟨r,hr,hClosed,M,hM,hWords,hFamily⟩
  refine ⟨r,hr,hClosed,M,hM,hWords,?_⟩
  intro O hOB R Frows Y
  rcases hFamily with ⟨D,hD,hBase,hJets⟩
  refine ⟨D,hD,hBase,?_⟩
  intro Dw
  let A : List (Fin 3) → R3 → R3 →L[ℝ] Y := fun w q =>
    ∑ i : Fin 3, (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).smulRight (Dw (i::w) q)
  have hDerivative (w : List (Fin 3)) (q : R3) (hq : q ∈ O) :
      HasFDerivAt (Dw w) (A w q) q := by
    simpa only [A, Dw, dif_pos hq] using (hJets w ⟨q,hq⟩).1
  have hFinite : ∀ n : ℕ, ∀ w : List (Fin 3),
      ContDiffOn ℝ (n : ℕ∞ω) (Dw w) O := by
    intro n
    induction n with
    | zero =>
      intro w
      apply contDiffOn_zero.2
      intro q hq
      exact (hDerivative w q hq).continuousAt.continuousWithinAt
    | succ n ih =>
      intro w
      have hA : ContDiffOn ℝ (n : ℕ∞ω) (A w) O := by
        change ContDiffOn ℝ (n : ℕ∞ω)
          (fun q => ∑ i : Fin 3,
            (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).smulRight (Dw (i::w) q)) O
        apply ContDiffOn.sum
        intro i _
        have hConst : ContDiffOn ℝ (n : ℕ∞ω)
            (fun _ : R3 => (EuclideanSpace.proj i : R3 →L[ℝ] ℝ)) O :=
          contDiffOn_const
        exact hConst.smulRight (ih (i::w))
      have hSucc : ContDiffOn ℝ ((n : ℕ∞ω)+1) (Dw w) O := by
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
          (n := (n : ℕ∞ω)) (isOpen_ball.uniqueDiffOn : UniqueDiffOn ℝ O)).2
        refine ⟨by simp, A w, hA, ?_⟩
        intro q hq
        exact (hDerivative w q hq).hasFDerivWithinAt
      simpa only [Nat.cast_add, Nat.cast_one] using hSucc
  have hInfinity (w : List (Fin 3)) : ContDiffOn ℝ (∞ : ℕ∞ω) (Dw w) O :=
    contDiffOn_infty.2 (fun n => hFinite n w)
  have hIncluded : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun q => Y.subtypeL (Dw [] q)) O :=
    Y.subtypeL.contDiff.fun_comp_contDiffOn (hInfinity [])
  have hRows : ContDiffOn ℝ (∞ : ℕ∞ω) (fun q =>
      if hq : q ∈ (radiusTwoOpens : Set R3) then R (K ⟨q,hq⟩) else 0) O := by
    apply hIncluded.congr
    intro q hq
    simpa only [Dw, Frows, dif_pos hq, dif_pos (hOB hq).1,
      Submodule.subtypeL_apply] using (hBase ⟨q,hq⟩).symm
  refine ⟨hInfinity,hRows,?_⟩
  intro w p
  simpa only [Dw] using hJets w p

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_local_smooth_poleWord_Y_family
