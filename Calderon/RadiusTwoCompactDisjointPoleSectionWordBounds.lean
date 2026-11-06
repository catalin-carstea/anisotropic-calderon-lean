import Calderon.RadiusTwoCompactPoleCutoffRoom
import Calderon.RadiusTwoFiniteRowLocalizedWordBounds
import Calderon.RadiusTwoCompactUniformInverseRowL2
import Calderon.ActualReferenceLocalCoordinateWordJets
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets
  ActualReferenceLocalCoordinateWordJets

theorem exists_radiusTwo_compactDisjoint_poleSection_word_bounds
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (hS : IsCompact S) (hSB : S ⊆ (radiusTwoOpens : Set R3))
    (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3) \ S) :
    ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ (radiusTwoOpens : Set R3) \ S ∧
      ∃ M : ℕ → ℝ, (∀ n : ℕ, 0 ≤ M n) ∧
        ∀ z : R3, ∀ hz : z ∈ S, ∀ p ∈ ball x (r/2), ∀ w : List (Fin 3),
          |coordinateFieldWordPartial w
            (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) p| ≤ M w.length := by
  classical
  have hRoom := exists_radiusTwo_compactPole_dyadic_cutoff_room S hS x hx
  rcases hRoom with ⟨r, hr, η, hClosed, hOne, hSupp, hNext, hAvoid, hSmall⟩
  let C : Set R3 := closedBall x r
  let O : Set R3 := ball x (r/2)
  have hCB : C ⊆ (radiusTwoOpens : Set R3) := fun y hy => (hClosed hy).1
  have hCompact : IsCompact (S ∪ C) := hS.union (isCompact_closedBall x r)
  have hUnionB : S ∪ C ⊆ (radiusTwoOpens : Set R3) := union_subset hSB hCB
  have hRows := exists_compact_uniform_radiusTwo_inverseSourceRow_L2_bound
    hreg hcalc g hg K G hData (S ∪ C) hCompact hUnionB
  rcases hRows with ⟨a₀, L, ha₀, ha₀1, hL, hUnionBall, hNorm⟩
  have hOC : O ⊆ C := by
    intro y hy
    exact closedBall_subset_closedBall (by linarith : r/2 ≤ r)
      (ball_subset_closedBall hy)
  have hOBall : O ⊆ ball (0 : R3) (2*a₀) :=
    fun y hy => hUnionBall (Or.inr (hOC hy))
  have hWords := exists_radiusTwo_finiteRow_localized_word_bound
    hreg hcalc g hg K G hData η C (isClosed_closedBall.measurableSet)
    hSupp hNext a₀ ha₀ ha₀1 O isOpen_ball hOBall (hOne 0)
  rcases hWords with ⟨CW, hCW, hWord⟩
  let M : ℕ → ℝ := fun n => CW n * L
  refine ⟨r, hr, hClosed, M, fun n => mul_nonneg (hCW n) hL, ?_⟩
  intro z hz p hp w
  let zB : (radiusTwoOpens : Set R3) := ⟨z,hSB hz⟩
  let I : ℝ := ∫ y in (radiusTwoOpens : Set R3) ∩ C,
    (K zB y)^2 ∂(volume : Measure R3)
  have hIntegrable : IntegrableOn (fun y => (K zB y)^2)
      (radiusTwoOpens : Set R3) (volume : Measure R3) := (Lp.memLp (K zB)).integrable_sq
  have hLocal : I ≤ ∫ y in radiusTwoOpens, (K zB y)^2 ∂(volume : Measure R3) := by
    exact setIntegral_mono_set hIntegrable
      (Eventually.of_forall (fun y => sq_nonneg (K zB y)))
      (Eventually.of_forall (fun y hy => hy.1))
  have hSquare : (∫ y in radiusTwoOpens, (K zB y)^2 ∂(volume : Measure R3)) =
      ‖K zB‖^2 := by
    calc
      (∫ y in radiusTwoOpens, (K zB y)^2 ∂(volume : Measure R3)) =
          ∫ y in radiusTwoOpens, ‖K zB y‖^2 ∂(volume : Measure R3) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => by
          change (K zB y)^2 = ‖K zB y‖^2
          rw [Real.norm_eq_abs, sq_abs])
      _ = ‖K zB‖^2 := Lp.integral_norm_sq_eq_norm_sq (K zB)
  have hSqrt : Real.sqrt I ≤ L := by
    calc
      Real.sqrt I ≤ Real.sqrt (‖K zB‖^2) := Real.sqrt_le_sqrt (hLocal.trans_eq hSquare)
      _ = ‖K zB‖ := Real.sqrt_sq (norm_nonneg _)
      _ ≤ L := hNorm zB (Or.inl hz)
  have hBound : |coordinateFieldWordPartial w (G zB) p| ≤ CW w.length * Real.sqrt I := by
    have h := hWord 1 (fun _ => (1 : ℝ)) (fun _ => zB)
      (fun _ j => hAvoid z hz j) w p hp
    simpa only [Fin.sum_univ_one, one_mul, one_smul] using h
  have hNear : radiusTwoKernelPoleSection G zB =ᶠ[𝓝 p] G zB := by
    filter_upwards [isOpen_ball.mem_nhds hp] with q hq
    have hqB : q ∈ (radiusTwoOpens : Set R3) := (hSmall hq).1
    change (if h : q ∈ (radiusTwoOpens : Set R3) then G ⟨q,h⟩ z else 0) = G zB q
    rw [dif_pos hqB]
    exact hData.2 ⟨q,hqB⟩ zB
  have hWordSame := (coordinateFieldWordPartial_eventuallyEq w hNear).eq_of_nhds
  calc
    |coordinateFieldWordPartial w (radiusTwoKernelPoleSection G zB) p| =
        |coordinateFieldWordPartial w (G zB) p| := congrArg abs hWordSame
    _ ≤ CW w.length * Real.sqrt I := hBound
    _ ≤ CW w.length * L := mul_le_mul_of_nonneg_left hSqrt (hCW w.length)
    _ = M w.length := rfl

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_compactDisjoint_poleSection_word_bounds
