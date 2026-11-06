import Calderon.NativeCoordinateOperatorBounds
import Calderon.RadiusTwoNativeRestrictedRowGraphs
import Calderon.ActualTwoMetricSeparatelySmoothSourceKernels

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds
open ActualReferenceLocalCoordinateWordJets

lemma norm_radiusTwo_nativeWord_family_firstOrder_remainder_le
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (hS : IsCompact S) (hSB : S ⊆ (radiusTwoOpens : Set R3))
    (O : Set R3) (hO : IsOpen O) (hConvex : Convex ℝ O)
    (hOB : O ⊆ (radiusTwoOpens : Set R3) \ S) (w : List (Fin 3))
    (M : ℝ) (hM : 0 ≤ M)
    (hSecond : ∀ z : R3, ∀ hz : z ∈ S, ∀ a ∈ O, ∀ i j : Fin 3,
      ‖coordinateFieldWordPartial (j::i::w) (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) a‖ ≤ M)
    (F : R3 → Lp ℝ 2 (((volume : Measure R3).restrict radiusTwoOpens).restrict S))
    (hF : ∀ a ∈ O, ∀ᵐ z ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S),
      ∀ hz : z ∈ S, F a z = coordinateFieldWordPartial w
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) a)
    (p : R3) (hp : p ∈ O)
    (D : Fin 3 → Lp ℝ 2 (((volume : Measure R3).restrict radiusTwoOpens).restrict S))
    (hD : ∀ i : Fin 3, ∀ᵐ z ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S),
      ∀ hz : z ∈ S, D i z = coordinateFieldWordPartial (i::w)
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) p)
    (q : R3) (hq : q ∈ O) :
    let A := ∑ i : Fin 3, (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).smulRight (D i)
    ‖F q - F p - A (q-p)‖ ≤
      measureUnivNNReal (((volume : Measure R3).restrict radiusTwoOpens).restrict S) ^
        (2 : ENNReal).toReal⁻¹ * ((9*M)*‖q-p‖^2) := by
  classical
  intro A
  let μ : Measure R3 := (volume : Measure R3).restrict radiusTwoOpens
  let ν : Measure R3 := μ.restrict S
  have hμ : μ ≤ (volume : Measure R3) := Measure.restrict_le_self
  letI radiusTwoNativeWordFrechetFiniteMeasure : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (ne_of_lt ((hμ S).trans_lt hS.measure_lt_top))
  let f : R3 → R3 → ℝ := fun a z => if hz : z ∈ (radiusTwoOpens : Set R3) then
    coordinateFieldWordPartial w (radiusTwoKernelPoleSection G ⟨z,hz⟩) a else 0
  have hSmooth := IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth
    hreg hcalc g hg K G hData
  have hFields : ∀ᵐ z ∂ν,
      (∀ a ∈ O, DifferentiableAt ℝ (fun b => f b z) a) ∧
      (∀ a ∈ O, ∀ b ∈ O,
        ‖fderiv ℝ (fun c => f c z) a - fderiv ℝ (fun c => f c z) b‖ ≤
          (9*M)*‖a-b‖) := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hzS
    let zB : (radiusTwoOpens : Set R3) := ⟨z,hSB hzS⟩
    have hAvoid : O ⊆ (radiusTwoOpens : Set R3) \ {(z : R3)} := by
      intro a ha
      refine ⟨(hOB ha).1, ?_⟩
      intro haz
      exact (hOB ha).2 ((mem_singleton_iff.mp haz).symm ▸ hzS)
    have hWord : ContDiffOn ℝ ∞
        (coordinateFieldWordPartial w (radiusTwoKernelPoleSection G zB)) O :=
      contDiffOn_coordinateFieldWordPartial w _ O hO ((hSmooth.2.2 zB).mono hAvoid)
    have hValue : (fun a => f a z) =
        coordinateFieldWordPartial w (radiusTwoKernelPoleSection G zB) := by
      funext a
      simp only [f, dif_pos (hSB hzS), zB]
    rw [hValue]
    refine ⟨fun a ha => (hWord.contDiffAt (hO.mem_nhds ha)).differentiableAt (by simp), ?_⟩
    intro a ha b hb
    apply norm_fderiv_sub_le_nine_mul_of_coordinateWord_two_bound
      _ O hO hConvex hWord M hM _ b a hb ha
    intro c hc i j
    have hPrefix : coordinateFieldWordPartial [j,i]
        (coordinateFieldWordPartial w (radiusTwoKernelPoleSection G zB)) =
        coordinateFieldWordPartial (j::i::w) (radiusTwoKernelPoleSection G zB) := by
      simp only [coordinateFieldWordPartial]
    rw [hPrefix]
    exact hSecond z hzS c hc i j
  have hAvalue (v : R3) : A v = ∑ i : Fin 3, v i • D i := by
    simp only [A, _root_.sum_apply, ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj]
  have hAgraph (v : R3) : (A v : R3 → ℝ) =ᵐ[ν]
      (fun z => fderiv ℝ (fun a => f a z) p v) := by
    rw [hAvalue v]
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin 3 => v i • D i),
      ae_all_iff.2 (fun i : Fin 3 => Lp.coeFn_smul (v i) (D i)),
      ae_all_iff.2 hD, ae_restrict_mem hS.measurableSet] with z hSum hSmul hDz hzS
    change (∑ i : Fin 3, v i • D i) z = ∑ i : Fin 3, (v i • D i) z at hSum
    rw [hSum]
    simp only [f, dif_pos (hSB hzS)]
    calc
      (∑ i : Fin 3, (v i • D i) z) =
          ∑ i : Fin 3, v i * coordinateFieldWordPartial (i::w)
            (radiusTwoKernelPoleSection G ⟨z,hSB hzS⟩) p := by
        apply Finset.sum_congr rfl
        intro i _
        have h := hSmul i
        simp only [Pi.smul_apply, smul_eq_mul] at h
        rw [h, hDz i hzS]
      _ = fderiv ℝ (coordinateFieldWordPartial w
          (radiusTwoKernelPoleSection G ⟨z,hSB hzS⟩)) p v := by
        symm
        simpa only [coordinateFieldWordPartial, smul_eq_mul] using
          ActualReferenceDecomposition.fderiv_apply_eq_coordinate_sum
            (coordinateFieldWordPartial w (radiusTwoKernelPoleSection G ⟨z,hSB hzS⟩)) p v
  have hRow (a : R3) (ha : a ∈ O) : (F a : R3 → ℝ) =ᵐ[ν] f a := by
    filter_upwards [hF a ha, ae_restrict_mem hS.measurableSet] with z hz hzS
    simpa only [f, dif_pos (hSB hzS)] using hz hzS
  exact norm_Lp_two_row_remainder_le ν F f O hConvex (9*M)
    (mul_nonneg (by norm_num) hM) hFields p q hp hq (hRow p hp) (hRow q hq)
    (A (q-p)) (hAgraph (q-p))

lemma hasFDerivAt_radiusTwo_nativeWord_Lp_family
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (hS : IsCompact S) (hSB : S ⊆ (radiusTwoOpens : Set R3))
    (O : Set R3) (hO : IsOpen O) (hConvex : Convex ℝ O)
    (hOB : O ⊆ (radiusTwoOpens : Set R3) \ S) (w : List (Fin 3))
    (M : ℝ) (hM : 0 ≤ M)
    (hSecond : ∀ z : R3, ∀ hz : z ∈ S, ∀ a ∈ O, ∀ i j : Fin 3,
      ‖coordinateFieldWordPartial (j::i::w) (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) a‖ ≤ M)
    (F : R3 → Lp ℝ 2 (((volume : Measure R3).restrict radiusTwoOpens).restrict S))
    (hF : ∀ a ∈ O, ∀ᵐ z ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S),
      ∀ hz : z ∈ S, F a z = coordinateFieldWordPartial w
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) a)
    (p : R3) (hp : p ∈ O)
    (D : Fin 3 → Lp ℝ 2 (((volume : Measure R3).restrict radiusTwoOpens).restrict S))
    (hD : ∀ i : Fin 3, ∀ᵐ z ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S),
      ∀ hz : z ∈ S, D i z = coordinateFieldWordPartial (i::w)
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) p) :
    HasFDerivAt F (∑ i : Fin 3, (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).smulRight (D i)) p := by
  let A := ∑ i : Fin 3, (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).smulRight (D i)
  let L : ℝ := measureUnivNNReal
    (((volume : Measure R3).restrict radiusTwoOpens).restrict S) ^
      (2 : ENNReal).toReal⁻¹ * (9*M)
  have hL : 0 ≤ L := by positivity
  change HasFDerivAt F A p
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hDen : 0 < L+1 := by linarith
  have hRadius : 0 < ε/(L+1) := div_pos hε hDen
  filter_upwards [hO.mem_nhds hp, Metric.ball_mem_nhds p hRadius] with q hq hBall
  have hNorm : ‖q-p‖ < ε/(L+1) := mem_ball_iff_norm.mp hBall
  have hMul : L*‖q-p‖ ≤ ε := by
    have h := (lt_div_iff₀ hDen).mp hNorm
    nlinarith [norm_nonneg (q-p)]
  have hRem := norm_radiusTwo_nativeWord_family_firstOrder_remainder_le
    hreg hcalc g hg K G hData S hS hSB O hO hConvex hOB w M hM hSecond F hF p hp D hD q hq
  calc
    ‖F q - F p - A (q-p)‖ ≤ L*‖q-p‖^2 := by
      simpa only [A, L, mul_assoc] using hRem
    _ ≤ ε*‖q-p‖ := by
      simpa only [pow_two, mul_assoc] using
        mul_le_mul_of_nonneg_right hMul (norm_nonneg (q-p))

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.norm_radiusTwo_nativeWord_family_firstOrder_remainder_le
#print axioms OAI.AnisotropicCalderon.ExteriorSource.hasFDerivAt_radiusTwo_nativeWord_Lp_family
