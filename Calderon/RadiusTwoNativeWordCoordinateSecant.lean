import Calderon.RadiusTwoNativeRestrictedRowGraphs
import Calderon.RadiusTwoPoleWordCoordinateLineRemainder

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds

lemma norm_radiusTwo_nativeWord_coordinateSecant_error_le
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (hS : IsCompact S) (hSB : S ⊆ (radiusTwoOpens : Set R3))
    (O : Set R3) (hO : IsOpen O) (hOB : O ⊆ (radiusTwoOpens : Set R3) \ S)
    (w : List (Fin 3)) (M : ℝ) (hM : 0 ≤ M)
    (hWord : ∀ z : R3, ∀ hz : z ∈ S, ∀ q ∈ O, ∀ i : Fin 3,
      |coordinateFieldWordPartial (i::i::w) (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) q| ≤ M)
    (p q : (radiusTwoOpens : Set R3)) (i : Fin 3) (t : ℝ) (ht : 0 < t)
    (hq : (q : R3) = (p : R3) + t • coordinateDirection i)
    (hLine : ∀ s ∈ Icc (0 : ℝ) t, (p : R3) + s • coordinateDirection i ∈ O)
    (Dp Dq Dnext : Lp ℝ 2 (((volume : Measure R3).restrict radiusTwoOpens).restrict S))
    (hP : ∀ᵐ z ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S),
      ∀ hz : z ∈ S, Dp z = coordinateFieldWordPartial w
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) p)
    (hQ : ∀ᵐ z ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S),
      ∀ hz : z ∈ S, Dq z = coordinateFieldWordPartial w
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) q)
    (hNext : ∀ᵐ z ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S),
      ∀ hz : z ∈ S, Dnext z = coordinateFieldWordPartial (i::w)
        (radiusTwoKernelPoleSection G ⟨z,hSB hz⟩) p) :
    ‖t⁻¹ • (Dq - Dp) - Dnext‖ ≤
      measureUnivNNReal (((volume : Measure R3).restrict radiusTwoOpens).restrict S) ^
        (2 : ENNReal).toReal⁻¹ * M * t := by
  let μ : Measure R3 := (volume : Measure R3).restrict radiusTwoOpens
  let ν : Measure R3 := μ.restrict S
  have hμ : μ ≤ (volume : Measure R3) := Measure.restrict_le_self
  letI radiusTwoNativeWordSecantFiniteMeasure : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (ne_of_lt ((hμ S).trans_lt hS.measure_lt_top))
  have hRem : ‖Dq - Dp - t • Dnext‖ ≤
      measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * (M * t^2) := by
    apply Lp.norm_le_of_ae_bound (mul_nonneg hM (sq_nonneg t))
    filter_upwards [Lp.coeFn_sub (Dq - Dp) (t • Dnext),
      Lp.coeFn_sub Dq Dp, Lp.coeFn_smul t Dnext, hP, hQ, hNext,
      ae_restrict_mem hS.measurableSet] with z hSub hRows hSmul hPz hQz hNz hz
    change (Dq - Dp - t • Dnext) z = (Dq - Dp) z - (t • Dnext) z at hSub
    change (Dq - Dp) z = Dq z - Dp z at hRows
    have hSmul' : (t • Dnext) z = t * Dnext z := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hSmul
    rw [hSub, hRows, hSmul', hPz hz, hQz hz, hNz hz]
    have hAvoid : O ⊆ (radiusTwoOpens : Set R3) \ {(z : R3)} := by
      intro a ha
      refine ⟨(hOB ha).1, ?_⟩
      intro h
      have heq : a = z := Set.mem_singleton_iff.mp h
      exact (hOB ha).2 (heq.symm ▸ hz)
    have h := norm_radiusTwo_poleSection_word_coordinateLine_remainder_le
      hreg hcalc g hg K G hData ⟨z,hSB hz⟩ w O hO hAvoid M hM i
      (fun a ha => hWord z hz a ha i) p t ht.le hLine
    rw [← hq] at h
    simpa only [Real.norm_eq_abs] using h
  have hScale : t⁻¹ • (Dq - Dp - t • Dnext) =
      t⁻¹ • (Dq - Dp) - Dnext := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
  calc
    ‖t⁻¹ • (Dq - Dp) - Dnext‖ =
        ‖t⁻¹ • (Dq - Dp - t • Dnext)‖ := congrArg norm hScale.symm
    _ = t⁻¹ * ‖Dq - Dp - t • Dnext‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    _ ≤ t⁻¹ * (measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * (M * t^2)) :=
      mul_le_mul_of_nonneg_left hRem (inv_nonneg.mpr ht.le)
    _ = measureUnivNNReal ν ^ (2 : ENNReal).toReal⁻¹ * M * t := by
      field_simp [ne_of_gt ht]
      <;> ring

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.norm_radiusTwo_nativeWord_coordinateSecant_error_le
