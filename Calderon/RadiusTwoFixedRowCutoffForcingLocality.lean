import Calderon.SmoothMetricCutoffFluxSupport
import Calderon.RadiusTwoFixedRowCutoffForcing
import Calderon.RadiusTwoSmoothValueMultiplier

/-! Full EXPANSION.json precedes exact native cutoff locality. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Gradient InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge MetricVolume

theorem radiusTwoFixedRowCutoffForcingLp_contDiffSMul_eq
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η χ : SmoothData)
    (V : Set R3) (hV : IsOpen V) (hηV : tsupport η.1 ⊆ V)
    (hOne : ∀ x ∈ V, χ.1 x = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ.1 x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient χ.1 x‖ ≤ M)
    (u : RadiusTwoH1) :
    radiusTwoFixedRowCutoffForcingLp g hg η
        (TauCeti.W1p.contDiffSMulL χ.1 χ.2 hM hAbs hGrad u) =
      radiusTwoFixedRowCutoffForcingLp g hg η u := by
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 :=
    TauCeti.W1p.contDiffSMulL χ.1 χ.2 hM hAbs hGrad
  have hValue : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      TauCeti.W1p.value (S u) x = χ.1 x • TauCeti.W1p.value u x := by
    simpa only [S,TauCeti.W1p.contDiffSMulL_apply] using
      TauCeti.W1p.value_contDiffSMul_ae χ.2 hM hAbs hGrad u
  have hGradient : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      TauCeti.W1p.gradient (S u) x = χ.1 x • TauCeti.W1p.gradient u x +
        TauCeti.W1p.value u x • gradient χ.1 x := by
    simpa only [S,TauCeti.W1p.contDiffSMulL_apply] using
      TauCeti.W1p.gradient_contDiffSMul_ae χ.2 hM hAbs hGrad u
  apply Lp.ext
  filter_upwards [radiusTwoFixedRowCutoffForcingLp_apply_ae g hg η (S u),
    radiusTwoFixedRowCutoffForcingLp_apply_ae g hg η u,hValue,hGradient]
    with x hLeft hRight hVal hG
  change (radiusTwoFixedRowCutoffForcingLp g hg η (S u)) x = _
  rw [hLeft,hRight]
  by_cases hxV : x ∈ V
  · have hNear : χ.1 =ᶠ[𝓝 x] (fun _ : R3 => (1 : ℝ)) := by
      filter_upwards [hV.mem_nhds hxV] with z hz
      exact hOne z hz
    have hχG : gradient χ.1 x = 0 := by
      simpa only [gradient_fun_const] using hNear.gradient_eq
    have hValEq : TauCeti.W1p.value (S u) x = TauCeti.W1p.value u x := by
      simpa only [hOne x hxV,one_smul] using hVal
    have hGradEq : TauCeti.W1p.gradient (S u) x = TauCeti.W1p.gradient u x := by
      simpa only [hOne x hxV,hχG,one_smul,smul_zero,add_zero] using hG
    simp only [radiusTwoFixedRowCutoffForcing,hValEq,hGradEq]
  · have hNot : x ∉ tsupport η.1 := fun h => hxV (hηV h)
    have hJ (i : Fin 3) : smoothMetricCutoffFlux g η i x = 0 := by
      by_contra hNonzero
      exact hNot (tsupport_smoothMetricCutoffFlux_subset g η i
        (subset_tsupport _ hNonzero))
    have hDiv : (smoothMetricCutoffFluxDivergence g hg η).1 x = 0 := by
      by_contra hNonzero
      exact hNot (tsupport_smoothMetricCutoffFluxDivergence_subset g hg η
        (subset_tsupport _ hNonzero))
    simp only [radiusTwoFixedRowCutoffForcing,hJ,hDiv,zero_mul,
      Finset.sum_const_zero,mul_zero,sub_zero]

theorem radiusTwo_contDiffSMul_comp_eq_of_one_on_tsupport
    (η χ : SmoothData) (hOne : ∀ x ∈ tsupport η.1, χ.1 x = 1)
    {Mη Mχ : ℝ} (hMη : 0 ≤ Mη) (hMχ : 0 ≤ Mχ)
    (hAbsη : ∀ x ∈ (radiusTwoOpens : Set R3), |η.1 x| ≤ Mη)
    (hGradη : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient η.1 x‖ ≤ Mη)
    (hAbsχ : ∀ x ∈ (radiusTwoOpens : Set R3), |χ.1 x| ≤ Mχ)
    (hGradχ : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient χ.1 x‖ ≤ Mχ)
    (u : RadiusTwoH1) :
    TauCeti.W1p.contDiffSMulL η.1 η.2 hMη hAbsη hGradη
        (TauCeti.W1p.contDiffSMulL χ.1 χ.2 hMχ hAbsχ hGradχ u) =
      TauCeti.W1p.contDiffSMulL η.1 η.2 hMη hAbsη hGradη u := by
  let Sη : RadiusTwoH1 →L[ℝ] RadiusTwoH1 :=
    TauCeti.W1p.contDiffSMulL η.1 η.2 hMη hAbsη hGradη
  let Sχ : RadiusTwoH1 →L[ℝ] RadiusTwoH1 :=
    TauCeti.W1p.contDiffSMulL χ.1 χ.2 hMχ hAbsχ hGradχ
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  filter_upwards [TauCeti.W1p.value_contDiffSMul_ae η.2 hMη hAbsη hGradη (Sχ u),
    TauCeti.W1p.value_contDiffSMul_ae χ.2 hMχ hAbsχ hGradχ u,
    TauCeti.W1p.value_contDiffSMul_ae η.2 hMη hAbsη hGradη u]
    with x hLeft hInner hRight
  change TauCeti.W1p.value (Sη (Sχ u)) x = TauCeti.W1p.value (Sη u) x
  change TauCeti.W1p.value (Sη (Sχ u)) x = η.1 x * TauCeti.W1p.value (Sχ u) x at hLeft
  change TauCeti.W1p.value (Sχ u) x = χ.1 x * TauCeti.W1p.value u x at hInner
  change TauCeti.W1p.value (Sη u) x = η.1 x * TauCeti.W1p.value u x at hRight
  rw [hLeft,hInner,hRight]
  by_cases hη : η.1 x = 0
  · simp only [hη,zero_mul]
  · rw [hOne x (subset_tsupport _ hη),one_mul]

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoFixedRowCutoffForcingLp_contDiffSMul_eq
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwo_contDiffSMul_comp_eq_of_one_on_tsupport
