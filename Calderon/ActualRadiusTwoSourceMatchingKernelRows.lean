import Calderon.ActualRadiusTwoKernelSelectedSourceResponse
import Calderon.RadiusTwoSourcePointwiseEmbedding
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution TauCeti.PDE.weakSolutionDirichlet

theorem eqOn_radiusTwoSourceKernel_rows_of_sourceEvaluationFamily_eq
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (K₁ K₂ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G₁ G₂ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData₁ : IsRadiusTwoSymmetricInverseSourceKernel g₁ hg₁ K₁ G₁)
    (hData₂ : IsRadiusTwoSymmetricInverseSourceKernel g₂ hg₂ K₂ G₂)
    (p₁ p₂ : (radiusTwoOpens : Set R3))
    (hMatch : radiusTwoSourceEvaluationFamily hreg hcalc g₁ hg₁ p₁ =
      radiusTwoSourceEvaluationFamily hreg hcalc g₂ hg₂ p₂) :
    EqOn (G₁ p₁) (G₂ p₂)
      ((fixedExteriorSourceOpens : Set R3) \ ({(p₁ : R3)} ∪ {(p₂ : R3)})) := by
  obtain ⟨_hLimit₁,hCont₁,hRep₁,_hBoundary₁,_hInverse₁,_hTest₁⟩ := hData₁.1 p₁
  obtain ⟨_hLimit₂,hCont₂,hRep₂,_hBoundary₂,_hInverse₂,_hTest₂⟩ := hData₂.1 p₂
  haveI : IsFiniteMeasure ((volume : Measure R3).restrict radiusTwoOpens) :=
    ⟨by simpa only [Measure.restrict_apply_univ,radiusTwoOpens,TopologicalSpace.Opens.coe_mk] using
      ((measure_mono (show ball (0 : R3) 2 ⊆ closedBall (0 : R3) 2 from ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 2).measure_lt_top)⟩
  have hInt₁ : IntegrableOn (G₁ p₁) (radiusTwoOpens : Set R3) :=
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp (K₁ p₁))).congr hRep₁.symm
  have hInt₂ : IntegrableOn (G₂ p₂) (radiusTwoOpens : Set R3) :=
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp (K₂ p₂))).congr hRep₂.symm
  have hLoc : LocallyIntegrableOn (fun z => G₁ p₁ z - G₂ p₂ z)
      (fixedExteriorSourceOpens : Set R3) (volume : Measure R3) :=
    ((hInt₁.sub hInt₂).mono_set fixedExteriorSourceOpens_le_radiusTwo).locallyIntegrableOn
  have hProd (K : RadiusTwoL2) (G : R3 → ℝ)
      (hRep : G =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (K : R3 → ℝ))
      (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
      Integrable (fun z => G z * f z) ((volume : Measure R3).restrict radiusTwoOpens) := by
    have hInner := L2.integrable_inner (𝕜 := ℝ) K
      (smoothRadiusTwoForcing ⟨(f : R3 → ℝ),f.contDiff⟩)
    have hInner' : Integrable
        (fun z => K z * smoothRadiusTwoForcing ⟨(f : R3 → ℝ),f.contDiff⟩ z)
        ((volume : Measure R3).restrict radiusTwoOpens) := by
      simpa only [Real.inner_apply] using hInner
    apply hInner'.congr
    filter_upwards [hRep,smoothRadiusTwoForcing_ae ⟨(f : R3 → ℝ),f.contDiff⟩] with z hGz hfz
    exact congrArg₂ (fun a b : ℝ => a * b) hGz.symm hfz
  have hTests (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
      (∫ z in radiusTwoOpens, f z * (G₁ p₁ z - G₂ p₂ z) ∂(volume : Measure R3)) = 0 := by
    calc
      (∫ z in radiusTwoOpens, f z * (G₁ p₁ z - G₂ p₂ z) ∂(volume : Measure R3)) =
          (∫ z in radiusTwoOpens, G₁ p₁ z * f z - G₂ p₂ z * f z ∂(volume : Measure R3)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = (∫ z in radiusTwoOpens, G₁ p₁ z * f z ∂(volume : Measure R3)) -
          (∫ z in radiusTwoOpens, G₂ p₂ z * f z ∂(volume : Measure R3)) :=
        integral_sub (hProd (K₁ p₁) (G₁ p₁) hRep₁ f) (hProd (K₂ p₂) (G₂ p₂) hRep₂ f)
      _ = radiusTwoSmoothSourceResponse hreg hcalc g₁ hg₁ f p₁ -
          radiusTwoSmoothSourceResponse hreg hcalc g₂ hg₂ f p₂ := by
        rw [integral_radiusTwoSourceKernel_mul_fixedSource_eq_response hreg hcalc g₁ hg₁ K₁ G₁ hData₁ p₁ f,
          integral_radiusTwoSourceKernel_mul_fixedSource_eq_response hreg hcalc g₂ hg₂ K₂ G₂ hData₂ p₂ f]
      _ = 0 := sub_eq_zero.mpr (congrFun hMatch f)
  have hZero := fixedExteriorSourceOpens.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := (volume : Measure R3)) hLoc (fun f hf hfc hfs => by
      have h0 := hTests ⟨f,hf,hfc,hfs⟩
      change (∫ z in radiusTwoOpens, f z * (G₁ p₁ z - G₂ p₂ z) ∂(volume : Measure R3)) = 0 at h0
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport
          (fun hz' => hz (fixedExteriorSourceOpens_le_radiusTwo (hfs hz')))
        simp only [hfz,zero_mul])] at h0
      simpa only [smul_eq_mul] using h0)
  have hAE : (G₁ p₁) =ᵐ[(volume : Measure R3).restrict fixedExteriorSourceOpens] (G₂ p₂) := by
    change ∀ᵐ z ∂(volume : Measure R3).restrict fixedExteriorSourceOpens, G₁ p₁ z = G₂ p₂ z
    rw [ae_restrict_iff' fixedExteriorSourceOpens.isOpen.measurableSet]
    filter_upwards [hZero] with z hz hzs
    exact sub_eq_zero.mp (hz hzs)
  let V : Set R3 := (fixedExteriorSourceOpens : Set R3) \ ({(p₁ : R3)} ∪ {(p₂ : R3)})
  have hV : IsOpen V := fixedExteriorSourceOpens.isOpen.sdiff
    (isClosed_singleton.union isClosed_singleton)
  have hV₁ : V ⊆ closedBall (0 : R3) 2 \ {(p₁ : R3)} := by
    intro z hz
    exact ⟨ball_subset_closedBall (fixedExteriorSourceOpens_le_radiusTwo hz.1),
      fun h => hz.2 (Or.inl h)⟩
  have hV₂ : V ⊆ closedBall (0 : R3) 2 \ {(p₂ : R3)} := by
    intro z hz
    exact ⟨ball_subset_closedBall (fixedExteriorSourceOpens_le_radiusTwo hz.1),
      fun h => hz.2 (Or.inr h)⟩
  exact Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3))
    (hAE.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) diff_subset)))
    hV (hCont₁.mono hV₁) (hCont₂.mono hV₂)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.eqOn_radiusTwoSourceKernel_rows_of_sourceEvaluationFamily_eq
