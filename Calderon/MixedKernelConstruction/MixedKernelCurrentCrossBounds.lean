import Calderon.MixedKernelConstruction.MixedKernelCurrentCoefficientPDE
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

/-- The exact current-cross scalar coefficient, with the manuscript's unnormalized mu^-2. -/
def currentCoefficient (F : R3 × R3 → ℝ) (U : Set R3) (μi : ℝ) (q : R3 → ℝ) : R3 → ℝ :=
  integralCoefficient ((volume : Measure R3).restrict U) F q (μi ^ 2)⁻¹

theorem productCurrent_memLp_product (Ω : Set (R3 × R3))
    (F : R3 × R3 → ℝ) (hFsmooth : ContDiffOn ℝ ∞ F Ω)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J)
    (hcross : K ×ˢ J ⊆ Ω) :
    MemLp (F) 2
      (((volume : Measure R3).restrict U).prod ((volume : Measure R3).restrict V)) := by
  rw [Measure.prod_restrict]
  have hc := hFsmooth.continuousOn.mono hcross
  apply (memLp_two_iff_integrable_sq
    ((hc.mono (Set.prod_mono hUK hVJ)).aestronglyMeasurable
      (hU.measurableSet.prod hV.measurableSet))).mpr
  exact ((hc.pow 2).integrableOn_compact (hK.prod hJ)).mono_set (Set.prod_mono hUK hVJ)

theorem productCurrent_slice_data (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (F : R3 × R3 → ℝ) (hSol : ProductSolutionOn S L lam F Ω)
    (D K : Set R3) (hD : IsOpen D) (hK : IsCompact K) (hDK : D ⊆ K)
    (y : R3) (hcross : ∀ x ∈ K, (x,y) ∈ Ω) :
    MemLp (fun x => F (x,y)) 2 ((volume : Measure R3).restrict D) ∧
    ContDiffOn ℝ ∞ (fun x => F (x,y)) D ∧
    ∀ x ∈ D, divCoeffGrad (dilatedFirstPrincipal S lam)
      (fun x => F (x,y)) x = 0 := by
  have hc : ContDiffOn ℝ ∞ (fun x => F (x,y)) K :=
    hSol.1.comp (contDiffOn_id.prodMk contDiffOn_const) hcross
  refine ⟨?_, hc.mono hDK, ?_⟩
  · exact (memLp_two_iff_integrable_sq
      ((hc.continuousOn.mono hDK).aestronglyMeasurable hD.measurableSet)).mpr
      (((hc.continuousOn.pow 2).integrableOn_compact hK).mono_set hDK)
  · intro x hx
    rw [dilatedFirstPrincipal, ← coordinateFluxDivergence_eq_divCoeffGrad]
    exact hSol.2.1 (x,y) (hcross x (hDK hx))

theorem productCurrent_integralCoefficient_agreement
    (S : KnownSideSourceData) (L lam : ℝ) (Ω : Set (R3 × R3))
    (F : R3 × R3 → ℝ) (hSol : ProductSolutionOn S L lam F Ω)
    (D K T V : Set R3) (hD : IsOpen D) (hK : IsCompact K) (hDK : D ⊆ K)
    (hTD : T ⊆ D) (hcross : ∀ y ∈ V, ∀ x ∈ K, (x,y) ∈ Ω)
    {ι : Type*}
    (w : HilbertBasis ι ℝ (harmonicSub D hD (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn))
    (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i,
      (ContinuousLinearMap.adjoint (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD) ∘L
        harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD) (w i) = μ i ^ 2 • w i)
    (i : ι) :
    EqOn
      (integralCoefficient ((volume : Measure R3).restrict T) (F)
        (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i)) (μ i ^ 2)⁻¹)
      (integralCoefficient ((volume : Measure R3).restrict D) (F)
        (w i : Lp ℝ 2 ((volume : Measure R3).restrict D)) 1) V := by
  intro y hy
  obtain ⟨hf, hfs, hfP⟩ := productCurrent_slice_data S L lam Ω F hSol D K hD hK hDK y (hcross y hy)
  have h1 := harmonicSlice_coefficient_agreement D hD (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD w μ hμ heigen
    (fun x => F (x,y)) hf hfs hfP i
  have h2 := harmonicSlice_repr_integral D hD (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn w
    (fun x => F (x,y)) hf hfs hfP i
  simpa only [integralCoefficient, one_mul] using h1.trans h2

theorem currentCoefficient_observed_bound (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (F : R3 × R3 → ℝ) (hSol : ProductSolutionOn S L lam F Ω)
    (D K T V J : Set R3) (hD : IsOpen D) (hK : IsCompact K) (hDK : D ⊆ K) (hTD : T ⊆ D)
    (hV : IsOpen V) (hJ : IsCompact J) (hVJ : V ⊆ J) (hcross : K ×ˢ J ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : Type)
      (w : HilbertBasis ι ℝ (harmonicSub D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ), (∀ i, 0 < μ i) →
      (∀ i, (ContinuousLinearMap.adjoint (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD) ∘L
        harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD) (w i) = μ i ^ 2 • w i) →
      ∀ i : ι, ∃ hb : MemLp (currentCoefficient F T (μ i)
          (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i)))
          2 ((volume : Measure R3).restrict V),
        ‖hb.toLp (currentCoefficient F T (μ i)
          (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i)))‖ ≤ M := by
  have hF := productCurrent_memLp_product Ω F hSol.1 D V K J hD hV hK hJ hDK hVJ hcross
  refine ⟨‖hF.toLp (F)‖, norm_nonneg _, fun ι w μ hμ heigen i => ?_⟩
  obtain ⟨hb1, hbound⟩ := harmonicIntegralCoefficient_memLp_and_norm_le
    ((volume : Measure R3).restrict D) ((volume : Measure R3).restrict V) _ w
    (F) hF i
  have hagree := productCurrent_integralCoefficient_agreement S L lam Ω F hSol D K T V hD hK hDK hTD
    (fun y hy x hx => hcross ⟨hx, hVJ hy⟩) w μ hμ heigen i
  have hae : currentCoefficient F T (μ i)
      (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i))
      =ᵐ[(volume : Measure R3).restrict V]
      integralCoefficient ((volume : Measure R3).restrict D) (F)
        (w i : Lp ℝ 2 ((volume : Measure R3).restrict D)) 1 :=
    (ae_restrict_mem hV.measurableSet).mono fun y hy => hagree hy
  have hb : MemLp (currentCoefficient F T (μ i)
      (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i)))
      2 ((volume : Measure R3).restrict V) := MemLp.ae_eq hae.symm hb1
  refine ⟨hb, ?_⟩
  rw [(MemLp.toLp_eq_toLp_iff hb hb1).mpr hae]
  exact hbound

theorem currentCoefficient_room_memLp (S : KnownSideSourceData) (lam : ℝ)
    (Ω : Set (R3 × R3)) (F : R3 × R3 → ℝ) (hFsmooth : ContDiffOn ℝ ∞ F Ω)
    (D1 : Set R3) (hD1 : IsOpen D1) (T KT D2 J2 : Set R3) (hT : IsOpen T) (hKT : IsCompact KT)
    (hTKT : T ⊆ KT) (hTD1 : T ⊆ D1) (hD2 : IsOpen D2) (hJ2 : IsCompact J2) (hD2J2 : D2 ⊆ J2)
    (hrow : KT ×ˢ J2 ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : Type)
      (w : ι → harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn) (μ : ι → ℝ), (∀ i, 0 < μ i) →
      (∀ i j, inner ℝ (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i))
        (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w j)) =
          if i = j then μ i ^ 2 else 0) →
      ∀ i : ι, ∃ hb : MemLp (currentCoefficient F T (μ i)
          (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)))
          2 ((volume : Measure R3).restrict D2),
        ‖hb.toLp (currentCoefficient F T (μ i)
          (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)))‖ ≤ M / μ i := by
  have hF := productCurrent_memLp_product Ω F hFsmooth T D2 KT J2 hT hD2 hKT hJ2 hTKT hD2J2 hrow
  refine ⟨‖hF.toLp (F)‖, norm_nonneg _, ?_⟩
  intro ι w μ hμ hgram i
  have hn : ‖harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)‖ = μ i := by
    have h := hgram i i
    rw [if_pos rfl, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (hμ i).le).mp h
  obtain ⟨hb, hbd⟩ := integralCoefficient_memLp_and_norm_le
    ((volume : Measure R3).restrict T) ((volume : Measure R3).restrict D2)
    (F) hF (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)) (μ i ^ 2)⁻¹
  refine ⟨hb, hbd.trans_eq ?_⟩
  rw [hn, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), pow_two, mul_inv,
    mul_assoc (μ i)⁻¹ (μ i)⁻¹ (μ i), inv_mul_cancel₀ (hμ i).ne', mul_one, div_eq_inv_mul]

theorem currentCoefficient_both_bounds (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (F : R3 × R3 → ℝ)
    (hSol : ProductSolutionOn S L lam F Ω)
    (D1 K1 T KT D2 J2 S2 JS : Set R3) (hD1 : IsOpen D1) (hK1 : IsCompact K1) (hD1K1 : D1 ⊆ K1)
    (hT : IsOpen T) (hKT : IsCompact KT) (hTKT : T ⊆ KT) (hTD1 : T ⊆ D1)
    (hD2 : IsOpen D2) (hJ2 : IsCompact J2) (hD2J2 : D2 ⊆ J2)
    (hS2 : IsOpen S2) (hJS : IsCompact JS) (hS2JS : S2 ⊆ JS)
    (hrow : KT ×ˢ J2 ⊆ Ω) (hobs : K1 ×ˢ JS ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : Type)
      (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
      ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ →
      ∀ i : ι, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
        (currentCoefficient F T (μ i) (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i))) := by
  obtain ⟨M2, hM2, HO⟩ := currentCoefficient_observed_bound S L lam Ω F hSol D1 K1 T S2 JS hD1 hK1
    hD1K1 hTD1 hS2 hJS hS2JS hobs
  obtain ⟨M1, hM1, HR⟩ := currentCoefficient_room_memLp S lam Ω F hSol.1 D1 hD1 T KT D2 J2 hT hKT hTKT
    hTD1 hD2 hJ2 hD2J2 hrow
  refine ⟨max M1 M2, le_max_of_le_right hM2, ?_⟩
  rintro ι w μ ⟨hμ, heigen, hgram⟩ i
  have hPDE := product_integralCoefficient_secondPDE S L lam Ω hΩ F hSol
    T D2 KT J2 hT hD2 hKT hJ2 hTKT hD2J2 hrow _
    (Lp.memLp (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i))) (μ i ^ 2)⁻¹
  obtain ⟨hb, hbd⟩ := HR ι w μ hμ hgram i
  obtain ⟨hs, hsd⟩ := HO ι w μ hμ heigen i
  unfold SecondCoefficientArmsOn
  refine ⟨hPDE.1, hPDE.2, ⟨hb, hbd.trans ?_⟩, ⟨hs, hsd.trans (le_max_right _ _)⟩⟩
  exact div_le_div_of_nonneg_right (le_max_left _ _) (hμ i).le

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
