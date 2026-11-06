import MixedKernelCurrentCrossBounds
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  ExteriorSource ConnectionError MetricOperator MetricVolume
  ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
  CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

theorem currentCoefficient_observed_bound_with_exact_product_norm (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (F : R3 × R3 → ℝ) (hSol : ProductSolutionOn S L lam F Ω)
    (D K T V J : Set R3) (hD : IsOpen D) (hK : IsCompact K) (hDK : D ⊆ K) (hTD : T ⊆ D)
    (hV : IsOpen V) (hJ : IsCompact J) (hVJ : V ⊆ J) (hcross : K ×ˢ J ⊆ Ω)
    (hF : MemLp F 2 (((volume:Measure R3).restrict D).prod ((volume:Measure R3).restrict V))) :
    ∀ (ι : Type)
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
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i)))‖ ≤ ‖hF.toLp F‖ := by
  intro ι w μ hμ heigen i
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

theorem currentCoefficient_room_bound_with_exact_product_norm (S : KnownSideSourceData) (lam : ℝ)
    (Ω : Set (R3 × R3)) (F : R3 × R3 → ℝ) (hFsmooth : ContDiffOn ℝ ∞ F Ω)
    (D1 : Set R3) (hD1 : IsOpen D1) (T KT D2 J2 : Set R3) (hT : IsOpen T) (hKT : IsCompact KT)
    (hTKT : T ⊆ KT) (hTD1 : T ⊆ D1) (hD2 : IsOpen D2) (hJ2 : IsCompact J2) (hD2J2 : D2 ⊆ J2)
    (hrow : KT ×ˢ J2 ⊆ Ω)
    (hF : MemLp F 2 (((volume:Measure R3).restrict T).prod ((volume:Measure R3).restrict D2))) :
    ∀ (ι : Type)
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
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)))‖ ≤ ‖hF.toLp F‖ / μ i := by
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

theorem currentCoefficient_arms_of_productL2_bounds (S : KnownSideSourceData) (L lam : ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (F : R3 × R3 → ℝ)
    (hSol : ProductSolutionOn S L lam F Ω)
    (D1 K1 T KT D2 J2 S2 JS : Set R3) (hD1 : IsOpen D1) (hK1 : IsCompact K1) (hD1K1 : D1 ⊆ K1)
    (hT : IsOpen T) (hKT : IsCompact KT) (hTKT : T ⊆ KT) (hTD1 : T ⊆ D1)
    (hD2 : IsOpen D2) (hJ2 : IsCompact J2) (hD2J2 : D2 ⊆ J2)
    (hS2 : IsOpen S2) (hJS : IsCompact JS) (hS2JS : S2 ⊆ JS)
    (hrow : KT ×ˢ J2 ⊆ Ω) (hobs : K1 ×ˢ JS ⊆ Ω)
    (hFrow : MemLp F 2 (((volume:Measure R3).restrict T).prod ((volume:Measure R3).restrict D2)))
    (hFobs : MemLp F 2 (((volume:Measure R3).restrict D1).prod ((volume:Measure R3).restrict S2)))
    (M : ℝ) (hM : 0 ≤ M) (hRoomCap : ‖hFrow.toLp F‖ ≤ M) (hObsCap : ‖hFobs.toLp F‖ ≤ M) :
    ∀ (ι : Type)
      (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
      ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ →
      ∀ i : ι, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
        (currentCoefficient F T (μ i) (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i))) := by
  have HO := currentCoefficient_observed_bound_with_exact_product_norm S L lam Ω F hSol D1 K1 T S2 JS hD1 hK1
    hD1K1 hTD1 hS2 hJS hS2JS hobs hFobs
  have HR := currentCoefficient_room_bound_with_exact_product_norm S lam Ω F hSol.1 D1 hD1 T KT D2 J2 hT hKT hTKT
    hTD1 hD2 hJ2 hD2J2 hrow hFrow
  rintro ι w μ ⟨hμ, heigen, hgram⟩ i
  have hPDE := product_integralCoefficient_secondPDE S L lam Ω hΩ F hSol
    T D2 KT J2 hT hD2 hKT hJ2 hTKT hD2J2 hrow _
    (Lp.memLp (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i))) (μ i ^ 2)⁻¹
  obtain ⟨hb, hbd⟩ := HR ι w μ hμ hgram i
  obtain ⟨hs, hsd⟩ := HO ι w μ hμ heigen i
  unfold SecondCoefficientArmsOn
  refine ⟨hPDE.1, hPDE.2, ⟨hb, hbd.trans ?_⟩, ⟨hs, hsd.trans hObsCap⟩⟩
  exact div_le_div_of_nonneg_right hRoomCap (hμ i).le

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
