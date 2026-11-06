import Calderon.ActualWeightedHorizontalActionBounds
import Calderon.ActualOriginalDoubleEForm
import Calderon.MetricFrameDivergence
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSScalarCoefficientBounds
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ReferenceDensityBounds ConformalDepth RadiusProfile ActualAngularPiDraft MetricFrameDivergence
  BaseDensityAdjoint WeightedFrameGreen FischerDensityIntegration
private lemma compact_family_bound {α E ι : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E] [Fintype ι] (K : Set α) (hK : IsCompact K)
    (f : ι → α → E) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i, ∀ x ∈ K, ‖f i x‖ ≤ C := by
  classical
  have hi (i : ι) : ∃ C : ℝ, ∀ x ∈ K, ‖f i x‖ ≤ C :=
    hK.exists_bound_of_continuousOn (hf i)
  choose C hC using hi
  refine ⟨1+∑ i, |C i|,le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg (C i))),?_⟩
  intro i x hx
  exact (hC i x hx).trans ((le_abs_self _).trans (by
    have h := Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)
    linarith))


/-- Actual native log-radius horizontal coefficient, with one constant before all profiles. -/
theorem exists_profile_horizontal_log_derivative_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
      0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      1 ≤ ReferenceWeightedApproximation.actualReferenceBeta g L q δr Ar p x → ∀ i : Fin 3,
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i| ≤
        Cf*ReferenceWeightedApproximation.actualReferenceBeta g L q δr Ar p x := by
  obtain ⟨CX,hCX,hFrame⟩ := compact_family_bound (Icc (0 : ℝ) 1 ×ˢ K) (isCompact_Icc.prod hK)
    (fun i : Fin 3 => fun t : ℝ × R3 => referenceMetricGramFrame g L t i)
    (fun i => (contDiff_referenceMetricGramFrame g hg L i).continuous.continuousOn)
  obtain ⟨J1,J2,hJ1,_hJ2,hLog⟩ := exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at
    g hg K hK L hL
  refine ⟨J1*CX,mul_nonneg hJ1.le (zero_le_one.trans hCX),?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq x hx hβ i
  have hX := hFrame i (q,x) ⟨hq,hx⟩
  have he : referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i =
      fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x
        (referenceMetricGramFrame g L (q,x) i) := by
    unfold referenceRadiusHorizontalLogDerivative
    rw [ActualHigherSZeroCoefficientBounds.conformalFrame_coordinateVector_eq g L q x i]
  rw [he,← Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ (fun y => Real.log (referenceRadius δr Ar p L y)) x‖*
        ‖referenceMetricGramFrame g L (q,x) i‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (J1*ReferenceWeightedApproximation.actualReferenceBeta g L q δr Ar p x)*CX :=
      mul_le_mul (hLog q hq δr hδr hδr1 Ar hAr p hp x hx).1 hX (norm_nonneg _)
        (mul_nonneg hJ1.le (zero_le_one.trans hβ))
    _ = _ := by ring

/-- Exact native metric divergence, retaining the actual positive physical density. -/
lemma weighted_frame_divergence_eq_density_trace (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q : ℝ) (i : Fin 3) (x : R3) :
    referenceWeightedFrameDivergence g L q i x = referenceDensityFamily g L (q,x)*
      ∑ a : Fin 3, referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) a) a i := by
  change weightedCoordinateDivergence (fun y => referenceDensityFamily g L (q,y))
    (fun y => referenceMetricGramFrame g L (q,y) i) x = _
  exact reference_weightedCoordinateDivergence_gramFrame g hg L q i x

/-- Uniform divergence/density bound directly from the native connection trace. -/
theorem exists_weighted_frame_divergence_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ Cdiv : ℝ, 0 ≤ Cdiv ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ i : Fin 3,
      |referenceWeightedFrameDivergence g L q i x| ≤ Cdiv*referenceDensityFamily g L (q,x) := by
  obtain ⟨M,hM,hGeo⟩ := ActualHorizontalNormBridge.exists_reference_geometry_uniform_bounds g hg L K hK
  refine ⟨3*M,mul_nonneg (by norm_num) (zero_le_one.trans hM),?_⟩
  intro q hq x hx i
  rw [weighted_frame_divergence_eq_density_trace g hg L q i x,abs_mul,
    abs_of_pos (referenceDensityFamily_pos g hg L (q,x))]
  have hs : |∑ a : Fin 3, referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) a) a i| ≤ 3*M := by
    calc
      _ ≤ ∑ a : Fin 3, |referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) a) a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin 3, M := Finset.sum_le_sum (fun a _ => (hGeo q hq x hx).2.2.2 a a i)
      _ = _ := by simp
  exact (mul_le_mul_of_nonneg_left hs (referenceDensityFamily_pos g hg L (q,x)).le).trans_eq (mul_comm _ _)

private lemma fderiv_slice_apply (f : (ℝ × R3) → ℝ) (hf : Differentiable ℝ f)
    (q : ℝ) (x v : R3) :
    fderiv ℝ (fun y => f (q,y)) x v = fderiv ℝ f (q,x) (0,v) := by
  have hi : HasFDerivAt (fun y : R3 => (q,y))
      ((0 : R3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ R3)) x :=
    (hasFDerivAt_const q x).prodMk (hasFDerivAt_id x)
  have h := ((hf (q,x)).hasFDerivAt.comp x hi).fderiv
  exact congrArg (fun A : R3 →L[ℝ] ℝ => A v) h

/-- Actual horizontal derivative of fixed-admissible-metric Q, uniform before profiles. -/
theorem exists_principal_horizontal_derivative_bound (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) :
    ∃ CQ1 : ℝ, 0 ≤ CQ1 ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ k i j : Fin 3,
      |fderiv ℝ (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x
        (referenceMetricGramFrame g L (q,x) k)| ≤ CQ1 := by
  let Q : Fin 3 → Fin 3 → (ℝ × R3) → ℝ :=
    fun i j t => referenceDensityPrincipalFrameCoefficient g g2 L t.1 t.2 i j
  have hQ (i j : Fin 3) : ContDiff ℝ ∞ (Q i j) :=
    contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j
  let DQ : (Fin 3 × Fin 3 × Fin 3) → (ℝ × R3) → ℝ := fun k t =>
    fderiv ℝ (Q k.2.1 k.2.2) t (0,referenceMetricGramFrame g L t k.1)
  have hDQ (k : Fin 3 × Fin 3 × Fin 3) : Continuous (DQ k) := by
    exact (((hQ k.2.1 k.2.2).fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const.prodMk (contDiff_referenceMetricGramFrame g hg L k.1))).continuous
  obtain ⟨CQ,hCQ,hBound⟩ := compact_family_bound (Icc (0 : ℝ) 1 ×ˢ K) (isCompact_Icc.prod hK)
    DQ (fun k => (hDQ k).continuousOn)
  refine ⟨CQ,zero_le_one.trans hCQ,?_⟩
  intro q hq x hx k i j
  have hd := fderiv_slice_apply (Q i j) ((hQ i j).differentiable (by simp)) q x
    (referenceMetricGramFrame g L (q,x) k)
  have hb := hBound (k,i,j) (q,x) ⟨hq,hx⟩
  rw [Real.norm_eq_abs] at hb
  exact (congrArg abs hd).le.trans hb

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSScalarCoefficientBounds
