import Calderon.ActualReferenceDecomposition

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualReferenceFullAdjunction
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  AmbientReferenceRaising ActualReferenceDecomposition SpectralCoreRegularity SpectralWeightedGraph
  WeightedBaseSpectral WeightedAngularConvergence ReferenceDensityBounds HarmonicRaisingModel
  ReferenceHarmonicRaisingAdjunction ReferenceRaisingAdjunctionEndpoint ConformalDepth

lemma inner_sphereHarmonicPartialSum (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (n : ℕ) (u v : SphereL2) :
    ⟪sphereHarmonicPartialSum hO hD n u,v⟫_ℝ =
      ∑ k ∈ Finset.range n, ⟪sphereHarmonicCoordinate hO hD k u,
        sphereHarmonicCoordinate hO hD k v⟫_ℝ := by
  rw [sphereHarmonicPartialSum_apply,sum_inner]
  apply Finset.sum_congr rfl
  intro k _
  change ⟪(sphereHarmonicCoordinate hO hD k u : SphereL2),v⟫_ℝ = _
  calc
    _ = ⟪v,(sphereHarmonicCoordinate hO hD k u : SphereL2)⟫_ℝ := real_inner_comm _ _
    _ = ⟪sphereHarmonicCoordinate hO hD k v,sphereHarmonicCoordinate hO hD k u⟫_ℝ :=
      inner_sphereHarmonicCoordinate_right hO hD k v _
    _ = _ := real_inner_comm _ _

/-- Finite coordinate integrals; each integrand is compact and integrable. -/
lemma integral_reference_partial_pairing (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (U V : R3 → SphereL2) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hcompact : HasCompactSupport U) (n : ℕ) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪sphereHarmonicPartialSum hO hD n (U x),V x⟫_ℝ) =
      ∑ k ∈ Finset.range n, ∫ x : R3, referenceDensityFamily g L (lam,x) *
        ⟪sphereHarmonicCoordinate hO hD k (U x),sphereHarmonicCoordinate hO hD k (V x)⟫_ℝ := by
  simp only [inner_sphereHarmonicPartialSum,Finset.mul_sum]
  apply integral_finsetSum
  intro k _
  exact ((continuous_referenceBaseDensity g hg L lam).mul
    (((sphereHarmonicCoordinate hO hD k).continuous.comp hU.continuous).inner
      ((sphereHarmonicCoordinate hO hD k).continuous.comp hV.continuous))).integrable_of_hasCompactSupport
        (hasCompactSupport_real_inner_left _ _
          (hasCompactSupport_sphereHarmonicCoordinate hO hD k U hcompact)).mul_left

/-- Genuine reference-base L2 convergence supplies the full pairing limit. -/
lemma tendsto_integral_reference_partial_pairing (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (U V : R3 → SphereL2) (hU : Continuous U) (hV : Continuous V)
    (hcompactU : HasCompactSupport U) (hcompactV : HasCompactSupport V) :
    Tendsto (fun n : ℕ => ∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪sphereHarmonicPartialSum hO hD n (U x),V x⟫_ℝ) atTop
      (𝓝 (∫ x : R3, referenceDensityFamily g L (lam,x) * ⟪U x,V x⟫_ℝ)) := by
  have h := (tendsto_referenceBaseLift_sphereHarmonicPartialSum g hg L lam hO hD U hU hcompactU).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := referenceBaseLift g hg L lam V hV hcompactV))
  simpa only [inner_referenceBaseLift] using h

/-- Actual adjacent-degree adjunction, including k=0 and its H1-to-H0 output. -/
lemma compact_referenceAllMode_adjunction_degree (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) (k : ℕ) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪sphereHarmonicCoordinate hO hD (k+1)
          (referenceAllModeRaising hF hO hD g hg L lam f G hG x),
        sphereHarmonicCoordinate hO hD (k+1) (ambientSphereL2 H hH x)⟫_ℝ) =
      ∫ x : R3, referenceDensityFamily g L (lam,x) *
        ⟪sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG x),
          sphereHarmonicCoordinate hO hD k
            (referenceAllModeAdjointExpression hF hO hD g hg L lam f H hH x)⟫_ℝ := by
  have hUg := contDiff_ambientSphereL2 G hG
  have hVh := contDiff_ambientSphereL2 H hH
  have hcU := hasCompactSupport_ambientSphereL2 G hG K hK hzG
  have hcV := hasCompactSupport_ambientSphereL2 H hH J hJ hzH
  cases k with
  | zero =>
      have hraise (x : R3) : sphereHarmonicCoordinate hO hD (0+1)
          (referenceAllModeRaising hF hO hD g hg L lam f G hG x) =
          referenceHarmonicConstantRaising hF g L lam
            (fun y => sphereHarmonicCoordinate hO hD 0 (ambientSphereL2 G hG y)) x :=
        referenceAllModeRaising_coordinate_one hF hO hD g hg L lam f G hG x
      simp only [hraise,referenceAllModeAdjointExpression_coordinate_zero]
      exact compact_referenceHarmonicConstantRaising_adjoint hF hO hD g hg L lam
        (fun x => sphereHarmonicCoordinate hO hD 0 (ambientSphereL2 G hG x))
        (fun x => sphereHarmonicCoordinate hO hD 1 (ambientSphereL2 H hH x))
        (contDiff_sphereHarmonicCoordinate hO hD 0 _ hUg)
        (contDiff_sphereHarmonicCoordinate hO hD 1 _ hVh)
        (hasCompactSupport_sphereHarmonicCoordinate hO hD 0 _ hcU)
        (hasCompactSupport_sphereHarmonicCoordinate hO hD 1 _ hcV)
  | succ m =>
      simp_rw [referenceAllModeRaising_coordinate,
        referenceAllModeAdjointExpression_coordinate_positive]
      exact compact_referenceHarmonicRaising_adjoint hF hO hD g hg L lam m
        (fun x => sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG x))
        (fun x => sphereHarmonicCoordinate hO hD ((m+1)+1) (ambientSphereL2 H hH x)) f
        (contDiff_sphereHarmonicCoordinate hO hD (m+1) _ hUg)
        (contDiff_sphereHarmonicCoordinate hO hD ((m+1)+1) _ hVh) hf
        (hasCompactSupport_sphereHarmonicCoordinate hO hD (m+1) _ hcU)
        (hasCompactSupport_sphereHarmonicCoordinate hO hD ((m+1)+1) _ hcV)

/-- Full finite pairing identity with the necessary one-degree shift. -/
lemma compact_referenceAllMode_adjunction_partial (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) (n : ℕ) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪sphereHarmonicPartialSum hO hD (n+1)
          (referenceAllModeRaising hF hO hD g hg L lam f G hG x),ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x : R3, referenceDensityFamily g L (lam,x) *
        ⟪sphereHarmonicPartialSum hO hD n (ambientSphereL2 G hG x),
          referenceAllModeAdjointExpression hF hO hD g hg L lam f H hH x⟫_ℝ := by
  rw [integral_reference_partial_pairing hO hD g hg L lam
      (referenceAllModeRaising hF hO hD g hg L lam f G hG) (ambientSphereL2 H hH)
      (contDiff_referenceAllModeRaising hF hO hD g hg L lam f hf G hG)
      (contDiff_ambientSphereL2 H hH)
      (hasCompactSupport_referenceAllModeRaising hF hO hD g hg L lam f G hG K hK hzG),
    integral_reference_partial_pairing hO hD g hg L lam (ambientSphereL2 G hG)
      (referenceAllModeAdjointExpression hF hO hD g hg L lam f H hH)
      (contDiff_ambientSphereL2 G hG)
      (contDiff_referenceAllModeAdjointExpression hF hO hD g hg L lam f hf H hH)
      (hasCompactSupport_ambientSphereL2 G hG K hK hzG),Finset.sum_range_succ']
  simp only [referenceAllModeRaising_coordinate_zero,inner_zero_left,mul_zero,integral_zero,zero_add,add_zero]
  apply Finset.sum_congr rfl
  intro k _
  exact compact_referenceAllMode_adjunction_degree hF hO hD g hg L lam f hf G H hG hH
    K J hK hJ hzG hzH k

/-- Genuine full reference-volume/probability-sphere adjunction on the actual smooth compact core.
Every harmonic degree and the constant endpoint are retained. -/
theorem compact_referenceAllModeRaising_adjointExpression (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪referenceAllModeRaising hF hO hD g hg L lam f G hG x,ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x : R3, referenceDensityFamily g L (lam,x) *
        ⟪ambientSphereL2 G hG x,
          referenceAllModeAdjointExpression hF hO hD g hg L lam f H hH x⟫_ℝ := by
  have hleft := (tendsto_integral_reference_partial_pairing hO hD g hg L lam
    (referenceAllModeRaising hF hO hD g hg L lam f G hG) (ambientSphereL2 H hH)
    (contDiff_referenceAllModeRaising hF hO hD g hg L lam f hf G hG).continuous
    (contDiff_ambientSphereL2 H hH).continuous
    (hasCompactSupport_referenceAllModeRaising hF hO hD g hg L lam f G hG K hK hzG)
    (hasCompactSupport_ambientSphereL2 H hH J hJ hzH)).comp (tendsto_add_atTop_nat 1)
  have hright := tendsto_integral_reference_partial_pairing hO hD g hg L lam
    (ambientSphereL2 G hG) (referenceAllModeAdjointExpression hF hO hD g hg L lam f H hH)
    (contDiff_ambientSphereL2 G hG).continuous
    (contDiff_referenceAllModeAdjointExpression hF hO hD g hg L lam f hf H hH).continuous
    (hasCompactSupport_ambientSphereL2 G hG K hK hzG)
    (hasCompactSupport_referenceAllModeAdjointExpression hF hO hD g hg L lam f H hH J hJ hzH)
  have he : (fun n : ℕ => ∫ x : R3, referenceDensityFamily g L (lam,x) *
      ⟪sphereHarmonicPartialSum hO hD (n+1)
        (referenceAllModeRaising hF hO hD g hg L lam f G hG x),ambientSphereL2 H hH x⟫_ℝ) =
      (fun n : ℕ => ∫ x : R3, referenceDensityFamily g L (lam,x) *
        ⟪sphereHarmonicPartialSum hO hD n (ambientSphereL2 G hG x),
          referenceAllModeAdjointExpression hF hO hD g hg L lam f H hH x⟫_ℝ) :=
    funext (compact_referenceAllMode_adjunction_partial hF hO hD g hg L lam f hf G H hG hH
      K J hK hJ hzG hzH)
  change Tendsto (fun n : ℕ => ∫ x : R3, referenceDensityFamily g L (lam,x) *
    ⟪sphereHarmonicPartialSum hO hD (n+1)
      (referenceAllModeRaising hF hO hD g hg L lam f G hG x),ambientSphereL2 H hH x⟫_ℝ) _ _ at hleft
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Actual source specialization, with profile smoothness discharged. -/
theorem compact_actual_referenceAllModeRaising_adjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (g1 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x : R3, referenceDensityFamily g1 L (lam,x) *
      ⟪referenceAllModeRaising hF hO hD g1 hg1 L lam (referenceLogRadius δ R p L) G hG x,
        ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪ambientSphereL2 G hG x,referenceAllModeAdjointExpression hF hO hD g1 hg1 L lam
          (referenceLogRadius δ R p L) H hH x⟫_ℝ :=
  compact_referenceAllModeRaising_adjointExpression hF hO hD g1 hg1 L lam _
    (contDiff_referenceLogRadius_actual δ R L p hδ hR) G H hG hH K J hK hJ hzG hzH

end OAI.AnisotropicCalderon.ActualReferenceFullAdjunction
