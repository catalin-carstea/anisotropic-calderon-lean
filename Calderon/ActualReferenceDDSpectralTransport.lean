import Calderon.ActualReferenceDDCoefficientSmallness

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceDDSpectralTransport
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  SmoothAmbientAngularCasimir AmbientAngularShift SmoothMetricFrame MovingFrameConnection
  AmbientReferenceRaising AmbientReferenceCovariantCore ActualReferenceParallelRaising
  ActualReferenceScaledRaisingTransport ActualReferenceModelTrace ActualReferenceDecomposition
  ActualReferenceOrdinaryPrincipal ActualReferenceDDNormalizedCoefficient ActualReferenceDDGeometryBounds
  ActualReferenceDDCoefficientSmallness ActualPhysicalPureAngular ActualPhysicalPureReferenceCancellation
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedNative ActualPhysicalMixedFirst
  ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualHorizontalNormBridge
  ActualNormalizedSphereRotation SmoothSphereRotationProjection ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds MetricOperator ActualScalarPrincipalAdjoint ActualBalancedFirstPrincipalError
  ScalarBaseAdjoint PrincipalCommutator ConformalDepth RadiusProfile WeightedBaseSpectral
  SectionFiveErrorForms BaseDensityAdjoint

/- Actual native all-degree spectral graph transport and exact half derivative pairing.
   No raw operator is declared bounded. Full U/E/F/drift and higher uniform jets remain separate. -/

def PreservesSphereSpectralGraphs
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (A : SphereL2 →L[ℝ] SphereL2) : Prop :=
  ∀ (w : ℕ → ℝ) (u U : SphereL2), (u,U) ∈ spectralGraph hO hD w →
    (A u,A U) ∈ spectralGraph hO hD w

lemma preservesSphereSpectralGraphs_id
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    : PreservesSphereSpectralGraphs hO hD (ContinuousLinearMap.id ℝ SphereL2) := by
  intro w u U hU
  exact hU

lemma preservesSphereSpectralGraphs_add
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (A B : SphereL2 →L[ℝ] SphereL2)
    (hA : PreservesSphereSpectralGraphs hO hD A)
    (hB : PreservesSphereSpectralGraphs hO hD B) :
    PreservesSphereSpectralGraphs hO hD (A + B) := by
  intro w u U hU k
  change sphereHarmonicCoordinate hO hD k ((A + B) U) =
    w k • sphereHarmonicCoordinate hO hD k ((A + B) u)
  simp only [ContinuousLinearMap.add_apply,map_add]
  rw [hA w u U hU k,hB w u U hU k,smul_add]

lemma preservesSphereSpectralGraphs_sub
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (A B : SphereL2 →L[ℝ] SphereL2)
    (hA : PreservesSphereSpectralGraphs hO hD A)
    (hB : PreservesSphereSpectralGraphs hO hD B) :
    PreservesSphereSpectralGraphs hO hD (A - B) := by
  intro w u U hU k
  change sphereHarmonicCoordinate hO hD k ((A - B) U) =
    w k • sphereHarmonicCoordinate hO hD k ((A - B) u)
  simp only [ContinuousLinearMap.sub_apply,map_sub]
  rw [hA w u U hU k,hB w u U hU k,smul_sub]

lemma preservesSphereSpectralGraphs_smul
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : ℝ) (A : SphereL2 →L[ℝ] SphereL2)
    (hA : PreservesSphereSpectralGraphs hO hD A) :
    PreservesSphereSpectralGraphs hO hD (c • A) := by
  intro w u U hU k
  change sphereHarmonicCoordinate hO hD k ((c • A) U) =
    w k • sphereHarmonicCoordinate hO hD k ((c • A) u)
  simp only [ContinuousLinearMap.smul_apply,map_smul]
  rw [hA w u U hU k,smul_comm]

lemma preservesSphereSpectralGraphs_comp
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (A B : SphereL2 →L[ℝ] SphereL2)
    (hA : PreservesSphereSpectralGraphs hO hD A)
    (hB : PreservesSphereSpectralGraphs hO hD B) :
    PreservesSphereSpectralGraphs hO hD (A.comp B) := by
  intro w u U hU
  exact hA w (B u) (B U) (hB w u U hU)

lemma preservesSphereSpectralGraphs_sum
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    {ι : Type*} [Fintype ι] (A : ι → SphereL2 →L[ℝ] SphereL2)
    (hA : ∀ i, PreservesSphereSpectralGraphs hO hD (A i)) :
    PreservesSphereSpectralGraphs hO hD (∑ i, A i) := by
  intro w u U hU k
  change sphereHarmonicCoordinate hO hD k ((∑ i, A i) U) =
    w k • sphereHarmonicCoordinate hO hD k ((∑ i, A i) u)
  simp only [ContinuousLinearMap.sum_apply,map_sum]
  simp_rw [hA _ w u U hU k]
  rw [Finset.smul_sum]

lemma preservesSphereSpectralGraphs_inverseDegreeMultiplier
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    : PreservesSphereSpectralGraphs hO hD (inverseDegreeMultiplier hO hD) := by
  intro w u U hU k
  change sphereHarmonicCoordinate hO hD k (inverseDegreeMultiplier hO hD U) =
    w k • sphereHarmonicCoordinate hO hD k (inverseDegreeMultiplier hO hD u)
  rw [inverseDegreeMultiplier_coordinate hO hD U k,
    inverseDegreeMultiplier_coordinate hO hD u k,hU k,smul_comm]

lemma normalizedRotation_coordinate
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b : Fin 3) (u : SphereL2) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (normalizedRotation hO hD a b u) =
      inverseDegreeWeight k • harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k u) := by
  have hN := normalizedRotationOutput_graph hO hD a b u k
  change sphereHarmonicCoordinate hO hD k (normalizedRotation hO hD a b u) =
    harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k (inverseDegreeMultiplier hO hD u)) at hN
  rw [inverseDegreeMultiplier_coordinate hO hD u k,map_smul] at hN
  exact hN

lemma preservesSphereSpectralGraphs_normalizedRotation
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (a b : Fin 3) : PreservesSphereSpectralGraphs hO hD (normalizedRotation hO hD a b) := by
  intro w u U hU k
  change sphereHarmonicCoordinate hO hD k (normalizedRotation hO hD a b U) =
    w k • sphereHarmonicCoordinate hO hD k (normalizedRotation hO hD a b u)
  rw [normalizedRotation_coordinate hO hD a b U k,
    normalizedRotation_coordinate hO hD a b u k,hU k,map_smul,smul_comm]

lemma preservesSphereSpectralGraphs_normalizedReferenceAngularConnection
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (x X : R3) :
    PreservesSphereSpectralGraphs hO hD (normalizedReferenceAngularConnection hO hD g L lam x X) := by
  unfold normalizedReferenceAngularConnection
  apply preservesSphereSpectralGraphs_smul
  apply preservesSphereSpectralGraphs_sum
  intro i
  apply preservesSphereSpectralGraphs_sum
  intro j
  exact preservesSphereSpectralGraphs_smul hO hD _ _
    (preservesSphereSpectralGraphs_normalizedRotation hO hD i j)

lemma preservesSphereSpectralGraphs_directionalFDeriv
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
    (hgraph : ∀ y, PreservesSphereSpectralGraphs hO hD (A y)) (x X : R3) :
    PreservesSphereSpectralGraphs hO hD (directionalFDeriv X A x) := by
  intro w u U hU k
  have hAu : ContDiff ℝ ∞ (fun y => A y u) := hA.clm_apply contDiff_const
  have hAU : ContDiff ℝ ∞ (fun y => A y U) := hA.clm_apply contDiff_const
  have hd := directionalDeriv_spectral_family hO hD (fun _ k => w k) X
    (fun y => A y u) (fun y => A y U) hAu hAU (fun _ => contDiff_const)
    (fun y => hgraph y w u U hU) x k
  simp only [directionalDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,zero_smul,zero_add] at hd
  have hApp (v : SphereL2) : fderiv ℝ (fun y => A y v) x X = (fderiv ℝ A x X) v := by
    have ht := directionalFDeriv_clm_apply X A (fun _ : R3 => v) hA contDiff_const x
    simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,map_zero,add_zero] using ht
  rw [hApp U,hApp u] at hd
  exact hd

lemma preservesSphereSpectralGraphs_referenceAngularConnection_directional
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : Fin 3) (x X : R3) :
    PreservesSphereSpectralGraphs hO hD (directionalFDeriv X
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y
        (referenceMetricGramFrame g L (lam,y) b)) x) := by
  exact preservesSphereSpectralGraphs_directionalFDeriv hO hD _
    (contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam b)
    (fun y => preservesSphereSpectralGraphs_normalizedReferenceAngularConnection hO hD g L lam y
      (referenceMetricGramFrame g L (lam,y) b)) x X

lemma preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3) (x : R3) :
    PreservesSphereSpectralGraphs hO hD (referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a x) := by
  unfold referenceWeightedZeroBaseNormalizedCoefficient
  apply preservesSphereSpectralGraphs_add
  · exact preservesSphereSpectralGraphs_normalizedReferenceAngularConnection hO hD g L lam x _
  · apply preservesSphereSpectralGraphs_smul
    exact preservesSphereSpectralGraphs_sub hO hD _ _
      (preservesSphereSpectralGraphs_id hO hD) (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)

lemma preservesSphereSpectralGraphs_referenceCovectorFirstBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b j : Fin 3) (x : R3) :
    PreservesSphereSpectralGraphs hO hD (referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j x) := by
  unfold referenceCovectorFirstBaseNormalizedCoefficient
  apply preservesSphereSpectralGraphs_add
  · apply preservesSphereSpectralGraphs_add
    · apply preservesSphereSpectralGraphs_add
      · exact preservesSphereSpectralGraphs_smul hO hD _ _
          (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
      · exact preservesSphereSpectralGraphs_smul hO hD _ _
          (preservesSphereSpectralGraphs_normalizedReferenceAngularConnection hO hD g L lam x _)
    · exact preservesSphereSpectralGraphs_smul hO hD _ _
        (preservesSphereSpectralGraphs_normalizedReferenceAngularConnection hO hD g L lam x _)
  · apply preservesSphereSpectralGraphs_smul
    exact preservesSphereSpectralGraphs_sub hO hD _ _
      (preservesSphereSpectralGraphs_id hO hD) (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)

lemma preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (j : Fin 3) (x : R3) :
    PreservesSphereSpectralGraphs hO hD (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x) := by
  rw [referenceWeightedFirstBaseNormalizedCoefficient_eq_sum hO hD g hg L lam δ R p h j x]
  apply preservesSphereSpectralGraphs_smul
  apply preservesSphereSpectralGraphs_sum
  intro a
  apply preservesSphereSpectralGraphs_sum
  intro b
  exact preservesSphereSpectralGraphs_smul hO hD _ _
    (preservesSphereSpectralGraphs_referenceCovectorFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p a b j x)

lemma preservesSphereSpectralGraphs_referenceCovectorZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3) (x : R3) :
    PreservesSphereSpectralGraphs hO hD (referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b x) := by
  have hDgraph := preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD
  have hZgraph (c : Fin 3) := preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p c x
  unfold referenceCovectorZeroBaseNormalizedCoefficient
  apply preservesSphereSpectralGraphs_add
  · apply preservesSphereSpectralGraphs_sub
    · apply preservesSphereSpectralGraphs_add
      · apply preservesSphereSpectralGraphs_add
        · exact preservesSphereSpectralGraphs_comp hO hD _ _
            (preservesSphereSpectralGraphs_referenceAngularConnection_directional hO hD g hg L lam b x _) hDgraph
        · apply preservesSphereSpectralGraphs_smul
          exact preservesSphereSpectralGraphs_sub hO hD _ _ hDgraph
            (preservesSphereSpectralGraphs_comp hO hD _ _ hDgraph hDgraph)
      · exact preservesSphereSpectralGraphs_comp hO hD _ _
          (preservesSphereSpectralGraphs_normalizedReferenceAngularConnection hO hD g L lam x _) (hZgraph b)
    · apply preservesSphereSpectralGraphs_sum
      intro c
      apply preservesSphereSpectralGraphs_smul
      exact preservesSphereSpectralGraphs_comp hO hD _ _ (hZgraph c) hDgraph
  · apply preservesSphereSpectralGraphs_smul
    exact preservesSphereSpectralGraphs_sub hO hD _ _ (hZgraph b)
      (preservesSphereSpectralGraphs_comp hO hD _ _ (hZgraph b) hDgraph)

lemma preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (x : R3) :
    PreservesSphereSpectralGraphs hO hD (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x) := by
  unfold referenceWeightedZeroBaseNormalizedCoefficientTrace
  apply preservesSphereSpectralGraphs_smul
  apply preservesSphereSpectralGraphs_sum
  intro a
  apply preservesSphereSpectralGraphs_sum
  intro b
  exact preservesSphereSpectralGraphs_smul hO hD _ _
    (preservesSphereSpectralGraphs_referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b x)

lemma ambientBesselField_between_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hs : s ≤ 2) (ht : t ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientBesselField hO hD s hs G hG x,ambientBesselField hO hD t ht G hG x) ∈
      sphereBesselGraph hO hD (t-s) := by
  intro k
  change sphereHarmonicCoordinate hO hD k (ambientBesselField hO hD t ht G hG x) =
    besselWeight (t-s) k • sphereHarmonicCoordinate hO hD k (ambientBesselField hO hD s hs G hG x)
  rw [ambientBesselField_graph hO hD t ht G hG x k,
    ambientBesselField_graph hO hD s hs G hG x k,smul_smul,← besselWeight_add]
  rw [sub_add_cancel]

lemma directional_ambientBesselField_between_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hs : s ≤ 2) (ht : t ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    (directionalFDeriv X (ambientBesselField hO hD s hs G hG) x,
      directionalFDeriv X (ambientBesselField hO hD t ht G hG) x) ∈ sphereBesselGraph hO hD (t-s) := by
  exact directionalDeriv_besselGraph hO hD (t-s) X _ _
    (contDiff_ambientBesselField hO hD s hs G hG)
    (contDiff_ambientBesselField hO hD t ht G hG)
    (ambientBesselField_between_graph hO hD s t hs ht G hG) x

theorem referenceWeightedFirstBaseTrace_inner_half_identity
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ⟪referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ =
      ∑ j : Fin 3, ⟪referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
        ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ := by
  rw [referenceWeightedFirstBaseTrace_eq_normalizedCoefficient hO hD g hg L lam δ R p h G hG x,
    sum_inner]
  apply Finset.sum_congr rfl
  intro j _
  have hbetween := directional_ambientBesselField_between_graph hO hD 1 (1/2)
    (by norm_num) (by norm_num) G hG x (coordinateDirection j)
  have houtput := preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x
    (besselWeight (-(1/2))) _ _ (by convert hbetween using 1 <;> norm_num [sphereBesselGraph])
  exact inner_besselGraph_inverse_pair hO hD (1/2) _ _ _ _ houtput
    (ambientBesselField_graph hO hD (1/2) (by norm_num) G hG x)

theorem referenceWeightedZeroBaseTrace_inner_half_identity
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ⟪referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ =
      ⟪referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x
        (ambientBesselField hO hD (3/2) (by norm_num) G hG x),
        ambientBesselField hO hD (1/2) (by norm_num) G hG x⟫_ℝ := by
  rw [referenceWeightedZeroBaseTrace_eq_normalizedCoefficient hO hD g hg L lam δ R p h G hG x]
  have hbetween := ambientBesselField_between_graph hO hD 2 (3/2)
    (by norm_num) (by norm_num) G hG x
  have houtput := preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x
    (besselWeight (-(1/2))) _ _ (by convert hbetween using 1 <;> norm_num [sphereBesselGraph])
  exact inner_besselGraph_inverse_pair hO hD (1/2) _ _ _ _ houtput
    (ambientBesselField_graph hO hD (1/2) (by norm_num) G hG x)

end OAI.AnisotropicCalderon.ActualReferenceDDSpectralTransport
