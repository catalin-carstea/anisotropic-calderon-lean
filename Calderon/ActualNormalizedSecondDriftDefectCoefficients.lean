import Calderon.ActualNormalizedSecondDriftDefectWeightedJets
import Calderon.ActualReferenceDDHigherSpectralGraphs

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondDriftDefectCoefficients
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection ActualReferenceParallelRaising
  ActualReferenceModelTrace ActualReferenceOrdinaryPrincipal ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDSpectralTransport ActualReferenceDDGeometryBounds
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherProfileJets
  ActualReferenceDDHigherCLMProducts ActualReferenceDDHigherSpectralGraphs
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftNativeAdjunction ActualNormalizedSecondDriftWeightedCoefficients
  ActualNormalizedSecondDriftDefectWeightedJets ActualScalarPrincipalAdjoint
  ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile

/- Actual native b2 adjoint-defect coefficients. Genuine independent
   adjoint-minus-U parent pays domains/density/support; no full E/F/H identity. -/

def normalizedSecondDriftAngularConnectionNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  referenceRadius δ R p L x • ∑ a : Fin 3,
  normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
    (normalizedReferenceAngularConnection hO hD g1 L lam x (referenceMetricGramFrame g1 L (lam,x) a)).comp
      (inverseDegreeMultiplier hO hD)

def normalizedSecondDriftDefectFirstNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  (-2 : ℝ) • normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x

def normalizedSecondDriftDefectZeroNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  (-2 : ℝ) • normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p x -
  normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p x •
    (inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD)

lemma normalizedSecondDriftAngularConnectionNormalizedCoefficient_apply_two (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (hg1 : IsAdmissibleMetric g1)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
  normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p x (ambientBesselField hO hD 2 (by norm_num) G hG x) =
    normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x := by
  unfold normalizedSecondDriftAngularConnectionNormalizedCoefficient normalizedSecondDriftAngularConnectionField
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  rw [inverseDegreeMultiplier_ambientBesselField_two hO hD G hG x]


theorem normalizedSecondWeightedDriftAdjointDefect_normalized_representation (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
  normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x =
    (∑ j : Fin 3, normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x)) +
    normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p x (ambientBesselField hO hD 2 (by norm_num) G hG x) := by
  have hf : (∑ j : Fin 3, normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
      (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x)) =
      (-2 : ℝ) • normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x := by
    unfold normalizedSecondDriftDefectFirstNormalizedCoefficient normalizedSecondDriftFirstNormalizedCoefficient
      normalizedSecondDriftFirstBaseField
    simp only [ContinuousLinearMap.smul_apply,Finset.smul_sum,smul_smul]
    simp_rw [inverseDegreeMultiplier_directional_ambientBesselField_one hO hD G hG x]
  have hz : normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p x
      (ambientBesselField hO hD 2 (by norm_num) G hG x) =
      (-2 : ℝ) • normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x -
        normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p x • ambientSphereL2 G hG x := by
    unfold normalizedSecondDriftDefectZeroNormalizedCoefficient
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply]
    rw [normalizedSecondDriftAngularConnectionNormalizedCoefficient_apply_two hO hD g1 g2 L lam δ R p hg1 G hG x,
      inverseDegreeMultiplier_ambientBesselField_two hO hD G hG x,
      inverseDegreeMultiplier_ambientBesselField_one hO hD G hG x]
  rw [normalizedSecondWeightedDriftAdjointDefect_normal_form hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR x,hf,hz]
  module


lemma contDiff_normalizedSecondDriftAngularConnectionNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
  ContDiff ℝ ∞ (normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p) := by
  have hb (a : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)) :=
    (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
      (contDiff_const.prodMk contDiff_id)
  have hK (a : Fin 3) := contDiff_normalizedReferenceAngularConnection_frame hO hD g1 hg1 L lam a
  have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
        (normalizedReferenceAngularConnection hO hD g1 L lam x
          (referenceMetricGramFrame g1 L (lam,x) a)).comp (inverseDegreeMultiplier hO hD)) :=
    ContDiff.sum (fun a _ => (hb a).smul ((hK a).clm_comp contDiff_const))
  unfold normalizedSecondDriftAngularConnectionNormalizedCoefficient
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul hs


lemma contDiff_normalizedSecondDriftDefectFirstNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
  ContDiff ℝ ∞ (normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j) := by
  unfold normalizedSecondDriftDefectFirstNormalizedCoefficient
  exact (contDiff_normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR j).const_smul (-2 : ℝ)


lemma contDiff_normalizedSecondDriftDefectZeroNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
  ContDiff ℝ ∞ (normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p) := by
  unfold normalizedSecondDriftDefectZeroNormalizedCoefficient
  exact ((contDiff_normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p hg1 hg2 hδ hR).const_smul (-2 : ℝ)).sub
    ((contDiff_normalizedSecondDriftDensityDivergence g1 g2 hg1 hg2 L lam δ R p hδ hR).smul contDiff_const)


lemma preservesSphereSpectralGraphs_normalizedSecondDriftAngularConnectionNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (x : R3) :
  PreservesSphereSpectralGraphs hO hD (normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p x) := by
  unfold normalizedSecondDriftAngularConnectionNormalizedCoefficient
  apply preservesSphereSpectralGraphs_smul
  apply preservesSphereSpectralGraphs_sum
  intro a
  apply preservesSphereSpectralGraphs_smul
  exact preservesSphereSpectralGraphs_comp hO hD _ _
    (preservesSphereSpectralGraphs_normalizedReferenceAngularConnection hO hD g1 L lam x _)
    (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)


lemma preservesSphereSpectralGraphs_normalizedSecondDriftDefectFirstNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (x : R3) :
  PreservesSphereSpectralGraphs hO hD (normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x) := by
  unfold normalizedSecondDriftDefectFirstNormalizedCoefficient normalizedSecondDriftFirstNormalizedCoefficient
  apply preservesSphereSpectralGraphs_smul
  exact preservesSphereSpectralGraphs_smul hO hD _ _
    (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)


lemma preservesSphereSpectralGraphs_normalizedSecondDriftDefectZeroNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (x : R3) :
  PreservesSphereSpectralGraphs hO hD (normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p x) := by
  unfold normalizedSecondDriftDefectZeroNormalizedCoefficient
  apply preservesSphereSpectralGraphs_sub
  · exact preservesSphereSpectralGraphs_smul hO hD _ _
      (preservesSphereSpectralGraphs_normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p x)
  · apply preservesSphereSpectralGraphs_smul
    exact preservesSphereSpectralGraphs_comp hO hD _ _
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)


lemma preservesSphereSpectralGraphs_coordinateWord_normalizedSecondDriftDefectFirstNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) (w : List (Fin 3)) (x : R3) :
  PreservesSphereSpectralGraphs hO hD
    (coordinateFieldWordPartial w (normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j) x) := by
  exact preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD _
    (contDiff_normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p hg1 hg2 hδ hR j)
    (fun y => preservesSphereSpectralGraphs_normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j y) w x


lemma preservesSphereSpectralGraphs_coordinateWord_normalizedSecondDriftDefectZeroNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (w : List (Fin 3)) (x : R3) :
  PreservesSphereSpectralGraphs hO hD
    (coordinateFieldWordPartial w (normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p) x) := by
  exact preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD _
    (contDiff_normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p hg1 hg2 hδ hR)
    (fun y => preservesSphereSpectralGraphs_normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p y) w x


theorem exists_normalizedSecondDriftAngularConnectionNormalized_uniform_coordinate_word_jet_bound (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) (N : ℕ) :
  ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
    ∀ x ∈ K,
    let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g1 lam) L)
      (fun y => Real.log (referenceRadius δ R p L y)) x;
    1 ≤ beta → HasCoordinateWordJetBound N (normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p) x
      (C*referenceRadius δ R p L x) beta 0 := by
  obtain ⟨Mb,hMb,hb2⟩ := exists_normalizedSecondDrift_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L K hK N
  obtain ⟨Mk,hMk,hgeom⟩ := exists_referenceDD_fixed_geometry_uniform_coordinate_word_bounds hO hD g1 hg1 L K hK N
  obtain ⟨Cr,hCr,hradius⟩ := exists_referenceRadius_uniform_coordinate_word_bounds g1 hg1 L hL K hK N
  let T : ℝ := (2:ℝ)^N
  let C : ℝ := 3*T^3*Cr*Mb*Mk
  have hMb0 : 0 ≤ Mb := by linarith
  have hMk0 : 0 ≤ Mk := by linarith
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C,T]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb
  have hb0 : 0 ≤ beta := by linarith
  let r0 : ℝ := referenceRadius δ R p L x
  have hr0 : 0 < r0 := referenceRadius_pos δ R p L x hδ hR
  have hDjet : HasCoordinateWordJetBound N (fun _ : R3 => inverseDegreeMultiplier hO hD) x 1 beta 0 :=
    hasCoordinateWordJetBound_const_normed N _ x 1 beta (norm_inverseDegreeMultiplier_le_one hO hD) hb0
  have hRjet : HasCoordinateWordJetBound N (referenceRadius δ R p L) x (Cr*r0) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,r0,Nat.zero_add,mul_assoc] using
      (hradius lam hlam δ hδ hδ1 R hR p hp x hx v hv).1
  have hbS (a : Fin 3) : ContDiff ℝ ∞
      (fun y : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y)) :=
    (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp (contDiff_const.prodMk contDiff_id)
  have hKS (a : Fin 3) := contDiff_normalizedReferenceAngularConnection_frame hO hD g1 hg1 L lam a
  have hbjet (a : Fin 3) : HasCoordinateWordJetBound N
      (fun y => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y)) x Mb beta 0 := by
    intro v hv
    have ht := (hb2 lam hlam x hx v hv).2 a
    have hconst : Mb ≤ Mb*beta^v.length := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hb (n := v.length)) hMb0
    simpa only [Real.norm_eq_abs,Nat.zero_add] using ht.trans hconst
  have hKjet (a : Fin 3) : HasCoordinateWordJetBound N
      (fun y => normalizedReferenceAngularConnection hO hD g1 L lam y
        (referenceMetricGramFrame g1 L (lam,y) a)) x Mk beta 0 := by
    intro v hv
    obtain ⟨_,_,_,_,_,hKa,_⟩ := hgeom lam hlam x hx v hv
    have hconst : Mk ≤ Mk*beta^v.length := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hb (n := v.length)) hMk0
    simpa only [Nat.zero_add] using (hKa a).trans hconst
  have hKD (a : Fin 3) : HasCoordinateWordJetBound N
      (fun y => (normalizedReferenceAngularConnection hO hD g1 L lam y
        (referenceMetricGramFrame g1 L (lam,y) a)).comp (inverseDegreeMultiplier hO hD))
      x (T*Mk) beta 0 := by
    have ht := hasCoordinateWordJetBound_clm_comp N _ _ (hKS a) contDiff_const
      x Mk 1 beta 0 0 hMk0 (by norm_num) hb0 (hKjet a) hDjet
    simpa only [T,mul_one] using ht
  have hTermS (a : Fin 3) : ContDiff ℝ ∞ (fun y : R3 =>
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        (normalizedReferenceAngularConnection hO hD g1 L lam y
          (referenceMetricGramFrame g1 L (lam,y) a)).comp (inverseDegreeMultiplier hO hD)) :=
    (hbS a).smul ((hKS a).clm_comp contDiff_const)
  have hTerm (a : Fin 3) : HasCoordinateWordJetBound N (fun y =>
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        (normalizedReferenceAngularConnection hO hD g1 L lam y
          (referenceMetricGramFrame g1 L (lam,y) a)).comp (inverseDegreeMultiplier hO hD))
      x (T^2*Mb*Mk) beta 0 := by
    have ht := hasCoordinateWordJetBound_smul N _ _ (hbS a) ((hKS a).clm_comp contDiff_const)
      x Mb (T*Mk) beta 0 0 hMb0 (mul_nonneg hT0 hMk0) hb0 (hbjet a) (hKD a)
    have he : (2:ℝ)^N*Mb*(T*Mk)=T^2*Mb*Mk := by dsimp [T]; ring
    rwa [he] at ht
  have hTotal : HasCoordinateWordJetBound N (fun y => ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        (normalizedReferenceAngularConnection hO hD g1 L lam y
          (referenceMetricGramFrame g1 L (lam,y) a)).comp (inverseDegreeMultiplier hO hD))
      x (3*T^2*Mb*Mk) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum N _ hTermS x (T^2*Mb*Mk) beta 0 hTerm
    simpa only [Fintype.card_fin,Nat.cast_ofNat,mul_assoc] using ht
  have hTotalS : ContDiff ℝ ∞ (fun y : R3 => ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        (normalizedReferenceAngularConnection hO hD g1 L lam y
          (referenceMetricGramFrame g1 L (lam,y) a)).comp (inverseDegreeMultiplier hO hD)) :=
    ContDiff.sum (fun a _ => hTermS a)
  have ht := hasCoordinateWordJetBound_smul N (referenceRadius δ R p L) _
    (contDiff_referenceRadius_actual δ R p L hδ hR) hTotalS
    x (Cr*r0) (3*T^2*Mb*Mk) beta 0 0 (mul_nonneg hCr.le hr0.le) (by positivity) hb0 hRjet hTotal
  have he : (2:ℝ)^N*(Cr*r0)*(3*T^2*Mb*Mk)=C*r0 := by dsimp [C,T]; ring
  rw [he] at ht
  exact ht


theorem exists_normalizedSecondDriftDefectNormalized_uniform_coordinate_word_smallness (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) (N : ℕ) :
  ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
    ∀ eps : ℝ, 0 ≤ eps → ∀ x ∈ K,
    let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g1 lam) L)
      (fun y => Real.log (referenceRadius δ R p L y)) x;
    1 ≤ beta → referenceRadius δ R p L x*beta^2 ≤ eps →
    ∀ w : List (Fin 3), w.length ≤ N →
    (∀ j, ‖coordinateFieldWordPartial w (normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j) x‖ ≤
      (C*eps/beta^2)*beta^w.length) ∧
    ‖coordinateFieldWordPartial w (normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p) x‖ ≤
      (C*eps/beta)*beta^w.length := by
  obtain ⟨C1,hC1,hfirst⟩ := exists_normalizedSecondDriftNormalized_uniform_coordinate_word_smallness
    hO hD g1 g2 hg1 hg2 L hL K hK N
  obtain ⟨Ca,hCa,hang⟩ := exists_normalizedSecondDriftAngularConnectionNormalized_uniform_coordinate_word_jet_bound
    hO hD g1 g2 hg1 hg2 L hL K hK N
  obtain ⟨Cd,hCd,hdiv⟩ := exists_normalizedSecondDriftDensityDivergence_uniform_coordinate_word_jet_bound
    g1 g2 hg1 hg2 L hL K hK N
  let T : ℝ := (2:ℝ)^N
  let C : ℝ := 1+2*T*C1+2*T*Ca+T*Cd
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hFirstC : 2*T*C1 ≤ C := by
    have hrest : 0 ≤ 2*T*Ca+T*Cd := by positivity
    dsimp [C]
    linarith
  have hZeroC : 2*T*Ca+T*Cd ≤ C := by
    have hrest : 0 ≤ 2*T*C1 := by positivity
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps x hx beta hb hsmall w hw
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  let r0 : ℝ := referenceRadius δ R p L x
  have hr0 : 0 < r0 := referenceRadius_pos δ R p L x hδ hR
  have hMinusTwo : HasCoordinateWordJetBound N (fun _ : R3 => (-2 : ℝ)) x 2 beta 0 :=
    hasCoordinateWordJetBound_const_normed N (-2 : ℝ) x 2 beta (by norm_num) hb0
  have hDsq : ‖(inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD)‖ ≤ 1 := by
    calc
      ‖(inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD)‖ ≤
          ‖inverseDegreeMultiplier hO hD‖*‖inverseDegreeMultiplier hO hD‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1:ℝ)*1 := mul_le_mul (norm_inverseDegreeMultiplier_le_one hO hD)
        (norm_inverseDegreeMultiplier_le_one hO hD) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hDsqjet : HasCoordinateWordJetBound N (fun _ : R3 =>
      (inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD)) x 1 beta 0 :=
    hasCoordinateWordJetBound_const_normed N _ x 1 beta hDsq hb0
  have hOriginalFirst (j : Fin 3) : HasCoordinateWordJetBound N
      (normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j)
      x (C1*eps/beta^2) beta 0 := by
    intro v hv
    have ht := (hfirst lam hlam δ hδ hδ1 R hR p hp eps heps x hx hb hsmall v hv).1 j
    simpa only [Nat.zero_add] using ht
  have hFirst (j : Fin 3) : HasCoordinateWordJetBound N
      (normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j)
      x (2*T*C1*eps/beta^2) beta 0 := by
    have ht := hasCoordinateWordJetBound_smul N (fun _ : R3 => (-2 : ℝ))
      (normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j)
      contDiff_const (contDiff_normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR j)
      x 2 (C1*eps/beta^2) beta 0 0 (by norm_num) (by positivity) hb0 hMinusTwo (hOriginalFirst j)
    have he : (2:ℝ)^N*2*(C1*eps/beta^2)=2*T*C1*eps/beta^2 := by dsimp [T]; ring
    rwa [he] at ht
  have hAS := contDiff_normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p hg1 hg2 hδ hR
  have hDS := contDiff_normalizedSecondDriftDensityDivergence g1 g2 hg1 hg2 L lam δ R p hδ hR
  have hAngular : HasCoordinateWordJetBound N (fun y => (-2 : ℝ) •
      normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p y)
      x (2*T*Ca*r0) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul N (fun _ : R3 => (-2 : ℝ)) _ contDiff_const hAS
      x 2 (Ca*r0) beta 0 0 (by norm_num) (mul_nonneg hCa.le hr0.le) hb0 hMinusTwo
      (hang lam hlam δ hδ hδ1 R hR p hp x hx hb)
    have he : (2:ℝ)^N*2*(Ca*r0)=2*T*Ca*r0 := by dsimp [T]; ring
    rw [he] at ht
    exact hasCoordinateWordJetBound_raise_degree N _ x (2*T*Ca*r0) beta 0 1
      (by positivity) hb (by omega) ht
  have hDensity : HasCoordinateWordJetBound N (fun y =>
      normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p y •
        (inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD))
      x (T*Cd*r0) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul N _ _ hDS contDiff_const
      x (Cd*r0) 1 beta 1 0 (mul_nonneg hCd.le hr0.le) (by norm_num) hb0
      (hdiv lam hlam δ hδ hδ1 R hR p hp x hx hb) hDsqjet
    simpa only [T,mul_one,mul_assoc,Nat.add_zero] using ht
  have hZero : HasCoordinateWordJetBound N
      (normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p)
      x ((2*T*Ca+T*Cd)*r0) beta 1 := by
    have ht := hasCoordinateWordJetBound_sub N _ _ (hAS.const_smul (-2 : ℝ))
      (hDS.smul contDiff_const) x (2*T*Ca*r0) (T*Cd*r0) beta 1 hAngular hDensity
    have he : 2*T*Ca*r0+T*Cd*r0=(2*T*Ca+T*Cd)*r0 := by ring
    rwa [he] at ht
  have hFirstSmall : 2*T*C1*eps/beta^2 ≤ C*eps/beta^2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hFirstC heps) (pow_nonneg hb0 2)
  have hZeroSmall : (2*T*Ca+T*Cd)*r0*beta ≤ C*eps/beta := by
    apply (le_div_iff₀ hbpos).mpr
    calc
      (2*T*Ca+T*Cd)*r0*beta*beta = (2*T*Ca+T*Cd)*(r0*beta^2) := by ring
      _ ≤ (2*T*Ca+T*Cd)*eps := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ C*eps := mul_le_mul_of_nonneg_right hZeroC heps
  refine ⟨?_,?_⟩
  · intro j
    apply (hFirst j w hw).trans
    simpa only [Nat.zero_add] using mul_le_mul_of_nonneg_right hFirstSmall (pow_nonneg hb0 _)
  · apply (hZero w hw).trans
    calc
      ((2*T*Ca+T*Cd)*r0)*beta^(1+w.length) =
        ((2*T*Ca+T*Cd)*r0*beta)*beta^w.length := by rw [pow_add,pow_one]; ring
      _ ≤ (C*eps/beta)*beta^w.length := mul_le_mul_of_nonneg_right hZeroSmall (pow_nonneg hb0 _)


end OAI.AnisotropicCalderon.ActualNormalizedSecondDriftDefectCoefficients
