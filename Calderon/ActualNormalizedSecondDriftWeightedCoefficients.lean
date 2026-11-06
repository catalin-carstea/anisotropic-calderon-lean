import Calderon.ActualNormalizedSecondDriftAngularAllocation
import Calderon.ActualReferenceDDHigherActualCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondDriftWeightedCoefficients
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift SmoothSphereFields SmoothAngularApplication
  AmbientAngularShift AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDSpectralTransport
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherProfileJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherSpectralGraphs ActualReferenceDDHigherActualCoefficients
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondDriftAngularAllocation
  ActualScalarPrincipalAdjoint ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile

def normalizedSecondRaisingDriftNormalizedJoint (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (L : ℝ) (z : ℝ × R3) : SphereL2 →L[ℝ] SphereL2 :=
  ∑ a : Fin 3, normalizedSecondDriftFrameJoint g1 g2 L a z • normalizedRaising hF hO hD a

lemma contDiff_normalizedSecondDriftFirstNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
  ContDiff ℝ ∞ (normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j) :=
by
  have hb : ContDiff ℝ ∞ (fun x : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) := by
    simpa only [Function.comp_def, Function.id_def] using
      (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
        (contDiff_const.prodMk contDiff_id)
  unfold normalizedSecondDriftFirstNormalizedCoefficient
  exact ((contDiff_referenceRadius_actual δ R p L hδ hR).mul hb).smul contDiff_const

lemma contDiff_normalizedSecondDriftZeroNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
  ContDiff ℝ ∞ (normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p) :=
by
  have hb (a : Fin 3) : ContDiff ℝ ∞
      (fun x : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)) := by
    simpa only [Function.comp_def, Function.id_def] using
      (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
        (contDiff_const.prodMk contDiff_id)
  have hs : ContDiff ℝ ∞ (fun x : R3 => ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
        (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a x).comp
          (inverseDegreeMultiplier hO hD)) :=
    ContDiff.sum (fun a _ => (hb a).smul
      ((contDiff_referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p hδ hR a).clm_comp contDiff_const))
  unfold normalizedSecondDriftZeroNormalizedCoefficient
  exact (contDiff_referenceRadius_actual δ R p L hδ hR).smul hs

lemma contDiff_normalizedSecondRaisingDriftNormalizedJoint (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) : ContDiff ℝ ∞ (normalizedSecondRaisingDriftNormalizedJoint hF hO hD g1 g2 L) :=
by
  unfold normalizedSecondRaisingDriftNormalizedJoint
  exact ContDiff.sum (fun a _ =>
    (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).smul contDiff_const)

lemma normalizedSecondRaisingDriftNormalizedJoint_apply_one (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
  normalizedSecondRaisingDriftNormalizedJoint hF hO hD g1 g2 L (lam,x)
    (ambientBesselField hO hD 1 (by norm_num) G hG x) =
      normalizedSecondRaisingDriftField hF hO hD g1 g2 hg1 L lam δ R p G hG x :=
by
  unfold normalizedSecondRaisingDriftNormalizedJoint normalizedSecondRaisingDriftField ambientRaisingField
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

lemma preservesSphereSpectralGraphs_coordinateWord_normalizedSecondDriftFirstNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) (w : List (Fin 3)) (x : R3) :
  PreservesSphereSpectralGraphs hO hD
    (coordinateFieldWordPartial w (normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j) x) :=
by
  apply preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD _
    (contDiff_normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR j)
  intro y
  unfold normalizedSecondDriftFirstNormalizedCoefficient
  exact preservesSphereSpectralGraphs_smul hO hD _ _
    (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)

lemma preservesSphereSpectralGraphs_coordinateWord_normalizedSecondDriftZeroNormalizedCoefficient (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (w : List (Fin 3)) (x : R3) :
  PreservesSphereSpectralGraphs hO hD
    (coordinateFieldWordPartial w (normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p) x) :=
by
  apply preservesSphereSpectralGraphs_coordinateFieldWordPartial hO hD _
    (contDiff_normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR)
  intro y
  unfold normalizedSecondDriftZeroNormalizedCoefficient
  apply preservesSphereSpectralGraphs_smul
  apply preservesSphereSpectralGraphs_sum
  intro a
  apply preservesSphereSpectralGraphs_smul
  exact preservesSphereSpectralGraphs_comp hO hD _ _
    (preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a y)
    (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)

theorem exists_normalizedSecondRaisingDriftNormalized_uniform_coordinate_word_bounds (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) (N : ℕ) :
  ∃ C : ℝ, 1 ≤ C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
    ∀ w : List (Fin 3), w.length ≤ N →
      ‖coordinateFieldWordPartial w
        (fun y => normalizedSecondRaisingDriftNormalizedJoint hF hO hD g1 g2 L (lam,y)) x‖ ≤ C :=
by
  obtain ⟨C,hC,hbound⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun _ : Unit => normalizedSecondRaisingDriftNormalizedJoint hF hO hD g1 g2 L)
    (fun _ => contDiff_normalizedSecondRaisingDriftNormalizedJoint hF hO hD g1 g2 hg1 hg2 L) K hK N
  exact ⟨C,hC,fun lam hlam x hx w hw => hbound lam hlam x hx () w hw⟩

theorem exists_normalizedSecondDriftNormalized_uniform_coordinate_word_smallness (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) (N : ℕ) :
  ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
    ∀ eps : ℝ, 0 ≤ eps → ∀ x ∈ K,
    let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g1 lam) L)
      (fun y => Real.log (referenceRadius δ R p L y)) x
    1 ≤ beta → referenceRadius δ R p L x*beta^2 ≤ eps →
    ∀ w : List (Fin 3), w.length ≤ N →
    (∀ j, ‖coordinateFieldWordPartial w
      (normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j) x‖ ≤
        (C*eps/beta^2)*beta^w.length) ∧
    ‖coordinateFieldWordPartial w
      (normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p) x‖ ≤
        (C*eps/beta)*beta^w.length :=
by
  obtain ⟨M,hM,hdrift⟩ := exists_normalizedSecondDrift_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L K hK N
  obtain ⟨Cr,hCr,hradius⟩ := exists_referenceRadius_uniform_coordinate_word_bounds g1 hg1 L hL K hK N
  obtain ⟨A,hA,hpair⟩ := exists_referenceDD_normalized_pair_uniform_coordinate_word_bounds hO hD g1 hg1 L hL K hK N
  let T : ℝ := (2:ℝ)^N
  let Cf : ℝ := T^2*Cr*M
  let Cz : ℝ := 3*T^3*Cr*M*A
  let C : ℝ := 1+Cf+Cz
  have hM0 : 0 ≤ M := by linarith
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hCf0 : 0 ≤ Cf := by dsimp [Cf]; positivity
  have hCz0 : 0 ≤ Cz := by dsimp [Cz]; positivity
  have hCfC : Cf ≤ C := by dsimp [C]; linarith
  have hCzC : Cz ≤ C := by dsimp [C]; linarith
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps x hx beta hb hsmall w hw
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  let r0 : ℝ := referenceRadius δ R p L x
  have hr0 : 0 < r0 := referenceRadius_pos δ R p L x hδ hR
  have hDjet : HasCoordinateWordJetBound N (fun _ : R3 => inverseDegreeMultiplier hO hD) x 1 beta 0 :=
    hasCoordinateWordJetBound_const_normed N _ x 1 beta (norm_inverseDegreeMultiplier_le_one hO hD) hb0
  have hRjet : HasCoordinateWordJetBound N (referenceRadius δ R p L) x (Cr*r0) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs, r0, Nat.zero_add, mul_assoc] using
      (hradius lam hlam δ hδ hδ1 R hR p hp x hx v hv).1
  have hbc (j : Fin 3) : HasCoordinateWordJetBound N
      (fun y => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) x M beta 0 := by
    intro v hv
    have ht := (hdrift lam hlam x hx v hv).1 j
    have hpow := one_le_pow₀ hb (n := v.length)
    have hconst : M ≤ M*beta^v.length := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hM0
    simpa only [Real.norm_eq_abs, Nat.zero_add] using ht.trans hconst
  have hbf (a : Fin 3) : HasCoordinateWordJetBound N
      (fun y => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y)) x M beta 0 := by
    intro v hv
    have ht := (hdrift lam hlam x hx v hv).2 a
    have hpow := one_le_pow₀ hb (n := v.length)
    have hconst : M ≤ M*beta^v.length := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hM0
    simpa only [Real.norm_eq_abs, Nat.zero_add] using ht.trans hconst
  have hbcS (j : Fin 3) : ContDiff ℝ ∞
      (fun y : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) := by
    simpa only [Function.comp_def, Function.id_def] using
      (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
        (contDiff_const.prodMk contDiff_id)
  have hbfS (a : Fin 3) : ContDiff ℝ ∞
      (fun y : R3 => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y)) := by
    simpa only [Function.comp_def, Function.id_def] using
      (contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp
        (contDiff_const.prodMk contDiff_id)
  have hrS : ContDiff ℝ ∞ (referenceRadius δ R p L) := contDiff_referenceRadius_actual δ R p L hδ hR
  have hFirst (j : Fin 3) : HasCoordinateWordJetBound N
      (normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j) x (Cf*r0) beta 0 := by
    have hprod := hasCoordinateWordJetBound_mul N (referenceRadius δ R p L)
      (fun y => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y)) hrS (hbcS j)
      x (Cr*r0) M beta 0 0 (mul_nonneg hCr.le hr0.le) hM0 hb0 hRjet (hbc j)
    have ht := hasCoordinateWordJetBound_smul N
      (fun y => referenceRadius δ R p L y*normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,y))
      (fun _ : R3 => inverseDegreeMultiplier hO hD) (hrS.mul (hbcS j)) contDiff_const
      x ((2:ℝ)^N*(Cr*r0)*M) 1 beta 0 0 (by positivity) (by norm_num) hb0 hprod hDjet
    have he : (2:ℝ)^N*((2:ℝ)^N*(Cr*r0)*M)*1=Cf*r0 := by dsimp [Cf,T]; ring
    rw [he] at ht
    exact ht
  obtain ⟨hZjet,_,_⟩ := hpair lam hlam δ hδ hδ1 R hR p hp x hx hb
  have hZS (a : Fin 3) : ContDiff ℝ ∞
      (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a) :=
    contDiff_referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p hδ hR a
  have hZD (a : Fin 3) : HasCoordinateWordJetBound N
      (fun y => (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a y).comp
        (inverseDegreeMultiplier hO hD)) x (T*A) beta 1 := by
    have ht := hasCoordinateWordJetBound_clm_comp N
      (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a)
      (fun _ : R3 => inverseDegreeMultiplier hO hD) (hZS a) contDiff_const
      x A 1 beta 1 0 hA.le (by norm_num) hb0 (hZjet a) hDjet
    simpa only [T,mul_one,Nat.add_zero] using ht
  have hTermS (a : Fin 3) : ContDiff ℝ ∞ (fun y : R3 =>
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a y).comp
          (inverseDegreeMultiplier hO hD)) :=
    (hbfS a).smul ((hZS a).clm_comp contDiff_const)
  have hTerm (a : Fin 3) : HasCoordinateWordJetBound N
      (fun y => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a y).comp
          (inverseDegreeMultiplier hO hD)) x (T^2*M*A) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul N
      (fun y => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y))
      (fun y => (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a y).comp
        (inverseDegreeMultiplier hO hD)) (hbfS a) ((hZS a).clm_comp contDiff_const)
      x M (T*A) beta 0 1 hM0 (mul_nonneg hT0 hA.le) hb0 (hbf a) (hZD a)
    have he : (2:ℝ)^N*M*(T*A)=T^2*M*A := by dsimp [T]; ring
    rwa [he] at ht
  have hTotal : HasCoordinateWordJetBound N
      (fun y => ∑ a : Fin 3, normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a y).comp
          (inverseDegreeMultiplier hO hD)) x (3*T^2*M*A) beta 1 := by
    have ht := hasCoordinateWordJetBound_sum N
      (fun a : Fin 3 => fun y => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a y).comp
          (inverseDegreeMultiplier hO hD)) hTermS x (T^2*M*A) beta 1 hTerm
    simpa only [Fintype.card_fin,Nat.cast_ofNat,mul_assoc] using ht
  have hTotalS : ContDiff ℝ ∞ (fun y : R3 => ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,y) •
        (referenceWeightedZeroBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p a y).comp
          (inverseDegreeMultiplier hO hD)) := ContDiff.sum (fun a _ => hTermS a)
  have hZero : HasCoordinateWordJetBound N
      (normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p) x (Cz*r0) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul N (referenceRadius δ R p L) _ hrS hTotalS
      x (Cr*r0) (3*T^2*M*A) beta 0 1 (mul_nonneg hCr.le hr0.le) (by positivity) hb0 hRjet hTotal
    have he : (2:ℝ)^N*(Cr*r0)*(3*T^2*M*A)=Cz*r0 := by dsimp [Cz,T]; ring
    rw [he] at ht
    exact ht
  have hsmall' : r0*beta^2 ≤ eps := hsmall
  have hFirstSmall : Cf*r0 ≤ C*eps/beta^2 := by
    apply (le_div_iff₀ (pow_pos hbpos 2)).mpr
    calc
      Cf*r0*beta^2 = Cf*(r0*beta^2) := by ring
      _ ≤ Cf*eps := mul_le_mul_of_nonneg_left hsmall' hCf0
      _ ≤ C*eps := mul_le_mul_of_nonneg_right hCfC heps
  have hZeroSmall : Cz*r0*beta ≤ C*eps/beta := by
    apply (le_div_iff₀ hbpos).mpr
    calc
      Cz*r0*beta*beta = Cz*(r0*beta^2) := by ring
      _ ≤ Cz*eps := mul_le_mul_of_nonneg_left hsmall' hCz0
      _ ≤ C*eps := mul_le_mul_of_nonneg_right hCzC heps
  refine ⟨?_,?_⟩
  · intro j
    apply (hFirst j w hw).trans
    simpa only [Nat.zero_add] using mul_le_mul_of_nonneg_right hFirstSmall (pow_nonneg hb0 w.length)
  · apply (hZero w hw).trans
    calc
      (Cz*r0)*beta^(1+w.length) = (Cz*r0*beta)*beta^w.length := by rw [pow_add,pow_one]; ring
      _ ≤ (C*eps/beta)*beta^w.length := mul_le_mul_of_nonneg_right hZeroSmall (pow_nonneg hb0 _)


end OAI.AnisotropicCalderon.ActualNormalizedSecondDriftWeightedCoefficients
