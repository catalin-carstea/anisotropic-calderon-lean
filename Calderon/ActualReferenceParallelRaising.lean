import Calderon.ActualPhysicalPureAngular
import Calderon.ActualNormalizedSphereRotation
import Calderon.ActualReferenceDecomposition

set_option autoImplicit false
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceParallelRaising
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph AngularWeightedCore BoundedAngularShift HarmonicDerivativeOperator
  SmoothSphereFields SmoothAngularApplication AmbientAngularShift SmoothMovingFrameFields
  SmoothSphereRotationProjection SphereDerivativeAdjoint HarmonicCoordinateCompatibility
  MovingFrameConnection AngularPolynomial SmoothMetricFrame
  AmbientReferenceRaising AmbientReferenceCovariantCore ActualPhysicalPureAngular
  ActualNormalizedSphereRotation ActualReferenceDecomposition ActualPrincipalErrorCoefficient
  PrincipalCommutator ConformalDepth RadiusProfile SmoothAmbientAngularCasimir ReferenceDensityBounds

/- Actual native reference angular connection and parallel covector-index raising.
   Every raw composition is paid with its genuine all-degree maximal graph.
   Source-only author candidate; ROOT alone checks and integrates. No full U/E/F claim. -/

def harmonicReferenceAngularConnection
    (g : MatrixField) (L lam : ℝ) (k : ℕ) (x X : R3) :
    harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k :=
  (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3,
    referenceFrameConnectionCoefficient g L lam x X i j • harmonicSphereRotation k i j

lemma referenceFrameAngularPolynomial_harmonicHomogeneous_all
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (x X : R3)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    referenceFrameAngularPolynomial g L lam x X p ∈ harmonicHomogeneous k := by
  cases k with
  | zero =>
    rw [referenceFrameAngularPolynomial_eq_zero_of_isHomogeneous_zero g L lam x X p hp.1]
    exact (harmonicHomogeneous 0).zero_mem
  | succ k =>
    exact referenceFrameAngularPolynomial_harmonicHomogeneous g hg L lam x X (k+1) (by omega) p hp

lemma referenceFrameAngularPolynomial_sphereDerivativeAdjoint_commutator
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (x X : R3)
    (k : ℕ) (a : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    referenceFrameAngularPolynomial g L lam x X (sphereDerivativeAdjoint k a p) -
      sphereDerivativeAdjoint k a (referenceFrameAngularPolynomial g L lam x X p) =
    ∑ b : Fin 3, C (referenceFrameConnectionCoefficient g L lam x X b a) *
      sphereDerivativeAdjoint k b p := by
  have h := referenceFrameAngularPolynomial_coordinateHarmonicRaising_commutator g hg L lam x X k a p
  simp only [sphereDerivativeAdjoint,referenceFrameAngularPolynomial_C_mul]
  simp only [Fin.sum_univ_three] at h ⊢
  linear_combination C (2*(k:ℝ)+3) * h

lemma harmonicReferenceAngularConnection_apply_image
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (x X : R3)
    (p : harmonicHomogeneous k) :
    harmonicReferenceAngularConnection g L lam k x X (harmonicPolynomialSphereMap k p) =
      harmonicPolynomialSphereMap k ⟨referenceFrameAngularPolynomial g L lam x X p,
        referenceFrameAngularPolynomial_harmonicHomogeneous_all g hg L lam x X k p p.property⟩ := by
  simp only [harmonicReferenceAngularConnection,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,harmonicSphereRotation_apply_image]
  apply Subtype.ext
  change (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3,
    referenceFrameConnectionCoefficient g L lam x X i j • polynomialSphereL2 (polynomialRotation i j p) =
      polynomialSphereL2 (referenceFrameAngularPolynomial g L lam x X p)
  rw [referenceFrameAngularPolynomial_eq_half_smul g hg L lam x X p]
  simp only [polynomialRotationCombination,← smul_eq_C_mul,map_smul,map_sum]

theorem harmonicReferenceAngularConnection_raising_commutator
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (k : ℕ) (x X : R3) (a : Fin 3) (u : harmonicSphereSubspace k) :
    harmonicReferenceAngularConnection g L lam (k+1) x X (harmonicDerivativeAdjoint hF k a u) -
      harmonicDerivativeAdjoint hF k a (harmonicReferenceAngularConnection g L lam k x X u) =
    ∑ b : Fin 3, referenceFrameConnectionCoefficient g L lam x X b a •
      harmonicDerivativeAdjoint hF k b u := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  rw [harmonicDerivativeAdjoint_apply_image]
  change harmonicReferenceAngularConnection g L lam (k+1) x X
      (harmonicPolynomialSphereMap (k+1) ⟨sphereDerivativeAdjoint k a p,
        sphereDerivativeAdjoint_harmonicHomogeneous k a p p.property⟩) - _ = _
  rw [harmonicReferenceAngularConnection_apply_image g hg L lam (k+1) x X,
    harmonicReferenceAngularConnection_apply_image g hg L lam k x X,
    harmonicDerivativeAdjoint_apply_image]
  simp_rw [harmonicDerivativeAdjoint_apply_image]
  apply Subtype.ext
  change polynomialSphereL2 (referenceFrameAngularPolynomial g L lam x X (sphereDerivativeAdjoint k a p)) -
    polynomialSphereL2 (sphereDerivativeAdjoint k a (referenceFrameAngularPolynomial g L lam x X p)) =
      ∑ b : Fin 3, referenceFrameConnectionCoefficient g L lam x X b a •
        polynomialSphereL2 (sphereDerivativeAdjoint k b p)
  rw [← map_sub,referenceFrameAngularPolynomial_sphereDerivativeAdjoint_commutator g hg L lam x X k a p]
  simp only [map_sum,← smul_eq_C_mul,map_smul]

def referenceAngularConnectionGraph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (x X : R3) : Set (SphereL2 × SphereL2) :=
  {z | ∀ k : ℕ, sphereHarmonicCoordinate hO hD k z.2 =
    harmonicReferenceAngularConnection g L lam k x X (sphereHarmonicCoordinate hO hD k z.1)}

def normalizedReferenceAngularConnection
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (x X : R3) : SphereL2 →L[ℝ] SphereL2 :=
  (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3,
    referenceFrameConnectionCoefficient g L lam x X i j • normalizedRotation hO hD i j

lemma normalizedReferenceAngularConnection_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (x X : R3) (u w : SphereL2)
    (hw : (u,w) ∈ sphereBesselGraph hO hD 1) :
    (u,normalizedReferenceAngularConnection hO hD g L lam x X w) ∈
      referenceAngularConnectionGraph hO hD g L lam x X := by
  intro k
  change sphereHarmonicCoordinate hO hD k (normalizedReferenceAngularConnection hO hD g L lam x X w) = _
  simp only [normalizedReferenceAngularConnection,harmonicReferenceAngularConnection,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum]
  have hr (i j : Fin 3) : sphereHarmonicCoordinate hO hD k (normalizedRotation hO hD i j w) =
      harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k u) :=
    normalizedRotation_graph hO hD i j u w hw k
  simp_rw [hr]

def ambientReferenceAngularConnection
    (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) : SphereL2 :=
  (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3,
    referenceFrameConnectionCoefficient g L lam x X i j •
      ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) x

lemma ambientReferenceAngularConnection_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    (ambientSphereL2 G hG x,ambientReferenceAngularConnection g L lam G hG x X) ∈
      referenceAngularConnectionGraph hO hD g L lam x X := by
  intro k
  change sphereHarmonicCoordinate hO hD k (ambientReferenceAngularConnection g L lam G hG x X) = _
  simp only [ambientReferenceAngularConnection,harmonicReferenceAngularConnection,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_smul,map_sum]
  simp_rw [sphereHarmonicCoordinate_ambientAngularRotation hO hD k _ _ G hG x]

def ambientReferenceAngularConnectionBessel
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) : SphereL2 :=
  (1/2 : ℝ) • ∑ i : Fin 3, ∑ j : Fin 3,
    referenceFrameConnectionCoefficient g L lam x X i j •
      ambientBesselField hO hD 1 (by norm_num) (ambientAngularRotation i j G)
        (contDiff_ambientAngularRotation i j G hG) x

lemma ambientReferenceAngularConnectionBessel_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    (ambientReferenceAngularConnection g L lam G hG x X,
      ambientReferenceAngularConnectionBessel hO hD g L lam G hG x X) ∈
        sphereBesselGraph hO hD 1 := by
  intro k
  change sphereHarmonicCoordinate hO hD k
    (ambientReferenceAngularConnectionBessel hO hD g L lam G hG x X) =
      besselWeight 1 k • sphereHarmonicCoordinate hO hD k
        (ambientReferenceAngularConnection g L lam G hG x X)
  simp only [ambientReferenceAngularConnectionBessel,ambientReferenceAngularConnection,map_smul,map_sum]
  simp_rw [ambientBesselField_graph hO hD 1 (by norm_num) (ambientAngularRotation _ _ G)
    (contDiff_ambientAngularRotation _ _ G hG) x k]
  rw [smul_comm (besselWeight 1 k) (1/2 : ℝ)]
  simp only [Finset.smul_sum]
  simp_rw [smul_comm (besselWeight 1 k)]

def ambientRaisingReferenceAngularConnection
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) : SphereL2 :=
  normalizedRaising hF hO hD a (ambientReferenceAngularConnectionBessel hO hD g L lam G hG x X)

lemma ambientRaisingReferenceAngularConnection_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    (ambientReferenceAngularConnection g L lam G hG x X,
      ambientRaisingReferenceAngularConnection hF hO hD g L lam a G hG x X) ∈
        sphereRaisingGraph hF hO hD a := by
  exact normalizedRaising_graph hF hO hD a _ _
    (ambientReferenceAngularConnectionBessel_graph hO hD g L lam G hG x X)

def ambientReferenceAngularConnectionRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) : SphereL2 :=
  normalizedReferenceAngularConnection hO hD g L lam x X
    (ambientRaisingBesselField hF hO hD a G hG x)

lemma ambientReferenceAngularConnectionRaising_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    (ambientRaisingField hF hO hD a G hG x,
      ambientReferenceAngularConnectionRaising hF hO hD g L lam a G hG x X) ∈
        referenceAngularConnectionGraph hO hD g L lam x X := by
  exact normalizedReferenceAngularConnection_graph hO hD g L lam x X _ _
    (ambientRaisingBesselField_graph hF hO hD a G hG x)

theorem ambientReferenceAngularConnection_raising_commutator
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    ambientReferenceAngularConnectionRaising hF hO hD g L lam a G hG x X -
      ambientRaisingReferenceAngularConnection hF hO hD g L lam a G hG x X =
    ∑ b : Fin 3, referenceFrameConnectionCoefficient g L lam x X b a •
      ambientRaisingField hF hO hD b G hG x := by
  have hOR := ambientReferenceAngularConnectionRaising_graph hF hO hD g L lam a G hG x X
  have hRO := ambientRaisingReferenceAngularConnection_graph hF hO hD g L lam a G hG x X
  have hR := ambientRaisingField_graph hF hO hD a G hG x
  have hOmega := ambientReferenceAngularConnection_graph hO hD g L lam G hG x X
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext m
  change sphereHarmonicCoordinate hO hD m
      (ambientReferenceAngularConnectionRaising hF hO hD g L lam a G hG x X -
        ambientRaisingReferenceAngularConnection hF hO hD g L lam a G hG x X) =
    sphereHarmonicCoordinate hO hD m
      (∑ b : Fin 3, referenceFrameConnectionCoefficient g L lam x X b a •
        ambientRaisingField hF hO hD b G hG x)
  rw [map_sub,map_sum]
  simp only [map_smul]
  cases m with
  | zero =>
    rw [hOR 0,hRO.1,hR.1,map_zero,sub_zero]
    simp_rw [(ambientRaisingField_graph hF hO hD _ G hG x).1]
    simp only [smul_zero,Finset.sum_const_zero]
  | succ m =>
    rw [hOR (m+1),hRO.2 m,hR.2 m,hOmega m]
    simp_rw [(ambientRaisingField_graph hF hO hD _ G hG x).2 m]
    exact harmonicReferenceAngularConnection_raising_commutator hF g hg L lam m x X a
      (sphereHarmonicCoordinate hO hD m (ambientSphereL2 G hG x))

def ambientRaisingCovectorDerivative
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) : SphereL2 :=
  directionalFDeriv X (ambientRaisingField hF hO hD a G hG) x +
    ambientReferenceAngularConnectionRaising hF hO hD g L lam a G hG x X -
      ∑ b : Fin 3, referenceFrameConnectionCoefficient g L lam x X b a •
        ambientRaisingField hF hO hD b G hG x

theorem ambientRaisingCovectorDerivative_eq_normalizedRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    ambientRaisingCovectorDerivative hF hO hD g L lam a G hG x X =
      normalizedRaising hF hO hD a
        (directionalFDeriv X (ambientBesselField hO hD 1 (by norm_num) G hG) x +
          ambientReferenceAngularConnectionBessel hO hD g L lam G hG x X) := by
  have hc := ambientReferenceAngularConnection_raising_commutator hF hO hD g hg L lam a G hG x X
  have hd : directionalFDeriv X (ambientRaisingField hF hO hD a G hG) x =
      normalizedRaising hF hO hD a
        (directionalFDeriv X (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
    unfold AmbientAngularShift.ambientRaisingField
    exact directionalFDeriv_fixed_map
      (normalizedRaising hF hO hD a) (ambientBesselField hO hD 1 (by norm_num) G hG)
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG) X x
  unfold ambientRaisingCovectorDerivative
  rw [← hc,hd]
  unfold ambientRaisingReferenceAngularConnection
  rw [map_add]
  abel

lemma ambientReferenceHorizontalInput_besselGraph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    (directionalFDeriv X (ambientSphereL2 G hG) x + ambientReferenceAngularConnection g L lam G hG x X,
      directionalFDeriv X (ambientBesselField hO hD 1 (by norm_num) G hG) x +
        ambientReferenceAngularConnectionBessel hO hD g L lam G hG x X) ∈
      sphereBesselGraph hO hD 1 := by
  intro k
  change sphereHarmonicCoordinate hO hD k
      (directionalFDeriv X (ambientBesselField hO hD 1 (by norm_num) G hG) x +
        ambientReferenceAngularConnectionBessel hO hD g L lam G hG x X) =
    besselWeight 1 k • sphereHarmonicCoordinate hO hD k
      (directionalFDeriv X (ambientSphereL2 G hG) x +
        ambientReferenceAngularConnection g L lam G hG x X)
  rw [map_add,map_add,smul_add]
  have hb : sphereHarmonicCoordinate hO hD k
      (directionalFDeriv X (ambientBesselField hO hD 1 (by norm_num) G hG) x) =
    besselWeight 1 k • sphereHarmonicCoordinate hO hD k
      (directionalFDeriv X (ambientSphereL2 G hG) x) := by
    exact SectionFiveErrorForms.directionalDeriv_besselGraph hO hD 1 X
      (ambientSphereL2 G hG) (ambientBesselField hO hD 1 (by norm_num) G hG)
      (contDiff_ambientSphereL2 G hG) (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)
      (ambientBesselField_graph hO hD 1 (by norm_num) G hG) x k
  rw [hb,ambientReferenceAngularConnectionBessel_graph hO hD g L lam G hG x X k]

theorem ambientRaisingCovectorDerivative_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (a : Fin 3) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    (directionalFDeriv X (ambientSphereL2 G hG) x + ambientReferenceAngularConnection g L lam G hG x X,
      ambientRaisingCovectorDerivative hF hO hD g L lam a G hG x X) ∈
        sphereRaisingGraph hF hO hD a := by
  rw [ambientRaisingCovectorDerivative_eq_normalizedRaising hF hO hD g hg L lam a G hG x X]
  exact normalizedRaising_graph hF hO hD a _ _
    (ambientReferenceHorizontalInput_besselGraph hO hD g L lam G hG x X)

lemma referenceHorizontalField_eq_base_add_angularConnection
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceHorizontalField g hg L lam i G hG x =
      directionalFDeriv (referenceMetricGramFrame g L (lam,x) i) (ambientSphereL2 G hG) x +
        ambientReferenceAngularConnection g L lam G hG x (referenceMetricGramFrame g L (lam,x) i) := by
  rw [referenceHorizontalField_expansion g hg L lam i G hG x]
  have he : directionalFDeriv (referenceMetricGramFrame g L (lam,x) i) (ambientSphereL2 G hG) x =
      ∑ k : Fin 3, referenceMetricGramFrame g L (lam,x) i k •
        directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x := by
    simpa only [directionalFDeriv] using fderiv_apply_eq_coordinate_sum
      (ambientSphereL2 G hG) x (referenceMetricGramFrame g L (lam,x) i)
  rw [he]
  rfl

lemma referenceHorizontalBesselField_eq_base_add_angularConnection
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceHorizontalBesselField hO hD g hg L lam 1 (by norm_num) i G hG x =
      directionalFDeriv (referenceMetricGramFrame g L (lam,x) i)
        (ambientBesselField hO hD 1 (by norm_num) G hG) x +
        ambientReferenceAngularConnectionBessel hO hD g L lam G hG x (referenceMetricGramFrame g L (lam,x) i) := by
  rw [referenceHorizontalBesselField_expansion hO hD g hg L lam i G hG x]
  have he : directionalFDeriv (referenceMetricGramFrame g L (lam,x) i)
      (ambientBesselField hO hD 1 (by norm_num) G hG) x =
      ∑ k : Fin 3, referenceMetricGramFrame g L (lam,x) i k •
        directionalFDeriv (coordinateDirection k) (ambientBesselField hO hD 1 (by norm_num) G hG) x := by
    simpa only [directionalFDeriv] using fderiv_apply_eq_coordinate_sum
      (ambientBesselField hO hD 1 (by norm_num) G hG) x (referenceMetricGramFrame g L (lam,x) i)
  rw [he]
  rfl

theorem referenceHorizontalField_raisingCovectorDerivative_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (i a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (referenceHorizontalField g hg L lam i G hG x,
      ambientRaisingCovectorDerivative hF hO hD g L lam a G hG x (referenceMetricGramFrame g L (lam,x) i)) ∈
        sphereRaisingGraph hF hO hD a := by
  rw [referenceHorizontalField_eq_base_add_angularConnection g hg L lam i G hG x]
  exact ambientRaisingCovectorDerivative_graph hF hO hD g hg L lam a G hG x
    (referenceMetricGramFrame g L (lam,x) i)

end OAI.AnisotropicCalderon.ActualReferenceParallelRaising
