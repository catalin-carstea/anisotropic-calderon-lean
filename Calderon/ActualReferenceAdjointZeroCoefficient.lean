import Calderon.ActualUnboundedFirstPrincipalCoordinates
import Calderon.AmbientReferenceRaising
import Calderon.ReferenceRaisingAdjunctionEndpoint

/-!
Source-only candidate: derived zero part of the actual reference raising adjoint.
Frozen target: OAI.AnisotropicCalderon.main, d1205fb493b3fbe04e55f72b76c6ff0761fb5a03.
Expansion frozen before authoring in EXPANSION.md and expansion-freeze.json.
No compilation, kernel, foundation, semantic-review or acceptance claim.
This coefficient is not identified with the full physical U†−U zero defect.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceAdjointZeroCoefficient
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph AngularShiftGraph BoundedAngularShift
  PrincipalCommutator ScalarBaseAdjoint NaturalAngularAdjoint
  SmoothSphereFields SmoothMovingFrameFields SmoothAmbientAngularCasimir
  SmoothAngularApplication AmbientAngularShift AmbientReferenceCovariantCore
  AmbientReferenceRaising MovingFrameConnection SmoothMetricFrame
  ReferenceDensityBounds ActualBalancedFirstPrincipalError
  HarmonicDerivativeOperator CovariantHarmonicEnergy ReferenceRaisingAdjunction
  ReferenceRaisingAdjunctionEndpoint SmoothSphereRotationProjection

/-- Connection products and the shifted radial-degree products are separate
fixed angular arrows. Their base coefficients alone depend on x. -/
abbrev ReferenceZeroIndex := (Fin 3 × Fin 3 × Fin 3) ⊕ Fin 3

def referenceZeroCoefficient (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (s : ReferenceZeroIndex) (x : R3) : ℝ :=
  match s with
  | .inl t => -(1/2 : ℝ) * referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) t.1) t.2.1 t.2.2
  | .inr b => referenceFrameDerivative g L lam b f x

/-- These continuous maps are between two finite harmonic fibers. No raw
angular operator is declared continuous on all SphereL2. -/
def referenceZeroAngularCoefficient (hF : SphereFischerInner) (m : ℕ)
    (s : ReferenceZeroIndex) :
    harmonicSphereSubspace (m+1) →L[ℝ] harmonicSphereSubspace m :=
  match s with
  | .inl t => (harmonicDerivative hF m t.1).comp
      (harmonicSphereRotation (m+1) t.2.1 t.2.2)
  | .inr b => (m : ℝ) • harmonicDerivative hF m b

def referenceAdjointZeroHarmonicCoefficient (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ) (m : ℕ) (x : R3) :
    harmonicSphereSubspace (m+1) →L[ℝ] harmonicSphereSubspace m :=
  ∑ s : ReferenceZeroIndex, referenceZeroCoefficient g L lam f s x •
    referenceZeroAngularCoefficient hF m s

/-- Literal signs, half factor, ordered rotation/lowering product, and the
output-degree weight m dictated by the physical formal adjoint. -/
lemma referenceAdjointZeroHarmonicCoefficient_apply (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ) (m : ℕ) (x : R3)
    (u : harmonicSphereSubspace (m+1)) :
    referenceAdjointZeroHarmonicCoefficient hF g L lam f m x u =
      -(1/2 : ℝ) • (∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        referenceFrameConnectionCoefficient g L lam x
          (referenceMetricGramFrame g L (lam,x) b) c d •
          harmonicDerivative hF m b (harmonicSphereRotation (m+1) c d u)) +
      ∑ b : Fin 3, referenceFrameDerivative g L lam b f x •
        ((m : ℝ) • harmonicDerivative hF m b u) := by
  simp only [referenceAdjointZeroHarmonicCoefficient, Fintype.sum_sum_type,
    Fintype.sum_prod_type, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    referenceZeroCoefficient, referenceZeroAngularCoefficient,
    ContinuousLinearMap.comp_apply, Finset.smul_sum, smul_smul]

/-- Expanding the actual metric-compatible connection identifies the zero
coefficient. No full perturbation-adjoint identity is presumed. -/
lemma referenceAdjoint_expression_coefficient_form (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ) (m : ℕ)
    (U : R3 → harmonicSphereSubspace (m+1)) (x : R3) :
    (∑ b : Fin 3, harmonicDerivative hF m b
      (-referenceHarmonicCovariantDerivative g L lam (m+1) U x
          (referenceMetricGramFrame g L (lam,x) b) +
        ((m : ℝ) * referenceFrameDerivative g L lam b f x) • U x)) =
      -(∑ b : Fin 3, harmonicDerivative hF m b
        (fderiv ℝ U x (referenceMetricGramFrame g L (lam,x) b))) +
      referenceAdjointZeroHarmonicCoefficient hF g L lam f m x (U x) := by
  rw [referenceAdjointZeroHarmonicCoefficient_apply]
  simp only [referenceHarmonicCovariantDerivative, map_add, map_neg, map_smul,
    map_sum, smul_add, smul_smul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.smul_sum, neg_add, neg_smul, smul_neg]
  simp only [neg_mul, neg_smul, Finset.sum_neg_distrib, mul_comm, add_assoc]

/-- Source correspondence for every positive output degree. The coefficient
comes from the native adjoint carrying the lower-degree weight. -/
theorem referenceHarmonicRaisingAdjoint_coefficient_form (hF : SphereFischerInner)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ) (n : ℕ)
    (U : R3 → harmonicSphereSubspace ((n+1)+1)) (x : R3) :
    referenceHarmonicRaisingAdjoint hF g L lam n U f x =
      -(∑ b : Fin 3, harmonicDerivative hF (n+1) b
        (fderiv ℝ U x (referenceMetricGramFrame g L (lam,x) b))) +
      referenceAdjointZeroHarmonicCoefficient hF g L lam f (n+1) x (U x) := by
  unfold referenceHarmonicRaisingAdjoint referenceAdjointHarmonicInput
  convert referenceAdjoint_expression_coefficient_form hF g L lam f (n+1) U x using 1
  apply Finset.sum_congr rfl
  intro b _
  simp only [referenceFrameDerivative, map_add, map_smul, map_neg] <;> module

/-- The native H1→H0 formal adjoint gives the same formula with m=0. The
weight part vanishes; its connection part is retained. -/
theorem referenceHarmonicDegreeOneRaisingAdjoint_coefficient_form
    (hF : SphereFischerInner) (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (U : R3 → harmonicSphereSubspace 1) (x : R3) :
    referenceHarmonicDegreeOneRaisingAdjoint hF g L lam U x =
      -(∑ b : Fin 3, harmonicDerivative hF 0 b
        (fderiv ℝ U x (referenceMetricGramFrame g L (lam,x) b))) +
      referenceAdjointZeroHarmonicCoefficient hF g L lam f 0 x (U x) := by
  simpa only [referenceHarmonicDegreeOneRaisingAdjoint, Nat.zero_add,
    Nat.cast_zero, zero_mul, zero_smul, add_zero] using
    referenceAdjoint_expression_coefficient_form hF g L lam f 0 U x

lemma contDiff_referenceZeroCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (s : ReferenceZeroIndex) :
    ContDiff ℝ ∞ (referenceZeroCoefficient g L lam f s) := by
  cases s with
  | inl t =>
    exact contDiff_const.mul
      (contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
        (contDiff_referenceMetricGramFrame_slice g hg L lam t.1) t.2.1 t.2.2)
  | inr b => exact contDiff_referenceFrameDerivative g hg L lam b f hf

def degreeMinusOneField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => ambientBesselField hO hD 1 (by norm_num) G hG x -
    (2 : ℝ) • ambientSphereL2 G hG x

def degreeMinusOneBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    R3 → SphereL2 :=
  fun x => ambientBesselField hO hD 2 (by norm_num) G hG x -
    (2 : ℝ) • ambientBesselField hO hD 1 (by norm_num) G hG x

/-- Exact (1+B)(B−1) output of the actual field, with no supplied domain or
summability witness. -/
lemma degreeMinusOneBesselField_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (degreeMinusOneField hO hD G hG x,
      degreeMinusOneBesselField hO hD G hG x) ∈ sphereBesselGraph hO hD 1 := by
  intro m
  simp only [degreeMinusOneField, degreeMinusOneBesselField, map_sub, map_smul]
  rw [ambientBesselField_graph hO hD 2 (by norm_num) G hG x m,
    ambientBesselField_graph hO hD 1 (by norm_num) G hG x m]
  simp only [besselWeight, Real.rpow_one, Real.rpow_two]
  module

def degreeMinusOneDerivativeField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedDerivative hF hO hD b (degreeMinusOneBesselField hO hD G hG x)

lemma degreeMinusOneDerivativeField_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (degreeMinusOneField hO hD G hG x,
      degreeMinusOneDerivativeField hF hO hD b G hG x) ∈
      sphereDerivativeGraph hF hO hD b :=
  normalizedDerivative_graph hF hO hD b _ _
    (degreeMinusOneBesselField_graph hO hD G hG x)

lemma degreeMinusOneDerivativeField_coordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD m
      (degreeMinusOneDerivativeField hF hO hD b G hG x) =
      (m : ℝ) • harmonicDerivative hF m b
        (sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG x)) := by
  rw [degreeMinusOneDerivativeField_graph hF hO hD b G hG x m]
  simp only [degreeMinusOneField, map_sub, map_smul]
  rw [ambientBesselField_graph hO hD 1 (by norm_num) G hG x (m+1)]
  simp only [besselWeight, Real.rpow_one, Nat.cast_add, Nat.cast_one,
    map_sub, map_smul]
  module

/-- Actual fixed angular-product outputs. The rotation is evaluated before
the lowering derivative, exactly as in the physical connection coefficient. -/
def referenceZeroOutput (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ReferenceZeroIndex)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  match s with
  | .inl t => ambientDerivativeField hF hO hD t.1
      (ambientAngularRotation t.2.1 t.2.2 G)
      (contDiff_ambientAngularRotation t.2.1 t.2.2 G hG)
  | .inr b => degreeMinusOneDerivativeField hF hO hD b G hG

lemma referenceZeroOutput_coordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ReferenceZeroIndex) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD m (referenceZeroOutput hF hO hD s G hG x) =
      referenceZeroAngularCoefficient hF m s
        (sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG x)) := by
  cases s with
  | inl t =>
    change sphereHarmonicCoordinate hO hD m
      (ambientDerivativeField hF hO hD t.1 _ _ x) = _
    rw [ambientDerivativeField_graph hF hO hD t.1 _ _ x m,
      sphereHarmonicCoordinate_ambientAngularRotation hO hD (m+1) t.2.1 t.2.2 G hG x]
    rfl
  | inr b =>
    simpa only [referenceZeroOutput, referenceZeroAngularCoefficient,
      ContinuousLinearMap.smul_apply] using
      degreeMinusOneDerivativeField_coordinate hF hO hD b G hG m x

lemma contDiff_referenceZeroOutput (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ReferenceZeroIndex) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceZeroOutput hF hO hD s G hG) := by
  cases s with
  | inl t =>
    exact contDiff_ambientDerivativeField hF hO hD t.1 _
      (contDiff_ambientAngularRotation t.2.1 t.2.2 G hG)
  | inr b =>
    exact (normalizedDerivative hF hO hD b).contDiff.comp
      ((contDiff_ambientBesselField hO hD 2 (by norm_num) G hG).sub
        ((contDiff_ambientBesselField hO hD 1 (by norm_num) G hG).const_smul 2))

lemma referenceZeroOutput_eq_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ReferenceZeroIndex) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (x : R3) (hx : x ∉ K) : referenceZeroOutput hF hO hD s G hG x = 0 := by
  cases s with
  | inl t =>
    exact ambientDerivativeField_eq_zero hF hO hD t.1 _
      (contDiff_ambientAngularRotation t.2.1 t.2.2 G hG) K
      (ambientAngularRotation_sphere_zero t.2.1 t.2.2 G hG K hz) x hx
  | inr b =>
    simp only [referenceZeroOutput, degreeMinusOneDerivativeField,
      degreeMinusOneBesselField,
      ambientBesselField_eq_zero hO hD 2 (by norm_num) G hG K hz x hx,
      ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
      smul_zero, sub_self, map_zero]

lemma hasCompactSupport_referenceZeroOutput (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ReferenceZeroIndex) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceZeroOutput hF hO hD s G hG) :=
  HasCompactSupport.intro hK
    (fun x hx => referenceZeroOutput_eq_zero hF hO hD s G hG K hz x hx)

def referenceAdjointZeroField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ s : ReferenceZeroIndex, referenceZeroCoefficient g L lam f s x •
    referenceZeroOutput hF hO hD s G hG x

lemma contDiff_referenceAdjointZeroField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (referenceAdjointZeroField hF hO hD g L lam f G hG) :=
  ContDiff.sum (fun s _ => (contDiff_referenceZeroCoefficient g hg L lam f hf s).smul
    (contDiff_referenceZeroOutput hF hO hD s G hG))

lemma referenceAdjointZeroField_coordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : R3) :
    sphereHarmonicCoordinate hO hD m
      (referenceAdjointZeroField hF hO hD g L lam f G hG x) =
      referenceAdjointZeroHarmonicCoefficient hF g L lam f m x
        (sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG x)) := by
  simp only [referenceAdjointZeroField, map_sum, map_smul,
    referenceZeroOutput_coordinate, referenceAdjointZeroHarmonicCoefficient,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

/-- Maximal all-degree lowering graph of the derived zero coefficient at x.
Existence is not asserted for arbitrary SphereL2 input. -/
def referenceAdjointZeroGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ) (x : R3) :
    Submodule ℝ (SphereL2 × SphereL2) where
  carrier := {z | ∀ m, sphereHarmonicCoordinate hO hD m z.2 =
    referenceAdjointZeroHarmonicCoefficient hF g L lam f m x
      (sphereHarmonicCoordinate hO hD (m+1) z.1)}
  zero_mem' := by intro m; simp
  add_mem' := by
    intro z z' hz hz' m
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    rw [hz m, hz' m]
  smul_mem' := by
    intro c z hz m
    change sphereHarmonicCoordinate hO hD m (c • z.2) =
      referenceAdjointZeroHarmonicCoefficient hF g L lam f m x
        (sphereHarmonicCoordinate hO hD (m+1) (c • z.1))
    rw [map_smul, map_smul, map_smul, hz m]

lemma referenceAdjointZeroField_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x, referenceAdjointZeroField hF hO hD g L lam f G hG x) ∈
      referenceAdjointZeroGraph hF hO hD g L lam f x :=
  fun m => referenceAdjointZeroField_coordinate hF hO hD g L lam f G hG m x

lemma referenceAdjointZeroGraph_output_unique (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ) (x : R3) (u z z' : SphereL2)
    (hz : (u,z) ∈ referenceAdjointZeroGraph hF hO hD g L lam f x)
    (hz' : (u,z') ∈ referenceAdjointZeroGraph hF hO hD g L lam f x) : z = z' := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext m
  exact (hz m).trans (hz' m).symm

lemma hasCompactSupport_referenceAdjointZeroField (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (f : R3 → ℝ)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceAdjointZeroField hF hO hD g L lam f G hG) := by
  apply HasCompactSupport.intro hK
  intro x hx
  simp only [referenceAdjointZeroField,
    referenceZeroOutput_eq_zero hF hO hD _ G hG K hz x hx,
    smul_zero, Finset.sum_const_zero]

end OAI.AnisotropicCalderon.ActualReferenceAdjointZeroCoefficient
