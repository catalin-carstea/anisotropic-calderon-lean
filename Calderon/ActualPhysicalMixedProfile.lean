import Calderon.AmbientReferenceRaising
import Calderon.ActualHorizontalGeometry
import Calderon.ActualUnboundedFirstPrincipalFormBound

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualPhysicalMixedProfile
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift HarmonicDerivativeOperator
  SmoothSphereFields SmoothAngularApplication AmbientAngularShift AmbientReferenceRaising
  ActualHorizontalNormBridge ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile

/- Actual zero-base profile part of2h A*D+, with f=log(referenceRadius).
   Its native independently ordered angular adjoint is BA, retaining all modes.
   No whole physical U, E/F trace or U/J allocation is asserted here. -/

def ambientMixedDegreeBesselField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => ambientBesselField hO hD 2 (by norm_num) G hG x -
    ambientBesselField hO hD 1 (by norm_num) G hG x

lemma ambientMixedDegreeBesselField_graph (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientDegreeField hO hD G hG x,ambientMixedDegreeBesselField hO hD G hG x) ∈
      sphereBesselGraph hO hD 1 := by
  intro k
  simp only [ambientMixedDegreeBesselField,map_sub,
    ambientBesselField_graph hO hD 2 (by norm_num) G hG x k,
    ambientBesselField_graph hO hD 1 (by norm_num) G hG x k,
    ambientDegreeField_coordinate,besselWeight,Real.rpow_two,Real.rpow_one]
  module

def ambientMixedRaisingDegreeField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedRaising hF hO hD i (ambientMixedDegreeBesselField hO hD G hG x)

lemma ambientMixedRaisingDegreeField_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientDegreeField hO hD G hG x,ambientMixedRaisingDegreeField hF hO hD i G hG x) ∈
      sphereRaisingGraph hF hO hD i := 
  normalizedRaising_graph hF hO hD i _ _
    (ambientMixedDegreeBesselField_graph hO hD G hG x)

lemma inverseDegreeWeight_second_double_difference (m : ℕ) :
    inverseDegreeWeight (m+1) * (besselWeight 2 (m+1)-2*besselWeight 1 (m+1)) = (m : ℝ) := by
  simp only [inverseDegreeWeight,besselWeight,Real.rpow_two,Real.rpow_one]
  push_cast
  field_simp
  ring

def ambientMixedDegreeDerivativeField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedDerivative hF hO hD i
    (ambientBesselField hO hD 2 (by norm_num) G hG x -
      (2 : ℝ) • ambientBesselField hO hD 1 (by norm_num) G hG x)

lemma ambientMixedDegreeDerivativeField_coordinate
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) (m : ℕ) :
    sphereHarmonicCoordinate hO hD m (ambientMixedDegreeDerivativeField hF hO hD i G hG x) =
      (m : ℝ) • sphereHarmonicCoordinate hO hD m (ambientDerivativeField hF hO hD i G hG x) := by
  have hinput : sphereHarmonicCoordinate hO hD (m+1)
      (inverseDegreeMultiplier hO hD
        (ambientBesselField hO hD 2 (by norm_num) G hG x -
          (2 : ℝ) • ambientBesselField hO hD 1 (by norm_num) G hG x)) =
      (m : ℝ) • sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG x) := by
    rw [inverseDegreeMultiplier_coordinate]
    simp only [map_sub,map_smul,
      ambientBesselField_graph hO hD 2 (by norm_num) G hG x (m+1),
      ambientBesselField_graph hO hD 1 (by norm_num) G hG x (m+1),smul_smul]
    have hsub := (sub_smul (besselWeight 2 (m+1)) (2*besselWeight 1 (m+1))
      (sphereHarmonicCoordinate hO hD (m+1) (ambientSphereL2 G hG x))).symm
    rw [hsub,smul_smul,inverseDegreeWeight_second_double_difference]
  change sphereHarmonicCoordinate hO hD m
    (normalizedDerivativeOutput hF hO hD i
      (ambientBesselField hO hD 2 (by norm_num) G hG x -
        (2 : ℝ) • ambientBesselField hO hD 1 (by norm_num) G hG x)) = _
  rw [normalizedDerivativeOutput_graph hF hO hD i _ m,hinput,map_smul,
    ambientDerivativeField_graph hF hO hD i G hG x m]

lemma ambientMixedDegreeDerivativeField_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientDerivativeField hF hO hD i G hG x,ambientMixedDegreeDerivativeField hF hO hD i G hG x) ∈
      spectralGraph hO hD (fun k => (k : ℝ)) := 
  ambientMixedDegreeDerivativeField_coordinate hF hO hD i G hG x

theorem ambientMixedRaisingDegreeField_inner_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪ambientMixedRaisingDegreeField hF hO hD i G hG x,ambientSphereL2 H hH x⟫_ℝ =
      ⟪ambientSphereL2 G hG x,ambientMixedDegreeDerivativeField hF hO hD i H hH x⟫_ℝ := by
  have hAdj := sphereDerivativeGraph_inner_adjoint hF hO hD i
    (ambientSphereL2 H hH x) (ambientDerivativeField hF hO hD i H hH x)
    (ambientDegreeField hO hD G hG x) (ambientMixedRaisingDegreeField hF hO hD i G hG x)
    (ambientDerivativeField_graph hF hO hD i H hH x)
    (ambientMixedRaisingDegreeField_graph hF hO hD i G hG x)
  have hDegree := spectralGraph_inner_symm hO hD (fun k => (k : ℝ))
    (ambientSphereL2 G hG x) (ambientDegreeField hO hD G hG x)
    (ambientDerivativeField hF hO hD i H hH x)
    (ambientMixedDegreeDerivativeField hF hO hD i H hH x)
    (fun k => ambientDegreeField_coordinate hO hD G hG k x)
    (ambientMixedDegreeDerivativeField_graph hF hO hD i H hH x)
  calc
    _ = ⟪ambientDegreeField hO hD G hG x,ambientDerivativeField hF hO hD i H hH x⟫_ℝ := by
      simpa only [real_inner_comm] using hAdj.symm
    _ = _ := hDegree

lemma contDiff_ambientMixedProfileAngularFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientMixedRaisingDegreeField hF hO hD i G hG) ∧
    ContDiff ℝ ∞ (ambientMixedDegreeDerivativeField hF hO hD i G hG) := by
  exact ⟨(normalizedRaising hF hO hD i).contDiff.comp
    ((contDiff_ambientBesselField hO hD 2 (by norm_num) G hG).sub
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)),
    (normalizedDerivative hF hO hD i).contDiff.comp
      ((contDiff_ambientBesselField hO hD 2 (by norm_num) G hG).sub
        ((contDiff_ambientBesselField hO hD 1 (by norm_num) G hG).const_smul 2))⟩

lemma ambientMixedProfileAngularFields_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    ambientMixedRaisingDegreeField hF hO hD i G hG x = 0 ∧
    ambientMixedDegreeDerivativeField hF hO hD i G hG x = 0 := by
  constructor
  · simp only [ambientMixedRaisingDegreeField,ambientMixedDegreeBesselField,
      ambientBesselField_eq_zero hO hD 2 (by norm_num) G hG K hz x hx,
      ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,sub_self,map_zero]
  · simp only [ambientMixedDegreeDerivativeField,
      ambientBesselField_eq_zero hO hD 2 (by norm_num) G hG K hz x hx,
      ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
      smul_zero,sub_zero,map_zero]

def physicalMixedProfileCoefficient (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (a : Fin 3) (x : R3) : ℝ :=
  2 * ∑ i : Fin 3, ∑ j : Fin 3, h x i j * referenceCoFrameEntry g L i a (lam,x) *
    directionalFDeriv (coordinateDirection j) (fun y => Real.log (referenceRadius δ R p L y)) x

lemma contDiff_physicalMixedProfileCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (a : Fin 3) :
    ContDiff ℝ ∞ (physicalMixedProfileCoefficient g L lam δ R p h a) := by
  unfold physicalMixedProfileCoefficient
  exact contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    ((hh i j).mul ((contDiff_referenceCoFrameEntry g hg L i a).comp
      (contDiff_const.prodMk contDiff_id))).mul
      (contDiff_directionalFDeriv (coordinateDirection j) _
        (contDiff_log_referenceRadius_profile δ R L p hδ hR)))

lemma physicalMixedProfileCoefficient_bound (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R) (x : R3) (eps M F : ℝ)
    (heps : 0 ≤ eps) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hh : ∀ i j, |h x i j| ≤ eps*referenceRadius δ R p L x)
    (hframe : ∀ i a, |referenceCoFrameEntry g L i a (lam,x)| ≤ M)
    (hf : ∀ j, |directionalFDeriv (coordinateDirection j)
      (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ F) (a : Fin 3) :
    |physicalMixedProfileCoefficient g L lam δ R p h a x| ≤ 18*M*F*eps*referenceRadius δ R p L x := by
  have hr := referenceRadius_pos δ R p L x hδ hR
  have ht (i j : Fin 3) : |h x i j*referenceCoFrameEntry g L i a (lam,x)*
      directionalFDeriv (coordinateDirection j) (fun y => Real.log (referenceRadius δ R p L y)) x| ≤
      eps*referenceRadius δ R p L x*M*F := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul
      (mul_le_mul (hh i j) (hframe i a) (abs_nonneg _) (mul_nonneg heps hr.le))
      (hf j) (abs_nonneg _) (mul_nonneg (mul_nonneg heps hr.le) hM)
  rw [physicalMixedProfileCoefficient,abs_mul]
  rw [show |(2 : ℝ)| = 2 by norm_num]
  calc
    _ ≤ 2*∑ i : Fin 3, |∑ j : Fin 3, h x i j*referenceCoFrameEntry g L i a (lam,x)*
        directionalFDeriv (coordinateDirection j) (fun y => Real.log (referenceRadius δ R p L y)) x| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2*∑ i : Fin 3, ∑ j : Fin 3, |h x i j*referenceCoFrameEntry g L i a (lam,x)*
        directionalFDeriv (coordinateDirection j) (fun y => Real.log (referenceRadius δ R p L y)) x| :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)) (by norm_num)
    _ ≤ 2*∑ i : Fin 3, ∑ j : Fin 3, eps*referenceRadius δ R p L x*M*F :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))) (by norm_num)
    _ = 18*M*F*eps*referenceRadius δ R p L x := by simp only [Fin.sum_univ_three]; ring

def physicalMixedProfileRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, physicalMixedProfileCoefficient g L lam δ R p h a x •
    ambientMixedRaisingDegreeField hF hO hD a G hG x

def physicalMixedProfileAdjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, physicalMixedProfileCoefficient g L lam δ R p h a x •
    ambientMixedDegreeDerivativeField hF hO hD a G hG x

def physicalMixedProfileDefect
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG x -
    physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x

theorem physicalMixedProfile_inner_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ =
      ⟪ambientSphereL2 G hG x,physicalMixedProfileAdjoint hF hO hD g L lam δ R p h H hH x⟫_ℝ := by
  simp only [physicalMixedProfileRaising,physicalMixedProfileAdjoint,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right,
    ambientMixedRaisingDegreeField_inner_adjoint hF hO hD _ G H hG hH x]

lemma contDiff_physicalMixedProfileFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG) ∧ ContDiff ℝ ∞ (physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG) ∧
    ContDiff ℝ ∞ (physicalMixedProfileDefect hF hO hD g L lam δ R p h G hG) := by
  have hU : ContDiff ℝ ∞ (physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG) :=
    ContDiff.sum fun a _ =>
      (contDiff_physicalMixedProfileCoefficient g hg L lam δ R p h hδ hR hh a).smul
        (contDiff_ambientMixedProfileAngularFields hF hO hD a G hG).1
  have hAdj : ContDiff ℝ ∞ (physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG) :=
    ContDiff.sum fun a _ =>
      (contDiff_physicalMixedProfileCoefficient g hg L lam δ R p h hδ hR hh a).smul
        (contDiff_ambientMixedProfileAngularFields hF hO hD a G hG).2
  exact ⟨hU,hAdj,hAdj.sub hU⟩

lemma physicalMixedProfileFields_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x = 0 ∧ physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG x = 0 ∧ physicalMixedProfileDefect hF hO hD g L lam δ R p h G hG x = 0 := by
  have hU : physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x = 0 := by
    simp only [physicalMixedProfileRaising,
      (ambientMixedProfileAngularFields_eq_zero hF hO hD _ G hG K hz x hx).1,
      smul_zero,Finset.sum_const_zero]
  have hAdj : physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG x = 0 := by
    simp only [physicalMixedProfileAdjoint,
      (ambientMixedProfileAngularFields_eq_zero hF hO hD _ G hG K hz x hx).2,
      smul_zero,Finset.sum_const_zero]
  exact ⟨hU,hAdj,by rw [physicalMixedProfileDefect,hAdj,hU,sub_self]⟩

lemma hasCompactSupport_physicalMixedProfileFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG) ∧ HasCompactSupport (physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG) ∧
    HasCompactSupport (physicalMixedProfileDefect hF hO hD g L lam δ R p h G hG) := by
  exact ⟨HasCompactSupport.intro hK (fun x hx =>
    (physicalMixedProfileFields_eq_zero hF hO hD g L lam δ R p h G hG K hz x hx).1),
    HasCompactSupport.intro hK (fun x hx =>
      (physicalMixedProfileFields_eq_zero hF hO hD g L lam δ R p h G hG K hz x hx).2.1),
    HasCompactSupport.intro hK (fun x hx =>
      (physicalMixedProfileFields_eq_zero hF hO hD g L lam δ R p h G hG K hz x hx).2.2)⟩

lemma integrable_physicalMixedProfile_density_pairs
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (J : Set R3) (hJ : IsCompact J) (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedProfileDefect hF hO hD g L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) := by
  have hs := contDiff_physicalMixedProfileFields hF hO hD g L lam δ R p h hg hδ hR hh G hG
  have hS := contDiff_ambientSphereL2 H hH
  have hc := hasCompactSupport_ambientSphereL2 H hH J hJ hzH
  exact ⟨integrable_density_pair_of_contDiff g hg L lam _ _ hs.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.2 hS hc⟩

theorem compact_physicalMixedProfile_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (lam,x) *
        ⟪ambientSphereL2 G hG x,physicalMixedProfileAdjoint hF hO hD g L lam δ R p h H hH x⟫_ℝ := by
  have hLeft := (integrable_physicalMixedProfile_density_pairs hF hO hD g L lam δ R p h
    hg hδ hR hh G H hG hH J hJ hzH).1
  have hRight : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪ambientSphereL2 G hG x,physicalMixedProfileAdjoint hF hO hD g L lam δ R p h H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using
      (integrable_physicalMixedProfile_density_pairs hF hO hD g L lam δ R p h
        hg hδ hR hh H G hH hG K hK hzG).2.1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg
    (fun t : ℝ => referenceDensityFamily g L (lam,x)*t)
    (physicalMixedProfile_inner_adjoint hF hO hD g L lam δ R p h G H hG hH x))

theorem physicalMixedProfileDefect_quadratic_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ⟪physicalMixedProfileDefect hF hO hD g L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ = 0 := by
  have hAdj : ⟪physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG x,
      ambientSphereL2 G hG x⟫_ℝ =
      ⟪physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ := by
    calc
      _ = ⟪ambientSphereL2 G hG x,
        physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG x⟫_ℝ := real_inner_comm _ _
      _ = _ := (physicalMixedProfile_inner_adjoint hF hO hD g L lam δ R p h G G hG hG x).symm
  rw [physicalMixedProfileDefect,inner_sub_left,hAdj,sub_self]

theorem integral_physicalMixedProfileDefect_quadratic_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedProfileDefect hF hO hD g L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ) = 0 := by
  have hi := (integrable_physicalMixedProfile_density_pairs hF hO hD g L lam δ R p h
    hg hδ hR hh G G hG hG K hK hz).2.2
  simp only [physicalMixedProfileDefect_quadratic_zero hF hO hD g L lam δ R p h G hG,
    mul_zero,integral_zero]

end OAI.AnisotropicCalderon.ActualPhysicalMixedProfile
