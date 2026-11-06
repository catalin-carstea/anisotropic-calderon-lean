import Calderon.ActualAngularDerivativeBesselField
import Calderon.ActualHorizontalGeometry
import Calderon.ActualUnboundedFirstPrincipalFormBound

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualPhysicalPureAngular
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph AngularWeightedCore BoundedAngularShift HarmonicDerivativeOperator
  SmoothSphereFields SmoothAngularApplication AmbientAngularShift
  AngularDerivativeBesselField ActualHorizontalNormBridge ActualScalarPrincipalAdjoint
  ActualUnboundedFirstPrincipalFormBound ReferenceDensityBounds ConformalDepth

/- Source-only author candidate. The ordinary-coordinate coefficient is converted
   with the actual reference coframe. This is the literal pure A* A* component
   of manuscript U, without any identification with full physical U or H. -/

lemma inverseDegreeWeight_second_sum (m : ℕ) :
    inverseDegreeWeight m * (besselWeight 2 m+besselWeight 1 m) = besselWeight 1 (m+1) := by
  simp only [inverseDegreeWeight,besselWeight,Real.rpow_two,Real.rpow_one]
  push_cast
  field_simp
  ring

def ambientRaisingBesselField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedRaising hF hO hD i
    (ambientBesselField hO hD 2 (by norm_num) G hG x +
      ambientBesselField hO hD 1 (by norm_num) G hG x)

lemma ambientRaisingBesselField_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientRaisingField hF hO hD i G hG x, ambientRaisingBesselField hF hO hD i G hG x) ∈
      sphereBesselGraph hO hD 1 := by
  intro m
  cases m with
  | zero =>
    change sphereHarmonicCoordinate hO hD 0
      (normalizedRaisingOutput hF hO hD i
        (ambientBesselField hO hD 2 (by norm_num) G hG x +
          ambientBesselField hO hD 1 (by norm_num) G hG x)) = _
    rw [(normalizedRaisingOutput_graph hF hO hD i _).1,
      (ambientRaisingField_graph hF hO hD i G hG x).1,smul_zero]
  | succ m =>
    change sphereHarmonicCoordinate hO hD (m+1)
      (normalizedRaisingOutput hF hO hD i
        (ambientBesselField hO hD 2 (by norm_num) G hG x +
          ambientBesselField hO hD 1 (by norm_num) G hG x)) = _
    rw [(normalizedRaisingOutput_graph hF hO hD i _).2 m,
      inverseDegreeMultiplier_coordinate,map_add,
      ambientBesselField_graph hO hD 2 (by norm_num) G hG x m,
      ambientBesselField_graph hO hD 1 (by norm_num) G hG x m,
      ← add_smul,smul_smul,map_smul,inverseDegreeWeight_second_sum,
      (ambientRaisingField_graph hF hO hD i G hG x).2 m]

lemma contDiff_ambientRaisingBesselField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientRaisingBesselField hF hO hD i G hG) := 
  (normalizedRaising hF hO hD i).contDiff.comp
    ((contDiff_ambientBesselField hO hD 2 (by norm_num) G hG).add
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG))

def ambientDoubleRaisingField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i j : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedRaising hF hO hD i (ambientRaisingBesselField hF hO hD j G hG x)

def ambientDoubleDerivativeField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i j : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedDerivative hF hO hD i (ambientDerivativeBesselField hF hO hD j G hG x)

lemma ambientDoubleRaisingField_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i j : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientRaisingField hF hO hD j G hG x, ambientDoubleRaisingField hF hO hD i j G hG x) ∈
      sphereRaisingGraph hF hO hD i := 
  normalizedRaising_graph hF hO hD i _ _
    (ambientRaisingBesselField_graph hF hO hD j G hG x)

lemma ambientDoubleDerivativeField_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i j : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientDerivativeField hF hO hD j G hG x, ambientDoubleDerivativeField hF hO hD i j G hG x) ∈
      sphereDerivativeGraph hF hO hD i := 
  normalizedDerivative_graph hF hO hD i _ _
    (ambientDerivativeBesselField_graph hF hO hD j G hG x)

theorem ambientDoubleRaisingField_inner_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i j : Fin 3)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪ambientDoubleRaisingField hF hO hD i j G hG x, ambientSphereL2 H hH x⟫_ℝ =
      ⟪ambientSphereL2 G hG x, ambientDoubleDerivativeField hF hO hD j i H hH x⟫_ℝ := by
  calc
    _ = ⟪ambientRaisingField hF hO hD j G hG x,
        ambientDerivativeField hF hO hD i H hH x⟫_ℝ := by
      have hAdj := sphereDerivativeGraph_inner_adjoint hF hO hD i
        (ambientSphereL2 H hH x) (ambientDerivativeField hF hO hD i H hH x)
        (ambientRaisingField hF hO hD j G hG x)
        (ambientDoubleRaisingField hF hO hD i j G hG x)
        (ambientDerivativeField_graph hF hO hD i H hH x)
        (ambientDoubleRaisingField_graph hF hO hD i j G hG x)
      simpa only [real_inner_comm] using hAdj.symm
    _ = _ := by
      have hAdj := sphereDerivativeGraph_inner_adjoint hF hO hD j
        (ambientDerivativeField hF hO hD i H hH x)
        (ambientDoubleDerivativeField hF hO hD j i H hH x)
        (ambientSphereL2 G hG x) (ambientRaisingField hF hO hD j G hG x)
        (ambientDoubleDerivativeField_graph hF hO hD j i H hH x)
        (ambientRaisingField_graph hF hO hD j G hG x)
      simpa only [real_inner_comm] using hAdj.symm

lemma contDiff_ambientDoubleAngularFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i j : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientDoubleRaisingField hF hO hD i j G hG) ∧
    ContDiff ℝ ∞ (ambientDoubleDerivativeField hF hO hD i j G hG) := by
  exact ⟨(normalizedRaising hF hO hD i).contDiff.comp
    (contDiff_ambientRaisingBesselField hF hO hD j G hG),
    (normalizedDerivative hF hO hD i).contDiff.comp
      (contDiff_ambientDerivativeBesselField hF hO hD j G hG)⟩

def physicalPureAngularCoefficient (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (a b : Fin 3) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (h x i j / referenceRadius δ R p L x) *
      referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)

lemma contDiff_physicalPureAngularCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (a b : Fin 3) :
    ContDiff ℝ ∞ (physicalPureAngularCoefficient g L lam δ R p h a b) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (((hh i j).div (contDiff_referenceRadius_actual δ R p L hδ hR)
    (fun y => (referenceRadius_pos δ R p L y hδ hR).ne')).mul
      ((contDiff_referenceCoFrameEntry g hg L i a).comp
        (contDiff_const.prodMk contDiff_id))).mul
    ((contDiff_referenceCoFrameEntry g hg L j b).comp
      (contDiff_const.prodMk contDiff_id))

lemma physicalPureAngularCoefficient_bound (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R) (x : R3) (eps M : ℝ)
    (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (hh : ∀ i j, |h x i j| ≤ eps * referenceRadius δ R p L x)
    (hframe : ∀ i a, |referenceCoFrameEntry g L i a (lam,x)| ≤ M) (a b : Fin 3) :
    |physicalPureAngularCoefficient g L lam δ R p h a b x| ≤ 9*M^2*eps := by
  have hr := referenceRadius_pos δ R p L x hδ hR
  have hterm (i j : Fin 3) :
      |(h x i j / referenceRadius δ R p L x) *
        referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)| ≤
        eps*M*M := by
    have hdiv : |h x i j / referenceRadius δ R p L x| ≤ eps := by
      rw [abs_div,abs_of_pos hr]
      exact (div_le_iff₀ hr).mpr (hh i j)
    rw [abs_mul,abs_mul]
    exact mul_le_mul
      (mul_le_mul hdiv (hframe i a) (abs_nonneg _) heps)
      (hframe j b) (abs_nonneg _) (mul_nonneg heps hM)
  calc
    _ ≤ ∑ i : Fin 3, |∑ j : Fin 3,
        (h x i j / referenceRadius δ R p L x) *
          referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        |(h x i j / referenceRadius δ R p L x) *
          referenceCoFrameEntry g L i a (lam,x) * referenceCoFrameEntry g L j b (lam,x)| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, eps*M*M :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = 9*M^2*eps := by simp only [Fin.sum_univ_three]; ring

def physicalPureAngularRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, ∑ b : Fin 3, physicalPureAngularCoefficient g L lam δ R p h a b x •
    ambientDoubleRaisingField hF hO hD a b G hG x

def physicalPureAngularAdjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, ∑ b : Fin 3, physicalPureAngularCoefficient g L lam δ R p h a b x •
    ambientDoubleDerivativeField hF hO hD b a G hG x

def physicalPureAngularDefect
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG x -
    physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x

theorem physicalPureAngular_inner_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)    
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x, ambientSphereL2 H hH x⟫_ℝ =
      ⟪ambientSphereL2 G hG x, physicalPureAngularAdjoint hF hO hD g L lam δ R p h H hH x⟫_ℝ := by
  simp only [physicalPureAngularRaising,physicalPureAngularAdjoint,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right,
    ambientDoubleRaisingField_inner_adjoint hF hO hD _ _ G H hG hH x]

lemma contDiff_physicalPureAngularFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (physicalPureAngularRaising hF hO hD g L lam δ R p h G hG) ∧
    ContDiff ℝ ∞ (physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG) ∧
    ContDiff ℝ ∞ (physicalPureAngularDefect hF hO hD g L lam δ R p h G hG) := by
  have hU : ContDiff ℝ ∞ (physicalPureAngularRaising hF hO hD g L lam δ R p h G hG) :=
    ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
      (contDiff_physicalPureAngularCoefficient g hg L lam δ R p h hδ hR hh a b).smul
        (contDiff_ambientDoubleAngularFields hF hO hD a b G hG).1
  have hAdj : ContDiff ℝ ∞ (physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG) :=
    ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
      (contDiff_physicalPureAngularCoefficient g hg L lam δ R p h hδ hR hh a b).smul
        (contDiff_ambientDoubleAngularFields hF hO hD b a G hG).2
  exact ⟨hU,hAdj,hAdj.sub hU⟩

lemma physicalPureAngularFields_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x = 0 ∧ physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG x = 0 ∧ physicalPureAngularDefect hF hO hD g L lam δ R p h G hG x = 0 := by
  have hRaise (a b : Fin 3) : ambientDoubleRaisingField hF hO hD a b G hG x = 0 := by
    simp only [ambientDoubleRaisingField,ambientRaisingBesselField,
      ambientBesselField_eq_zero hO hD 2 (by norm_num) G hG K hz x hx,
      ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
      zero_add,map_zero]
  have hDeriv (a b : Fin 3) : ambientDoubleDerivativeField hF hO hD a b G hG x = 0 := by
    rw [ambientDoubleDerivativeField,
      ambientDerivativeBesselField_eq_zero hF hO hD b G hG K hz x hx,map_zero]
  have hU : physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x = 0 := by
    simp only [physicalPureAngularRaising,hRaise,smul_zero,Finset.sum_const_zero]
  have hAdj : physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG x = 0 := by
    simp only [physicalPureAngularAdjoint,hDeriv,smul_zero,Finset.sum_const_zero]
  exact ⟨hU,hAdj,by rw [physicalPureAngularDefect,hAdj,hU,sub_self]⟩

lemma hasCompactSupport_physicalPureAngularFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (physicalPureAngularRaising hF hO hD g L lam δ R p h G hG) ∧ HasCompactSupport (physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG) ∧ HasCompactSupport (physicalPureAngularDefect hF hO hD g L lam δ R p h G hG) := by
  exact ⟨HasCompactSupport.intro hK (fun x hx =>
    (physicalPureAngularFields_eq_zero hF hO hD g L lam δ R p h G hG K hz x hx).1),
    HasCompactSupport.intro hK (fun x hx =>
      (physicalPureAngularFields_eq_zero hF hO hD g L lam δ R p h G hG K hz x hx).2.1),
    HasCompactSupport.intro hK (fun x hx =>
      (physicalPureAngularFields_eq_zero hF hO hD g L lam δ R p h G hG K hz x hx).2.2)⟩

lemma integrable_physicalPureAngular_density_pairs
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K : Set R3) (hK : IsCompact K) (hzH : ∀ x ∉ K, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalPureAngularDefect hF hO hD g L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) := by
  have hs := contDiff_physicalPureAngularFields hF hO hD g L lam δ R p h hg hδ hR hh G hG
  have hS := contDiff_ambientSphereL2 H hH
  have hc := hasCompactSupport_ambientSphereL2 H hH K hK hzH
  exact ⟨integrable_density_pair_of_contDiff g hg L lam _ _ hs.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.2 hS hc⟩

theorem compact_physicalPureAngular_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (lam,x) *
        ⟪ambientSphereL2 G hG x,physicalPureAngularAdjoint hF hO hD g L lam δ R p h H hH x⟫_ℝ := by
  have hLeft := (integrable_physicalPureAngular_density_pairs hF hO hD g L lam δ R p h
    hg hδ hR hh G H hG hH J hJ hzH).1
  have hRight : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪ambientSphereL2 G hG x,
        physicalPureAngularAdjoint hF hO hD g L lam δ R p h H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using
      (integrable_physicalPureAngular_density_pairs hF hO hD g L lam δ R p h
        hg hδ hR hh H G hH hG K hK hzG).2.1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg
    (fun t : ℝ => referenceDensityFamily g L (lam,x)*t)
    (physicalPureAngular_inner_adjoint hF hO hD g L lam δ R p h G H hG hH x))

theorem physicalPureAngularDefect_quadratic_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ⟪physicalPureAngularDefect hF hO hD g L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ = 0 := by
  have hAdj : ⟪physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG x,
      ambientSphereL2 G hG x⟫_ℝ =
      ⟪physicalPureAngularRaising hF hO hD g L lam δ R p h G hG x,
        ambientSphereL2 G hG x⟫_ℝ := by
    calc
      _ = ⟪ambientSphereL2 G hG x,
        physicalPureAngularAdjoint hF hO hD g L lam δ R p h G hG x⟫_ℝ := real_inner_comm _ _
      _ = _ := (physicalPureAngular_inner_adjoint hF hO hD g L lam δ R p h G G hG hG x).symm
  rw [physicalPureAngularDefect,inner_sub_left,hAdj,sub_self]

theorem integral_physicalPureAngularDefect_quadratic_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalPureAngularDefect hF hO hD g L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ) = 0 := by
  have hi := (integrable_physicalPureAngular_density_pairs hF hO hD g L lam δ R p h
    hg hδ hR hh G G hG hG K hK hz).2.2
  simp only [physicalPureAngularDefect_quadratic_zero hF hO hD g L lam δ R p h G hG,
    mul_zero,integral_zero]

end OAI.AnisotropicCalderon.ActualPhysicalPureAngular
