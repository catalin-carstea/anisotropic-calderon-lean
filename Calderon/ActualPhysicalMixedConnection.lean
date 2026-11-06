import Calderon.ActualNormalizedSphereRotation
import Calderon.ActualAngularDerivativeBesselField
import Calderon.ActualHorizontalGeometry
import Calderon.ActualUnboundedFirstPrincipalFormBound
import Calderon.BalancedAngularShift

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualPhysicalMixedConnection
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BalancedAngularShift HarmonicDerivativeOperator
  SmoothSphereFields SmoothAngularApplication AmbientAngularShift SmoothMovingFrameFields
  SmoothAmbientAngularCasimir SmoothSphereRotationProjection WeightedSphereRotation
  ActualNormalizedSphereRotation AngularDerivativeBesselField ActualHorizontalNormBridge
  ActualUnboundedFirstPrincipalFormBound AmbientReferenceCovariantCore MovingFrameConnection
  ReferenceDensityBounds PrincipalCommutator

/- Actual A*Omega part of2h A*D+; factor2 cancels the native half rotation.
   The genuine angular adjoint keeps reverse order -R_bc A_a.
   Full trace/coframe/Gamma cancellation and physical U/J assembly remain separate. -/

def ambientMixedRaisingRotationField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (a b c : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  ambientRaisingField hF hO hD a (ambientAngularRotation b c G)
    (contDiff_ambientAngularRotation b c G hG)

def ambientMixedRotatedDerivativeField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (a b c : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => normalizedRotation hO hD b c (ambientDerivativeBesselField hF hO hD a G hG x)

lemma ambientMixedRotationField_graph (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (b c : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x,ambientSphereL2 (ambientAngularRotation b c G)
      (contDiff_ambientAngularRotation b c G hG) x) ∈ sphereRotationGraph hO hD b c := 
  fun k => sphereHarmonicCoordinate_ambientAngularRotation hO hD k b c G hG x

lemma ambientMixedRotatedDerivativeField_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (a b c : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientDerivativeField hF hO hD a G hG x,
      ambientMixedRotatedDerivativeField hF hO hD a b c G hG x) ∈ sphereRotationGraph hO hD b c := 
  normalizedRotation_graph hO hD b c _ _
    (ambientDerivativeBesselField_graph hF hO hD a G hG x)

theorem ambientMixedRaisingRotationField_inner_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (a b c : Fin 3)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪ambientMixedRaisingRotationField hF hO hD a b c G hG x,ambientSphereL2 H hH x⟫_ℝ =
      -⟪ambientSphereL2 G hG x,ambientMixedRotatedDerivativeField hF hO hD a b c H hH x⟫_ℝ := by
  calc
    _ = ⟪ambientSphereL2 (ambientAngularRotation b c G)
      (contDiff_ambientAngularRotation b c G hG) x,ambientDerivativeField hF hO hD a H hH x⟫_ℝ := by
      have hAdj := sphereDerivativeGraph_inner_adjoint hF hO hD a
        (ambientSphereL2 H hH x) (ambientDerivativeField hF hO hD a H hH x)
        (ambientSphereL2 (ambientAngularRotation b c G)
          (contDiff_ambientAngularRotation b c G hG) x)
        (ambientMixedRaisingRotationField hF hO hD a b c G hG x)
        (ambientDerivativeField_graph hF hO hD a H hH x)
        (ambientRaisingField_graph hF hO hD a (ambientAngularRotation b c G)
          (contDiff_ambientAngularRotation b c G hG) x)
      simpa only [real_inner_comm] using hAdj.symm
    _ = _ := sphereRotationGraph_inner_skew hO hD b c _ _ _ _
      (ambientMixedRotationField_graph hO hD b c G hG x)
      (ambientMixedRotatedDerivativeField_graph hF hO hD a b c H hH x)

lemma contDiff_ambientMixedConnectionAngularFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (a b c : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientMixedRaisingRotationField hF hO hD a b c G hG) ∧
    ContDiff ℝ ∞ (ambientMixedRotatedDerivativeField hF hO hD a b c G hG) := by
  exact ⟨contDiff_ambientRaisingField hF hO hD a (ambientAngularRotation b c G)
    (contDiff_ambientAngularRotation b c G hG),
    (normalizedRotation hO hD b c).contDiff.comp
      (contDiff_ambientDerivativeBesselField hF hO hD a G hG)⟩

lemma ambientMixedConnectionAngularFields_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (a b c : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    ambientMixedRaisingRotationField hF hO hD a b c G hG x = 0 ∧
    ambientMixedRotatedDerivativeField hF hO hD a b c G hG x = 0 := by
  constructor
  · exact ambientRaisingField_eq_zero hF hO hD a
      (ambientAngularRotation b c G) (contDiff_ambientAngularRotation b c G hG) K
      (ambientAngularRotation_sphere_zero b c G hG K hz) x hx
  · rw [ambientMixedRotatedDerivativeField,
      ambientDerivativeBesselField_eq_zero hF hO hD a G hG K hz x hx,map_zero]

lemma norm_half_ambientMixedRaisingRotationField_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (a b c : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖halfDegreeMultiplier hO hD (ambientMixedRaisingRotationField hF hO hD a b c G hG x)‖ ≤
      4*‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
  change ‖halfDegreeMultiplier hO hD
    (ambientRaisingField hF hO hD a (ambientAngularRotation b c G)
      (contDiff_ambientAngularRotation b c G hG) x)‖ ≤ _
  rw [← balancedRaising_ambient_realization hF hO hD a (ambientAngularRotation b c G)
    (contDiff_ambientAngularRotation b c G hG) x]
  have hRot : ‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
      (ambientAngularRotation b c G) (contDiff_ambientAngularRotation b c G hG) x‖^2 ≤
      2*‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖^2 := by
    convert norm_sq_ambient_weighted_rotation_le hO hD (1/2 : ℝ) (by norm_num) b c G hG x using 1 <;> norm_num
  have hRot' : ‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
      (ambientAngularRotation b c G) (contDiff_ambientAngularRotation b c G hG) x‖ ≤
      2*‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ := by
    nlinarith [norm_nonneg (ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
      (ambientAngularRotation b c G) (contDiff_ambientAngularRotation b c G hG) x),
      norm_nonneg (ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x)]
  have hRaise := ((balancedRaising hF hO hD a).le_opNorm
    (ambientBesselField hO hD (1/2 : ℝ) (by norm_num)
      (ambientAngularRotation b c G) (contDiff_ambientAngularRotation b c G hG) x)).trans
    (mul_le_mul_of_nonneg_right (norm_balancedRaising_le hF hO hD a) (norm_nonneg _))
  nlinarith

lemma abs_inner_ambientMixedRaisingRotationField_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (a b c : Fin 3)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    |⟪ambientMixedRaisingRotationField hF hO hD a b c G hG x,ambientSphereL2 H hH x⟫_ℝ| ≤
      4*‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ *
        ‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num) H hH x‖ := by
  rw [inner_eq_halfDegreeMultiplier hO hD _ _ _
    (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) H hH x)]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_half_ambientMixedRaisingRotationField_le hF hO hD a b c G hG x) (norm_nonneg _))

def physicalMixedConnectionCoefficient (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (a b c : Fin 3) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, h x i j * referenceCoFrameEntry g L i a (lam,x) *
    referenceFrameConnectionCoefficient g L lam x (coordinateDirection j) b c

lemma contDiff_physicalMixedConnectionCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (a b c : Fin 3) : ContDiff ℝ ∞ (physicalMixedConnectionCoefficient g L lam h a b c) := by
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    ((hh i j).mul ((contDiff_referenceCoFrameEntry g hg L i a).comp
      (contDiff_const.prodMk contDiff_id))).mul
      (contDiff_referenceFrameConnectionCoefficient_field g hg L lam
        (fun _ => coordinateDirection j) contDiff_const b c)

lemma physicalMixedConnectionCoefficient_bound (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (x : R3) (eps radius M Kappa : ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M) (hKappa : 0 ≤ Kappa)
    (hh : ∀ i j, |h x i j| ≤ eps*radius)
    (hframe : ∀ i a, |referenceCoFrameEntry g L i a (lam,x)| ≤ M)
    (hconnection : ∀ j b c, |referenceFrameConnectionCoefficient g L lam x (coordinateDirection j) b c| ≤ Kappa) (a b c : Fin 3) :
    |physicalMixedConnectionCoefficient g L lam h a b c x| ≤ 9*M*Kappa*eps*radius := by
  have ht (i j : Fin 3) : |h x i j*referenceCoFrameEntry g L i a (lam,x)*
      referenceFrameConnectionCoefficient g L lam x (coordinateDirection j) b c| ≤
      eps*radius*M*Kappa := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul
      (mul_le_mul (hh i j) (hframe i a) (abs_nonneg _) (mul_nonneg heps hradius))
      (hconnection j b c) (abs_nonneg _) (mul_nonneg (mul_nonneg heps hradius) hM)
  calc
    _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, h x i j*referenceCoFrameEntry g L i a (lam,x)*
        referenceFrameConnectionCoefficient g L lam x (coordinateDirection j) b c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |h x i j*referenceCoFrameEntry g L i a (lam,x)*
        referenceFrameConnectionCoefficient g L lam x (coordinateDirection j) b c| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, eps*radius*M*Kappa :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = 9*M*Kappa*eps*radius := by simp only [Fin.sum_univ_three]; ring

def physicalMixedConnectionRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, physicalMixedConnectionCoefficient g L lam h a b c x •
    ambientMixedRaisingRotationField hF hO hD a b c G hG x

def physicalMixedConnectionAdjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (-physicalMixedConnectionCoefficient g L lam h a b c x) •
    ambientMixedRotatedDerivativeField hF hO hD a b c G hG x

def physicalMixedConnectionDefect
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  physicalMixedConnectionAdjoint hF hO hD g L lam h G hG x -
    physicalMixedConnectionRaising hF hO hD g L lam h G hG x

theorem physicalMixedConnection_inner_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : R3) :
    ⟪physicalMixedConnectionRaising hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ =
      ⟪ambientSphereL2 G hG x,physicalMixedConnectionAdjoint hF hO hD g L lam h H hH x⟫_ℝ := by
  simp only [physicalMixedConnectionRaising,physicalMixedConnectionAdjoint,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right,
    ambientMixedRaisingRotationField_inner_adjoint hF hO hD _ _ _ G H hG hH x,mul_neg,neg_mul]

lemma contDiff_physicalMixedConnectionFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (physicalMixedConnectionRaising hF hO hD g L lam h G hG) ∧ ContDiff ℝ ∞ (physicalMixedConnectionAdjoint hF hO hD g L lam h G hG) ∧
    ContDiff ℝ ∞ (physicalMixedConnectionDefect hF hO hD g L lam h G hG) := by
  have hU : ContDiff ℝ ∞ (physicalMixedConnectionRaising hF hO hD g L lam h G hG) :=
    ContDiff.sum fun a _ => ContDiff.sum fun b _ => ContDiff.sum fun c _ =>
      (contDiff_physicalMixedConnectionCoefficient g hg L lam h hh a b c).smul
        (contDiff_ambientMixedConnectionAngularFields hF hO hD a b c G hG).1
  have hAdj : ContDiff ℝ ∞ (physicalMixedConnectionAdjoint hF hO hD g L lam h G hG) :=
    ContDiff.sum fun a _ => ContDiff.sum fun b _ => ContDiff.sum fun c _ =>
      (contDiff_physicalMixedConnectionCoefficient g hg L lam h hh a b c).neg.smul
        (contDiff_ambientMixedConnectionAngularFields hF hO hD a b c G hG).2
  exact ⟨hU,hAdj,hAdj.sub hU⟩

lemma physicalMixedConnectionFields_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    physicalMixedConnectionRaising hF hO hD g L lam h G hG x = 0 ∧ physicalMixedConnectionAdjoint hF hO hD g L lam h G hG x = 0 ∧ physicalMixedConnectionDefect hF hO hD g L lam h G hG x = 0 := by
  have hU : physicalMixedConnectionRaising hF hO hD g L lam h G hG x = 0 := by
    simp only [physicalMixedConnectionRaising,
      (ambientMixedConnectionAngularFields_eq_zero hF hO hD _ _ _ G hG K hz x hx).1,
      smul_zero,Finset.sum_const_zero]
  have hAdj : physicalMixedConnectionAdjoint hF hO hD g L lam h G hG x = 0 := by
    simp only [physicalMixedConnectionAdjoint,
      (ambientMixedConnectionAngularFields_eq_zero hF hO hD _ _ _ G hG K hz x hx).2,
      smul_zero,Finset.sum_const_zero]
  exact ⟨hU,hAdj,by rw [physicalMixedConnectionDefect,hAdj,hU,sub_self]⟩

lemma hasCompactSupport_physicalMixedConnectionFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (physicalMixedConnectionRaising hF hO hD g L lam h G hG) ∧ HasCompactSupport (physicalMixedConnectionAdjoint hF hO hD g L lam h G hG) ∧
    HasCompactSupport (physicalMixedConnectionDefect hF hO hD g L lam h G hG) := by
  exact ⟨HasCompactSupport.intro hK (fun x hx =>
    (physicalMixedConnectionFields_eq_zero hF hO hD g L lam h G hG K hz x hx).1),
    HasCompactSupport.intro hK (fun x hx =>
      (physicalMixedConnectionFields_eq_zero hF hO hD g L lam h G hG K hz x hx).2.1),
    HasCompactSupport.intro hK (fun x hx =>
      (physicalMixedConnectionFields_eq_zero hF hO hD g L lam h G hG K hz x hx).2.2)⟩

lemma integrable_physicalMixedConnection_density_pairs
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (J : Set R3) (hJ : IsCompact J) (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedConnectionRaising hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedConnectionAdjoint hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedConnectionDefect hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ) := by
  have hs := contDiff_physicalMixedConnectionFields hF hO hD g L lam h hg hh G hG
  have hS := contDiff_ambientSphereL2 H hH
  have hc := hasCompactSupport_ambientSphereL2 H hH J hJ hzH
  exact ⟨integrable_density_pair_of_contDiff g hg L lam _ _ hs.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.2 hS hc⟩

theorem compact_physicalMixedConnection_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedConnectionRaising hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (lam,x) *
        ⟪ambientSphereL2 G hG x,physicalMixedConnectionAdjoint hF hO hD g L lam h H hH x⟫_ℝ := by
  have hLeft := (integrable_physicalMixedConnection_density_pairs hF hO hD g L lam h hg hh
    G H hG hH J hJ hzH).1
  have hRight : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪ambientSphereL2 G hG x,physicalMixedConnectionAdjoint hF hO hD g L lam h H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using
      (integrable_physicalMixedConnection_density_pairs hF hO hD g L lam h hg hh
        H G hH hG K hK hzG).2.1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg
    (fun t : ℝ => referenceDensityFamily g L (lam,x)*t)
    (physicalMixedConnection_inner_adjoint hF hO hD g L lam h G H hG hH x))

theorem physicalMixedConnectionDefect_quadratic_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ⟪physicalMixedConnectionDefect hF hO hD g L lam h G hG x,ambientSphereL2 G hG x⟫_ℝ = 0 := by
  have hAdj : ⟪physicalMixedConnectionAdjoint hF hO hD g L lam h G hG x,ambientSphereL2 G hG x⟫_ℝ =
      ⟪physicalMixedConnectionRaising hF hO hD g L lam h G hG x,ambientSphereL2 G hG x⟫_ℝ := by
    calc
      _ = ⟪ambientSphereL2 G hG x,physicalMixedConnectionAdjoint hF hO hD g L lam h G hG x⟫_ℝ :=
        real_inner_comm _ _
      _ = _ := (physicalMixedConnection_inner_adjoint hF hO hD g L lam h G G hG hG x).symm
  rw [physicalMixedConnectionDefect,inner_sub_left,hAdj,sub_self]

theorem integral_physicalMixedConnectionDefect_quadratic_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedConnectionDefect hF hO hD g L lam h G hG x,ambientSphereL2 G hG x⟫_ℝ) = 0 := by
  have hi := (integrable_physicalMixedConnection_density_pairs hF hO hD g L lam h hg hh
    G G hG hG K hK hz).2.2
  simp only [physicalMixedConnectionDefect_quadratic_zero hF hO hD g L lam h G hG,
    mul_zero,integral_zero]

theorem abs_inner_physicalMixedConnection_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (x : R3) (eps radius M Kappa : ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M) (hKappa : 0 ≤ Kappa)
    (hh : ∀ i j, |h x i j| ≤ eps*radius)
    (hframe : ∀ i a, |referenceCoFrameEntry g L i a (lam,x)| ≤ M)
    (hconnection : ∀ j b c, |referenceFrameConnectionCoefficient g L lam x (coordinateDirection j) b c| ≤ Kappa) :
    |⟪physicalMixedConnectionRaising hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ| ≤
      972*M*Kappa*eps*radius *
        ‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖ *
          ‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num) H hH x‖ := by
  have ht (a b c : Fin 3) : |physicalMixedConnectionCoefficient g L lam h a b c x * ⟪ambientMixedRaisingRotationField hF hO hD a b c G hG x,ambientSphereL2 H hH x⟫_ℝ| ≤
      (9*M*Kappa*eps*radius)*(4*‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖*‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num) H hH x‖) := by
    rw [abs_mul]
    exact mul_le_mul
      (physicalMixedConnectionCoefficient_bound g L lam h x eps radius M Kappa
        heps hradius hM hKappa hh hframe hconnection a b c)
      (abs_inner_ambientMixedRaisingRotationField_le hF hO hD a b c G H hG hH x)
      (abs_nonneg _) (by positivity)
  simp only [physicalMixedConnectionRaising,sum_inner,real_inner_smul_left]
  calc
    _ ≤ ∑ a : Fin 3, |∑ b : Fin 3, ∑ c : Fin 3, physicalMixedConnectionCoefficient g L lam h a b c x * ⟪ambientMixedRaisingRotationField hF hO hD a b c G hG x,ambientSphereL2 H hH x⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, |∑ c : Fin 3, physicalMixedConnectionCoefficient g L lam h a b c x * ⟪ambientMixedRaisingRotationField hF hO hD a b c G hG x,ambientSphereL2 H hH x⟫_ℝ| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, |physicalMixedConnectionCoefficient g L lam h a b c x * ⟪ambientMixedRaisingRotationField hF hO hD a b c G hG x,ambientSphereL2 H hH x⟫_ℝ| :=
      Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        (9*M*Kappa*eps*radius)*(4*‖ambientBesselField hO hD (3/2 : ℝ) (by norm_num) G hG x‖*‖ambientBesselField hO hD (1/2 : ℝ) (by norm_num) H hH x‖) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ => ht a b c)))
    _ = _ := by simp only [Fin.sum_univ_three]; ring

end OAI.AnisotropicCalderon.ActualPhysicalMixedConnection
