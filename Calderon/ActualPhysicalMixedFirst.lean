import Calderon.ActualRawMixedPrincipalCollection
import Calderon.ActualHorizontalGeometry
import Calderon.AmbientAngularShift
import Calderon.ActualUnboundedFirstPrincipalFormBound

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualPhysicalMixedFirst
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift HarmonicDerivativeOperator
  SmoothSphereFields SmoothAngularApplication AmbientAngularShift ActualHorizontalNormBridge
  ActualRawMixedPrincipalCollection ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds PrincipalCommutator

/- Actual first-base part of manuscript mixed perturbation2h A*D+.
   Ordinary-coordinate h is converted with the actual coframe. The density
   adjoint uses true raw angular graph outputs and reversed base order. -/

def physicalMixedFirstCoefficient (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (a j : Fin 3) (x : R3) : ℝ :=
  2 * ∑ i : Fin 3, h x i j * referenceCoFrameEntry g L i a (lam,x)

lemma contDiff_physicalMixedFirstCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (a j : Fin 3) : ContDiff ℝ ∞ (physicalMixedFirstCoefficient g L lam h a j) := by
  unfold physicalMixedFirstCoefficient
  exact contDiff_const.mul (ContDiff.sum (fun i _ => (hh i j).mul
    ((contDiff_referenceCoFrameEntry g hg L i a).comp
      (contDiff_const.prodMk contDiff_id))))

lemma physicalMixedFirstCoefficient_bound (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (x : R3) (eps radius M : ℝ) (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M)
    (hh : ∀ i j, |h x i j| ≤ eps * radius)
    (hframe : ∀ i a, |referenceCoFrameEntry g L i a (lam,x)| ≤ M) (a j : Fin 3) :
    |physicalMixedFirstCoefficient g L lam h a j x| ≤ 6*M*eps*radius := by
  have ht (i : Fin 3) : |h x i j*referenceCoFrameEntry g L i a (lam,x)| ≤ eps*radius*M := by
    rw [abs_mul]
    exact mul_le_mul (hh i j) (hframe i a) (abs_nonneg _)
      (mul_nonneg heps hradius)
  rw [physicalMixedFirstCoefficient,abs_mul]
  rw [show |(2 : ℝ)| = 2 by norm_num]
  calc
    _ ≤ 2*∑ i : Fin 3, |h x i j*referenceCoFrameEntry g L i a (lam,x)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2*∑ i : Fin 3, eps*radius*M :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ht i)) (by norm_num)
    _ = 6*M*eps*radius := by simp only [Fin.sum_univ_three]; ring

def physicalMixedFirstRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  frameRaisingFirst (physicalMixedFirstCoefficient g L lam h)
    (fun a => ambientRaisingField hF hO hD a G hG)

def physicalMixedFirstAdjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  frameRaisingFirstAdjoint (fun y => referenceDensityFamily g L (lam,y))
    (physicalMixedFirstCoefficient g L lam h)
    (fun a => ambientDerivativeField hF hO hD a G hG)

def physicalMixedFirstDefect
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => physicalMixedFirstAdjoint hF hO hD g L lam h G hG x -
    physicalMixedFirstRaising hF hO hD g L lam h G hG x

def physicalMixedDensityCorrection (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (a : Fin 3) : R3 → ℝ :=
  frameDensityCorrection (fun y => referenceDensityFamily g L (lam,y))
    (physicalMixedFirstCoefficient g L lam h) a

lemma physicalMixedFirst_raising_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (a j : Fin 3) (x : R3) :
    (directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x,
      directionalFDeriv (coordinateDirection j) (ambientRaisingField hF hO hD a G hG) x) ∈
        sphereRaisingGraph hF hO hD a := 
  directionalFDeriv_sphereRaisingGraph hF hO hD a (coordinateDirection j)
    (ambientSphereL2 G hG) (ambientRaisingField hF hO hD a G hG)
    (contDiff_ambientSphereL2 G hG) (contDiff_ambientRaisingField hF hO hD a G hG)
    (ambientRaisingField_graph hF hO hD a G hG) x

theorem physicalMixedFirst_angular_pairing
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (a j : Fin 3) (x : R3) :
    ⟪directionalFDeriv (coordinateDirection j) (ambientRaisingField hF hO hD a G hG) x,
      ambientSphereL2 H hH x⟫_ℝ =
      ⟪directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x,
        ambientDerivativeField hF hO hD a H hH x⟫_ℝ := 
  raising_derivative_inner_transport hF hO hD a (coordinateDirection j)
    (ambientSphereL2 G hG) (ambientRaisingField hF hO hD a G hG)
    (ambientSphereL2 H hH) (ambientDerivativeField hF hO hD a H hH)
    (contDiff_ambientSphereL2 G hG) (contDiff_ambientRaisingField hF hO hD a G hG)
    (ambientRaisingField_graph hF hO hD a G hG)
    (ambientDerivativeField_graph hF hO hD a H hH) x

lemma contDiff_physicalMixedFirstFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (physicalMixedFirstRaising hF hO hD g L lam h G hG) ∧
    ContDiff ℝ ∞ (physicalMixedFirstAdjoint hF hO hD g L lam h G hG) ∧
    ContDiff ℝ ∞ (physicalMixedFirstDefect hF hO hD g L lam h G hG) := by
  have hm : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (lam,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hp : ∀ y : R3, referenceDensityFamily g L (lam,y) ≠ 0 :=
    fun y => (referenceDensityFamily_pos g hg L (lam,y)).ne'
  have hc : ∀ a j, ContDiff ℝ ∞ (physicalMixedFirstCoefficient g L lam h a j) :=
    contDiff_physicalMixedFirstCoefficient g hg L lam h hh
  have hU : ContDiff ℝ ∞ (physicalMixedFirstRaising hF hO hD g L lam h G hG) :=
    contDiff_frameRaisingFirst _ _ hc (fun a => contDiff_ambientRaisingField hF hO hD a G hG)
  have hAdj : ContDiff ℝ ∞ (physicalMixedFirstAdjoint hF hO hD g L lam h G hG) :=
    contDiff_frameRaisingFirstAdjoint _ _ _ hm hc
      (fun a => contDiff_ambientDerivativeField hF hO hD a G hG) hp
  exact ⟨hU,hAdj,hAdj.sub hU⟩

lemma contDiff_physicalMixedDensityCorrection (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedDensityCorrection g L lam h a) := by
  have hm : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (lam,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hp : ∀ y : R3, referenceDensityFamily g L (lam,y) ≠ 0 :=
    fun y => (referenceDensityFamily_pos g hg L (lam,y)).ne'
  have hc : ∀ a j, ContDiff ℝ ∞ (physicalMixedFirstCoefficient g L lam h a j) :=
    contDiff_physicalMixedFirstCoefficient g hg L lam h hh
  exact contDiff_frameDensityCorrection _ _ hm hc hp a

theorem physicalMixedFirstAdjoint_coefficient_form
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalMixedFirstAdjoint hF hO hD g L lam h G hG x =
      (∑ a : Fin 3, ∑ j : Fin 3, (-physicalMixedFirstCoefficient g L lam h a j x) •
        directionalFDeriv (coordinateDirection j) (ambientDerivativeField hF hO hD a G hG) x) +
      ∑ a : Fin 3, physicalMixedDensityCorrection g L lam h a x •
        ambientDerivativeField hF hO hD a G hG x := by
  have hm : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (lam,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hp : ∀ y : R3, referenceDensityFamily g L (lam,y) ≠ 0 :=
    fun y => (referenceDensityFamily_pos g hg L (lam,y)).ne'
  have hc : ∀ a j, ContDiff ℝ ∞ (physicalMixedFirstCoefficient g L lam h a j) :=
    contDiff_physicalMixedFirstCoefficient g hg L lam h hh
  exact frameRaisingFirstAdjoint_coefficient_form _ _ _ hm hc
    (fun a => contDiff_ambientDerivativeField hF hO hD a G hG) hp x

theorem physicalMixedFirstDefect_coefficient_form
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalMixedFirstDefect hF hO hD g L lam h G hG x =
      (∑ a : Fin 3, ∑ j : Fin 3, (-physicalMixedFirstCoefficient g L lam h a j x) •
        (directionalFDeriv (coordinateDirection j) (ambientDerivativeField hF hO hD a G hG) x +
          directionalFDeriv (coordinateDirection j) (ambientRaisingField hF hO hD a G hG) x)) +
      ∑ a : Fin 3, physicalMixedDensityCorrection g L lam h a x •
        ambientDerivativeField hF hO hD a G hG x := by
  rw [physicalMixedFirstDefect,
    physicalMixedFirstAdjoint_coefficient_form hF hO hD g L lam h hg hh G hG x]
  simp only [physicalMixedFirstRaising,frameRaisingFirst,smul_add,neg_smul,
    Finset.sum_add_distrib,Finset.sum_neg_distrib]
  abel

lemma hasCompactSupport_physicalMixedFirstFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (physicalMixedFirstRaising hF hO hD g L lam h G hG) ∧
    HasCompactSupport (physicalMixedFirstAdjoint hF hO hD g L lam h G hG) ∧
    HasCompactSupport (physicalMixedFirstDefect hF hO hD g L lam h G hG) := by
  have hU : HasCompactSupport (physicalMixedFirstRaising hF hO hD g L lam h G hG) :=
    hasCompactSupport_frameRaisingFirst _ _
      (fun a => hasCompactSupport_ambientRaisingField hF hO hD a G hG K hK hz)
  have hAdj : HasCompactSupport (physicalMixedFirstAdjoint hF hO hD g L lam h G hG) :=
    hasCompactSupport_frameRaisingFirstAdjoint _ _ _
      (fun a => hasCompactSupport_ambientDerivativeField hF hO hD a G hG K hK hz)
  exact ⟨hU,hAdj,hAdj.sub hU⟩

lemma integrable_physicalMixedFirst_density_pairs
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (J : Set R3) (hJ : IsCompact J) (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedFirstRaising hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedFirstAdjoint hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedFirstDefect hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ) := by
  have hs := contDiff_physicalMixedFirstFields hF hO hD g L lam h hg hh G hG
  have hS := contDiff_ambientSphereL2 H hH
  have hc := hasCompactSupport_ambientSphereL2 H hH J hJ hzH
  exact ⟨integrable_density_pair_of_contDiff g hg L lam _ _ hs.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.2 hS hc⟩

theorem compact_physicalMixedFirst_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedFirstRaising hF hO hD g L lam h G hG x,ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (lam,x) *
        ⟪ambientSphereL2 G hG x,physicalMixedFirstAdjoint hF hO hD g L lam h H hH x⟫_ℝ := by
  have hm : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (lam,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hc := contDiff_physicalMixedFirstCoefficient g hg L lam h hh
  have hLeft := (integrable_physicalMixedFirst_density_pairs hF hO hD g L lam h hg hh
    G H hG hH J hJ hzH).1
  have hRight : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪ambientSphereL2 G hG x,physicalMixedFirstAdjoint hF hO hD g L lam h H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using
      (integrable_physicalMixedFirst_density_pairs hF hO hD g L lam h hg hh
        H G hH hG K hK hzG).2.1
  exact compact_frameRaisingFirst_adjoint hF hO hD _ _
    (ambientSphereL2 G hG) (ambientSphereL2 H hH)
    (fun a => ambientRaisingField hF hO hD a G hG)
    (fun a => ambientDerivativeField hF hO hD a H hH)
    hm hc (contDiff_ambientSphereL2 G hG)
    (fun a => contDiff_ambientRaisingField hF hO hD a G hG)
    (fun a => contDiff_ambientDerivativeField hF hO hD a H hH)
    (hasCompactSupport_ambientSphereL2 G hG K hK hzG)
    (fun y => referenceDensityFamily_pos g hg L (lam,y))
    (fun a y => ambientRaisingField_graph hF hO hD a G hG y)
    (fun a y => ambientDerivativeField_graph hF hO hD a H hH y)

theorem integral_physicalMixedFirstDefect_quadratic_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (hg : IsAdmissibleMetric g) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedFirstDefect hF hO hD g L lam h G hG x,ambientSphereL2 G hG x⟫_ℝ) = 0 := by
  have hi := integrable_physicalMixedFirst_density_pairs hF hO hD g L lam h hg hh
    G G hG hG K hK hz
  have hAdj := compact_physicalMixedFirst_adjoint hF hO hD g L lam h hg hh
    G G hG hG K K hK hK hz hz
  have hEq : (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedFirstRaising hF hO hD g L lam h G hG x,ambientSphereL2 G hG x⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (lam,x) *
        ⟪physicalMixedFirstAdjoint hF hO hD g L lam h G hG x,ambientSphereL2 G hG x⟫_ℝ := by
    simpa only [real_inner_comm] using hAdj
  simp only [physicalMixedFirstDefect,inner_sub_left,mul_sub]
  rw [integral_sub hi.2.1 hi.1,hEq,sub_self]

theorem physicalMixedDensityCorrection_expansion (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (a : Fin 3) (x : R3) :
    physicalMixedDensityCorrection g L lam h a x =
      -∑ j : Fin 3, (directionalFDeriv (coordinateDirection j)
        (physicalMixedFirstCoefficient g L lam h a j) x +
          (referenceDensityFamily g L (lam,x))⁻¹ *
            directionalFDeriv (coordinateDirection j)
              (fun y => referenceDensityFamily g L (lam,y)) x *
                physicalMixedFirstCoefficient g L lam h a j x) := by
  have hm : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g L (lam,y)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hp : ∀ y : R3, referenceDensityFamily g L (lam,y) ≠ 0 :=
    fun y => (referenceDensityFamily_pos g hg L (lam,y)).ne'
  have hc : ∀ a j, ContDiff ℝ ∞ (physicalMixedFirstCoefficient g L lam h a j) :=
    contDiff_physicalMixedFirstCoefficient g hg L lam h hh
  unfold physicalMixedDensityCorrection frameDensityCorrection
  rw [Finset.mul_sum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hprod : directionalFDeriv (coordinateDirection j)
      (fun y => referenceDensityFamily g L (lam,y)*physicalMixedFirstCoefficient g L lam h a j y) x =
      directionalFDeriv (coordinateDirection j) (fun y => referenceDensityFamily g L (lam,y)) x *
        physicalMixedFirstCoefficient g L lam h a j x +
      referenceDensityFamily g L (lam,x) *
        directionalFDeriv (coordinateDirection j) (physicalMixedFirstCoefficient g L lam h a j) x := by
    simpa only [smul_eq_mul] using directionalFDeriv_smul (coordinateDirection j)
      (fun y => referenceDensityFamily g L (lam,y))
      (physicalMixedFirstCoefficient g L lam h a j) hm (hc a j) x
  rw [hprod]
  field_simp [hp x]
  ring

end OAI.AnisotropicCalderon.ActualPhysicalMixedFirst
