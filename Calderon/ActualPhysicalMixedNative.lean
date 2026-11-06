import Calderon.ActualReferenceDecomposition
import Calderon.ActualPhysicalMixedFirst
import Calderon.ActualPhysicalMixedProfile
import Calderon.ActualPhysicalMixedConnection

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualPhysicalMixedNative
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift SmoothSphereFields SmoothAngularApplication
  AmbientAngularShift SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising
  ActualReferenceDecomposition ActualHorizontalNormBridge ActualPrincipalErrorCoefficient
  ActualRawMixedPrincipalCollection ActualUnboundedFirstPrincipalFormBound
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection
  ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile

/- Genuine raw mixed perturbation on actual native all-mode fields.
   The graph-domain definition precedes its derived component decomposition.
   Full physical U/J/Gamma/E/F allocation remains a separate source obligation. -/

def physicalMixedFrameCoefficient (g : MatrixField) (L lam : ℝ) (h : MatrixField)
    (a b : Fin 3) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, h x i j * referenceCoFrameEntry g L i a (lam,x) *
    referenceCoFrameEntry g L j b (lam,x)

lemma contDiff_physicalMixedFrameCoefficient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (a b : Fin 3) : ContDiff ℝ ∞ (physicalMixedFrameCoefficient g L lam h a b) := by
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    ((hh i j).mul ((contDiff_referenceCoFrameEntry g hg L i a).comp
      (contDiff_const.prodMk contDiff_id))).mul
      ((contDiff_referenceCoFrameEntry g hg L j b).comp (contDiff_const.prodMk contDiff_id))

lemma referenceCoFrame_frameEntry_duality (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (j k : Fin 3) :
    (∑ b : Fin 3, referenceCoFrameEntry g L j b (lam,x) *
      referenceFrameEntryFamily g L b k (lam,x)) = if j = k then 1 else 0 := by
  have ht := congrArg (fun v : R3 => v k)
    (coordinateDirection_eq_sum_referenceGramFrame g hg L lam x j)
  change (∑ b : Fin 3, referenceCoFrameEntry g L j b (lam,x) *
    referenceMetricGramFrame g L (lam,x) b k) = _
  fin_cases j <;> fin_cases k <;>
    simpa [Fin.sum_univ_three,PiLp.smul_apply,coordinateDirection,Pi.single_apply] using ht.symm

lemma referenceCoFrame_frameDerivative_duality (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (f : R3 → ℝ) (x : R3) (j : Fin 3) :
    (∑ b : Fin 3, referenceCoFrameEntry g L j b (lam,x) *
      referenceFrameDerivative g L lam b f x) = directionalFDeriv (coordinateDirection j) f x := by
  have ht := congrArg (fun v : R3 => fderiv ℝ f x v)
    (coordinateDirection_eq_sum_referenceGramFrame g hg L lam x j)
  simpa only [map_sum,map_smul,smul_eq_mul,referenceFrameDerivative,directionalFDeriv] using ht.symm

lemma referenceCoFrame_connection_duality (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (j c d : Fin 3) :
    (∑ b : Fin 3, referenceCoFrameEntry g L j b (lam,x) *
      referenceConnectionEntry g L lam b c d x) =
      referenceFrameConnectionCoefficient g L lam x (coordinateDirection j) c d := by
  have ht := referenceFrameConnectionCoefficient_sum g L lam x
    (fun b => referenceCoFrameEntry g L j b (lam,x))
    (fun b => referenceMetricGramFrame g L (lam,x) b) c d
  rw [← coordinateDirection_eq_sum_referenceGramFrame g hg L lam x j] at ht
  exact ht.symm

lemma physicalMixedFrameCoefficient_contract (g : MatrixField) (L lam : ℝ)
    (h : MatrixField) (a : Fin 3) (F : Fin 3 → ℝ) (x : R3) :
    (∑ b : Fin 3, physicalMixedFrameCoefficient g L lam h a b x * F b) =
      ∑ i : Fin 3, ∑ j : Fin 3, h x i j * referenceCoFrameEntry g L i a (lam,x) *
        (∑ b : Fin 3, referenceCoFrameEntry g L j b (lam,x) * F b) := by
  simp only [physicalMixedFrameCoefficient,Fin.sum_univ_three]
  ring

lemma physicalMixedFrameCoefficient_first_contract (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (a j : Fin 3) (x : R3) :
    (∑ b : Fin 3, (2 * physicalMixedFrameCoefficient g L lam h a b x) *
      referenceFrameEntryFamily g L b j (lam,x)) = physicalMixedFirstCoefficient g L lam h a j x := by
  have ht : (∑ b : Fin 3, (2 * physicalMixedFrameCoefficient g L lam h a b x) *
      referenceFrameEntryFamily g L b j (lam,x)) =
      2 * (∑ b : Fin 3, physicalMixedFrameCoefficient g L lam h a b x *
        referenceFrameEntryFamily g L b j (lam,x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [ht,physicalMixedFrameCoefficient_contract]
  simp_rw [referenceCoFrame_frameEntry_duality g hg L lam x]
  simp [mul_ite,physicalMixedFirstCoefficient]

lemma physicalMixedFrameCoefficient_profile_contract (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (a : Fin 3) (x : R3) :
    (∑ b : Fin 3, (2 * physicalMixedFrameCoefficient g L lam h a b x) *
      referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x) =
      physicalMixedProfileCoefficient g L lam δ R p h a x := by
  have ht : (∑ b : Fin 3, (2 * physicalMixedFrameCoefficient g L lam h a b x) *
      referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x) =
      2 * (∑ b : Fin 3, physicalMixedFrameCoefficient g L lam h a b x *
        referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [ht,physicalMixedFrameCoefficient_contract]
  simp_rw [referenceCoFrame_frameDerivative_duality g hg L lam]
  rfl

lemma physicalMixedFrameCoefficient_connection_contract (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (h : MatrixField) (a c d : Fin 3) (x : R3) :
    (∑ b : Fin 3, physicalMixedFrameCoefficient g L lam h a b x *
      referenceConnectionEntry g L lam b c d x) = physicalMixedConnectionCoefficient g L lam h a c d x := by
  rw [physicalMixedFrameCoefficient_contract]
  simp_rw [referenceCoFrame_connection_duality g hg L lam x]
  rfl

def physicalMixedNativeRaising
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  ∑ a : Fin 3, ∑ b : Fin 3, (2 * physicalMixedFrameCoefficient g L lam h a b x) •
    normalizedRaising hF hO hD a
      (referenceWeightedBesselField hO hD g hg L lam 1 b
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x)

lemma physicalMixedNative_term_raising_graph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (a b : Fin 3) (x : R3) :
    (referenceWeightedInputField hO hD g hg L lam 1 b
      (fun y => Real.log (referenceRadius δ R p L y)) G hG x,
      normalizedRaising hF hO hD a
        (referenceWeightedBesselField hO hD g hg L lam 1 b
          (fun y => Real.log (referenceRadius δ R p L y)) G hG x)) ∈ sphereRaisingGraph hF hO hD a := normalizedRaising_graph hF hO hD a _ _
    (referenceWeightedBesselField_graph hO hD g hg L lam 1 b
      (fun y => Real.log (referenceRadius δ R p L y)) G hG x)

lemma physicalMixedNative_term_expansion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (a b : Fin 3) (x : R3) :
    normalizedRaising hF hO hD a
      (referenceWeightedBesselField hO hD g hg L lam 1 b
        (fun y => Real.log (referenceRadius δ R p L y)) G hG x) =
      (∑ j : Fin 3, referenceFrameEntryFamily g L b j (lam,x) •
        directionalFDeriv (coordinateDirection j) (ambientRaisingField hF hO hD a G hG) x) +
      (1/2 : ℝ) • ∑ c : Fin 3, ∑ d : Fin 3, referenceConnectionEntry g L lam b c d x •
        ambientMixedRaisingRotationField hF hO hD a c d G hG x +
      referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x •
        ambientMixedRaisingDegreeField hF hO hD a G hG x := by
  have hfixed (j : Fin 3) :
      directionalFDeriv (coordinateDirection j) (ambientRaisingField hF hO hD a G hG) x =
        normalizedRaising hF hO hD a
          (directionalFDeriv (coordinateDirection j)
            (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
    change directionalFDeriv (coordinateDirection j)
      (fun y => normalizedRaising hF hO hD a
        (ambientBesselField hO hD 1 (by norm_num) G hG y)) x = _
    exact directionalFDeriv_fixed_map _ _
      (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG) _ _
  simp only [referenceWeightedBesselField,one_smul,referenceHorizontalBesselField_expansion,
    referenceRotationBesselField,map_add,map_smul,map_sum]
  simp_rw [hfixed]
  rfl

theorem physicalMixedNativeRaising_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG x =
      physicalMixedFirstRaising hF hO hD g L lam h G hG x + physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x +
      physicalMixedConnectionRaising hF hO hD g L lam h G hG x := by
  have hbase :
      (∑ a : Fin 3, ∑ b : Fin 3, (2 * physicalMixedFrameCoefficient g L lam h a b x) •
        (∑ j : Fin 3, referenceFrameEntryFamily g L b j (lam,x) •
          directionalFDeriv (coordinateDirection j) (ambientRaisingField hF hO hD a G hG) x)) =
        physicalMixedFirstRaising hF hO hD g L lam h G hG x := by
    unfold physicalMixedFirstRaising frameRaisingFirst
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul,physicalMixedFrameCoefficient_first_contract g hg L lam]
  have hprofile :
      (∑ a : Fin 3, ∑ b : Fin 3, (2 * physicalMixedFrameCoefficient g L lam h a b x) •
        (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x •
          ambientMixedRaisingDegreeField hF hO hD a G hG x)) =
        physicalMixedProfileRaising hF hO hD g L lam δ R p h G hG x := by
    unfold physicalMixedProfileRaising
    simp only [smul_smul]
    simp_rw [← Finset.sum_smul,physicalMixedFrameCoefficient_profile_contract g hg L lam]
  have hconnection :
      (∑ a : Fin 3, ∑ b : Fin 3, (2 * physicalMixedFrameCoefficient g L lam h a b x) •
        ((1/2 : ℝ) • ∑ c : Fin 3, ∑ d : Fin 3, referenceConnectionEntry g L lam b c d x •
          ambientMixedRaisingRotationField hF hO hD a c d G hG x)) =
        physicalMixedConnectionRaising hF hO hD g L lam h G hG x := by
    have hhalf (v : ℝ) (z : SphereL2) : (2*v) • ((1/2 : ℝ) • z) = v • z := by
      rw [smul_smul]
      congr 1
      ring
    simp_rw [hhalf]
    unfold physicalMixedConnectionRaising
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul,physicalMixedFrameCoefficient_connection_contract g hg L lam]
  unfold physicalMixedNativeRaising
  simp_rw [physicalMixedNative_term_expansion hF hO hD g hg L lam δ R p h G hG]
  simp only [smul_add,Finset.sum_add_distrib]
  rw [hbase,hconnection,hprofile]
  abel

def physicalMixedNativeAdjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  frameRaisingFirstAdjoint (fun y => referenceDensityFamily g L (lam,y))
    (physicalMixedFirstCoefficient g L lam h)
    (fun a => ambientDerivativeField hF hO hD a G hG) x +
    (∑ a : Fin 3, physicalMixedProfileCoefficient g L lam δ R p h a x •
      ambientMixedDegreeDerivativeField hF hO hD a G hG x) +
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (-physicalMixedConnectionCoefficient g L lam h a b c x) •
      ambientMixedRotatedDerivativeField hF hO hD a b c G hG x

theorem physicalMixedNativeAdjoint_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalMixedNativeAdjoint hF hO hD g hg L lam δ R p h G hG x =
      physicalMixedFirstAdjoint hF hO hD g L lam h G hG x + physicalMixedProfileAdjoint hF hO hD g L lam δ R p h G hG x +
      physicalMixedConnectionAdjoint hF hO hD g L lam h G hG x := rfl

def physicalMixedNativeDefect
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  physicalMixedNativeAdjoint hF hO hD g hg L lam δ R p h G hG x - physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG x

theorem physicalMixedNativeDefect_decomposition
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    physicalMixedNativeDefect hF hO hD g hg L lam δ R p h G hG x =
      physicalMixedFirstDefect hF hO hD g L lam h G hG x +
      physicalMixedProfileDefect hF hO hD g L lam δ R p h G hG x +
      physicalMixedConnectionDefect hF hO hD g L lam h G hG x := by
  rw [physicalMixedNativeDefect,physicalMixedNativeAdjoint_decomposition,
    physicalMixedNativeRaising_decomposition]
  simp only [physicalMixedFirstDefect,physicalMixedProfileDefect,physicalMixedConnectionDefect]
  abel

lemma contDiff_physicalMixedNativeFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG) ∧
    ContDiff ℝ ∞ (physicalMixedNativeAdjoint hF hO hD g hg L lam δ R p h G hG) ∧
    ContDiff ℝ ∞ (physicalMixedNativeDefect hF hO hD g hg L lam δ R p h G hG) := by
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have hU : ContDiff ℝ ∞ (physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG) :=
    ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
      (contDiff_const.mul (contDiff_physicalMixedFrameCoefficient g hg L lam h hh a b)).smul
        ((normalizedRaising hF hO hD a).contDiff.comp
          (contDiff_referenceWeightedBesselField hO hD g hg L lam 1 b
            (fun y => Real.log (referenceRadius δ R p L y)) hf G hG))
  have hFirst := contDiff_physicalMixedFirstFields hF hO hD g L lam h hg hh G hG
  have hProfile := contDiff_physicalMixedProfileFields hF hO hD g L lam δ R p h hg hδ hR hh G hG
  have hConnection := contDiff_physicalMixedConnectionFields hF hO hD g L lam h hg hh G hG
  have hAdj : ContDiff ℝ ∞ (physicalMixedNativeAdjoint hF hO hD g hg L lam δ R p h G hG) :=
    (hFirst.2.1.add hProfile.2.1).add hConnection.2.1
  exact ⟨hU,hAdj,hAdj.sub hU⟩

lemma hasCompactSupport_physicalMixedNativeFields
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG) ∧
    HasCompactSupport (physicalMixedNativeAdjoint hF hO hD g hg L lam δ R p h G hG) ∧
    HasCompactSupport (physicalMixedNativeDefect hF hO hD g hg L lam δ R p h G hG) := by
  have hU : HasCompactSupport (physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG) :=
    HasCompactSupport.intro hK (by
      intro x hx
      simp only [physicalMixedNativeRaising,
        referenceWeightedBesselField_eq_zero hO hD g hg L lam 1 _
          (fun y => Real.log (referenceRadius δ R p L y)) G hG K hK hz x hx,
        map_zero,smul_zero,Finset.sum_const_zero])
  have hFirst := hasCompactSupport_physicalMixedFirstFields hF hO hD g L lam h G hG K hK hz
  have hProfile := hasCompactSupport_physicalMixedProfileFields hF hO hD g L lam δ R p h G hG K hK hz
  have hConnection := hasCompactSupport_physicalMixedConnectionFields hF hO hD g L lam h G hG K hK hz
  have hAdj : HasCompactSupport (physicalMixedNativeAdjoint hF hO hD g hg L lam δ R p h G hG) :=
    (hFirst.2.1.add hProfile.2.1).add hConnection.2.1
  exact ⟨hU,hAdj,hAdj.sub hU⟩

lemma integrable_physicalMixedNative_density_pairs
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (J : Set R3) (hJ : IsCompact J) (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedNativeAdjoint hF hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedNativeDefect hF hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) := by
  have hs := contDiff_physicalMixedNativeFields hF hO hD g hg L lam δ R p h hδ hR hh G hG
  have hS := contDiff_ambientSphereL2 H hH
  have hc := hasCompactSupport_ambientSphereL2 H hH J hJ hzH
  exact ⟨integrable_density_pair_of_contDiff g hg L lam _ _ hs.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.1 hS hc,
    integrable_density_pair_of_contDiff g hg L lam _ _ hs.2.2 hS hc⟩

theorem compact_physicalMixedNative_adjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G H : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J)
    (hzG : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0)
    (hzH : ∀ x ∉ J, ∀ theta : UnitSphere, H (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG x,ambientSphereL2 H hH x⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (lam,x) *
        ⟪ambientSphereL2 G hG x,physicalMixedNativeAdjoint hF hO hD g hg L lam δ R p h H hH x⟫_ℝ := by
  have iFirst := integrable_physicalMixedFirst_density_pairs hF hO hD g L lam h hg hh G H hG hH J hJ hzH
  have iProfile := integrable_physicalMixedProfile_density_pairs hF hO hD g L lam δ R p h hg hδ hR hh G H hG hH J hJ hzH
  have iConnection := integrable_physicalMixedConnection_density_pairs hF hO hD g L lam h hg hh G H hG hH J hJ hzH
  have rFirst : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪ambientSphereL2 G hG x,physicalMixedFirstAdjoint hF hO hD g L lam h H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using
      (integrable_physicalMixedFirst_density_pairs hF hO hD g L lam h hg hh H G hH hG K hK hzG).2.1
  have rProfile : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪ambientSphereL2 G hG x,physicalMixedProfileAdjoint hF hO hD g L lam δ R p h H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using
      (integrable_physicalMixedProfile_density_pairs hF hO hD g L lam δ R p h hg hδ hR hh H G hH hG K hK hzG).2.1
  have rConnection : Integrable (fun x => referenceDensityFamily g L (lam,x) *
      ⟪ambientSphereL2 G hG x,physicalMixedConnectionAdjoint hF hO hD g L lam h H hH x⟫_ℝ) := by
    simpa only [real_inner_comm] using
      (integrable_physicalMixedConnection_density_pairs hF hO hD g L lam h hg hh H G hH hG K hK hzG).2.1
  simp only [physicalMixedNativeRaising_decomposition,physicalMixedNativeAdjoint_decomposition,
    inner_add_left,inner_add_right,mul_add]
  have hsum (f0 f1 f2 : R3 → ℝ)
      (i0 : Integrable f0) (i1 : Integrable f1) (i2 : Integrable f2) :
      (∫ x, f0 x + f1 x + f2 x) = (∫ x, f0 x) + (∫ x, f1 x) + (∫ x, f2 x) := by
    have h01 : (∫ x, f0 x + f1 x) = (∫ x, f0 x) + (∫ x, f1 x) := by
      simpa only [Pi.add_apply] using integral_add i0 i1
    have h012 : (∫ x, f0 x + f1 x + f2 x) =
        (∫ x, f0 x + f1 x) + (∫ x, f2 x) := by
      simpa only [Pi.add_apply] using integral_add (i0.add i1) i2
    exact h012.trans (congrArg (fun z : ℝ => z + (∫ x, f2 x)) h01)
  rw [hsum _ _ _ iFirst.1 iProfile.1 iConnection.1,
    hsum _ _ _ rFirst rProfile rConnection,
    compact_physicalMixedFirst_adjoint hF hO hD g L lam h hg hh G H hG hH K J hK hJ hzG hzH,
    compact_physicalMixedProfile_adjoint hF hO hD g L lam δ R p h hg hδ hR hh G H hG hH K J hK hJ hzG hzH,
    compact_physicalMixedConnection_adjoint hF hO hD g L lam h hg hh G H hG hH K J hK hJ hzG hzH]

theorem integral_physicalMixedNativeDefect_quadratic_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedNativeDefect hF hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ) = 0 := by
  have hi := integrable_physicalMixedNative_density_pairs hF hO hD g hg L lam δ R p h hδ hR hh
    G G hG hG K hK hz
  have hAdj := compact_physicalMixedNative_adjoint hF hO hD g hg L lam δ R p h hδ hR hh
    G G hG hG K K hK hK hz hz
  have hEq : (∫ x, referenceDensityFamily g L (lam,x) *
      ⟪physicalMixedNativeRaising hF hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ) =
      ∫ x, referenceDensityFamily g L (lam,x) *
        ⟪physicalMixedNativeAdjoint hF hO hD g hg L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ := by
    simpa only [real_inner_comm] using hAdj
  simp only [physicalMixedNativeDefect,inner_sub_left,mul_sub]
  rw [integral_sub hi.2.1 hi.1,hEq,sub_self]

end OAI.AnisotropicCalderon.ActualPhysicalMixedNative
