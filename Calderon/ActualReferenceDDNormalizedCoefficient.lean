import Calderon.ActualReferenceOrdinaryPrincipal

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualReferenceDDNormalizedCoefficient
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  SmoothAmbientAngularCasimir AmbientAngularShift SmoothMetricFrame MovingFrameConnection
  AmbientReferenceRaising AmbientReferenceCovariantCore ActualReferenceParallelRaising
  ActualReferenceScaledRaisingTransport ActualReferenceModelTrace ActualReferenceDecomposition
  ActualReferenceOrdinaryPrincipal ActualPhysicalPureAngular ActualPhysicalPureReferenceCancellation
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedNative ActualPhysicalMixedFirst
  ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualHorizontalNormBridge
  ActualNormalizedSphereRotation ActualUnboundedFirstPrincipalFormBound
  ReferenceDensityBounds WeightedBaseSpectral MetricOperator ActualScalarPrincipalAdjoint
  ScalarBaseAdjoint PrincipalCommutator ConformalDepth RadiusProfile

/- Independent actual DD order-normalized coefficient bodies, connected to genuine
   native first/zero fields only on proved W1/W2/derivative graph outputs.
   Compact support and actual density L2 paid. Full U/E/F/H and uniform weighted jets remain separate. -/

lemma norm_inverseDegreeMultiplier_le_one
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) : ‖inverseDegreeMultiplier hO hD‖ ≤ 1 := by
  exact norm_boundedSpectralMultiplier_le hO hD inverseDegreeWeight 1 (by norm_num)
    abs_inverseDegreeWeight_le_one

lemma inverseDegreeMultiplier_ambientBesselField_one
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    inverseDegreeMultiplier hO hD (ambientBesselField hO hD 1 (by norm_num) G hG x) = ambientSphereL2 G hG x := by
  exact inverseDegreeMultiplier_of_besselGraph hO hD _ _
    (ambientBesselField_graph hO hD 1 (by norm_num) G hG x)

lemma inverseDegreeMultiplier_ambientBesselField_two
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    inverseDegreeMultiplier hO hD (ambientBesselField hO hD 2 (by norm_num) G hG x) =
      ambientBesselField hO hD 1 (by norm_num) G hG x := by
  exact inverseDegreeMultiplier_of_besselGraph hO hD _ _
    (ambientBesselField_one_two_graph hO hD G hG x)

lemma inverseDegreeMultiplier_directional_ambientBesselField_one
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    inverseDegreeMultiplier hO hD
      (directionalFDeriv X (ambientBesselField hO hD 1 (by norm_num) G hG) x) =
      directionalFDeriv X (ambientSphereL2 G hG) x := by
  exact inverseDegreeMultiplier_of_besselGraph hO hD _ _
    (SectionFiveErrorForms.directionalDeriv_besselGraph hO hD 1 X
      (ambientSphereL2 G hG) (ambientBesselField hO hD 1 (by norm_num) G hG)
      (contDiff_ambientSphereL2 G hG) (contDiff_ambientBesselField hO hD 1 (by norm_num) G hG)
      (ambientBesselField_graph hO hD 1 (by norm_num) G hG) x)

def referenceWeightedZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a) +
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
      (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD)

lemma referenceWeightedZeroBaseNormalizedCoefficient_apply_one
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a x
      (ambientBesselField hO hD 1 (by norm_num) G hG x) =
      referenceWeightedZeroBaseField hO hD g hg L lam δ R p a G hG x := by
  unfold referenceWeightedZeroBaseNormalizedCoefficient referenceWeightedZeroBaseField
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply]
  rw [inverseDegreeMultiplier_ambientBesselField_one hO hD G hG x]

lemma referenceWeightedZeroBaseNormalizedCoefficient_apply_two
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a x
      (ambientBesselField hO hD 2 (by norm_num) G hG x) =
      referenceWeightedZeroBaseBesselField hO hD g hg L lam δ R p a G hG x := by
  unfold referenceWeightedZeroBaseNormalizedCoefficient referenceWeightedZeroBaseBesselField
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply]
  rw [inverseDegreeMultiplier_ambientBesselField_two hO hD G hG x]

def referenceWeightedFirstBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g L lam h a b x •
      ((-(referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
          (referenceMetricGramFrame g L (lam,x) b)) j) • inverseDegreeMultiplier hO hD +
       referenceMetricGramFrame g L (lam,x) a j •
         normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) b) +
       referenceMetricGramFrame g L (lam,x) b j •
         normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a) +
       (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x *
           referenceMetricGramFrame g L (lam,x) a j +
         referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x *
           referenceMetricGramFrame g L (lam,x) b j) •
         (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD))

def referenceCovectorZeroBaseNormalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  (directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
    (fun y => normalizedReferenceAngularConnection hO hD g L lam y
      (referenceMetricGramFrame g L (lam,y) b)) x).comp (inverseDegreeMultiplier hO hD) +
  directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
    (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x •
      (inverseDegreeMultiplier hO hD - (inverseDegreeMultiplier hO hD).comp (inverseDegreeMultiplier hO hD)) +
  (normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)).comp
    (referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p b x) -
  ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x
    (referenceMetricGramFrame g L (lam,x) a) c b •
    (referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p c x).comp
      (inverseDegreeMultiplier hO hD) +
  referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
    (referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p b x -
      (referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p b x).comp
        (inverseDegreeMultiplier hO hD))

def referenceWeightedZeroBaseNormalizedCoefficientTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  referenceRadius δ R p L x • ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g L lam h a b x •
      referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b x

theorem referenceWeightedFirstBaseTrace_eq_normalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x =
      ∑ j : Fin 3, referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
  have hInv (j : Fin 3) := inverseDegreeMultiplier_directional_ambientBesselField_one hO hD G hG x (coordinateDirection j)
  have hphi (X : R3) : directionalFDeriv X (ambientSphereL2 G hG) x =
      ∑ j : Fin 3, X j • directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x := by
    simpa only [directionalFDeriv] using fderiv_apply_eq_coordinate_sum (ambientSphereL2 G hG) x X
  have hB1 (X : R3) : directionalFDeriv X (ambientBesselField hO hD 1 (by norm_num) G hG) x =
      ∑ j : Fin 3, X j • directionalFDeriv (coordinateDirection j)
        (ambientBesselField hO hD 1 (by norm_num) G hG) x := by
    simpa only [directionalFDeriv] using fderiv_apply_eq_coordinate_sum
      (ambientBesselField hO hD 1 (by norm_num) G hG) x X
  have hTerm (a b : Fin 3) : referenceCovectorFirstBaseField hO hD g hg L lam δ R p a b G hG x =
      ∑ j : Fin 3,
      ((-(referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
          (referenceMetricGramFrame g L (lam,x) b)) j) • inverseDegreeMultiplier hO hD +
       referenceMetricGramFrame g L (lam,x) a j •
         normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) b) +
       referenceMetricGramFrame g L (lam,x) b j •
         normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a) +
       (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x *
           referenceMetricGramFrame g L (lam,x) a j +
         referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x *
           referenceMetricGramFrame g L (lam,x) b j) •
         (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD))
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x) := by
    unfold referenceCovectorFirstBaseField
    rw [hphi (-(referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
      (referenceMetricGramFrame g L (lam,x) b))),
      hB1 (referenceMetricGramFrame g L (lam,x) a),hB1 (referenceMetricGramFrame g L (lam,x) b),
      hphi (referenceMetricGramFrame g L (lam,x) a),hphi (referenceMetricGramFrame g L (lam,x) b)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply]
    simp_rw [hInv]
    have hNegGamma (j : Fin 3) :
        (-(referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
          (referenceMetricGramFrame g L (lam,x) b))) j =
        -(referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a)
          (referenceMetricGramFrame g L (lam,x) b) j) := rfl
    simp_rw [hNegGamma]
    simp only [map_sum,map_add,map_smul,Fin.sum_univ_three,smul_add,smul_sub,smul_smul]
    module
  unfold referenceWeightedFirstBaseTrace referenceWeightedFirstBaseNormalizedCoefficient
  simp_rw [hTerm]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,Finset.smul_sum]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

lemma referenceCovectorZeroBaseNormalizedCoefficient_apply_two
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b x
      (ambientBesselField hO hD 2 (by norm_num) G hG x) =
      referenceCovectorZeroBaseField hO hD g hg L lam δ R p a b G hG x := by
  unfold referenceCovectorZeroBaseNormalizedCoefficient
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  simp_rw [inverseDegreeMultiplier_ambientBesselField_two hO hD G hG x,
    inverseDegreeMultiplier_ambientBesselField_one hO hD G hG x,
    referenceWeightedZeroBaseNormalizedCoefficient_apply_two hO hD g hg L lam δ R p _ G hG x,
    referenceWeightedZeroBaseNormalizedCoefficient_apply_one hO hD g hg L lam δ R p _ G hG x]
  rfl

theorem referenceWeightedZeroBaseTrace_eq_normalizedCoefficient
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x =
      referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x
        (ambientBesselField hO hD 2 (by norm_num) G hG x) := by
  unfold referenceWeightedZeroBaseNormalizedCoefficientTrace
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]
  simp_rw [referenceCovectorZeroBaseNormalizedCoefficient_apply_two hO hD g hg L lam δ R p _ _ G hG x]
  rfl

lemma norm_referenceWeightedFirstBaseTrace_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x‖ ≤
      ∑ j : Fin 3, ‖referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x‖ *
        ‖directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD 1 (by norm_num) G hG) x‖ := by
  rw [referenceWeightedFirstBaseTrace_eq_normalizedCoefficient hO hD g hg L lam δ R p h G hG x]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
    (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x).le_opNorm _)

lemma norm_referenceWeightedZeroBaseTrace_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ‖referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x‖ ≤
      ‖referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x‖ *
        ‖ambientBesselField hO hD 2 (by norm_num) G hG x‖ := by
  rw [referenceWeightedZeroBaseTrace_eq_normalizedCoefficient hO hD g hg L lam δ R p h G hG x]
  exact (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x).le_opNorm _

lemma ambientSphereL2_directionalFDeriv_eq_zero_outside
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) (X : R3) :
    directionalFDeriv X (ambientSphereL2 G hG) x = 0 := by
  have he : ambientSphereL2 G hG =ᶠ[𝓝 x] (fun _ : R3 => (0 : SphereL2)) := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact ambientSphereL2_eq_zero G hG y (hz y hy)
  unfold directionalFDeriv
  rw [he.fderiv_eq]
  simp

lemma ambientBesselField_directionalFDeriv_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) (X : R3) :
    directionalFDeriv X (ambientBesselField hO hD s hs G hG) x = 0 := by
  have he : ambientBesselField hO hD s hs G hG =ᶠ[𝓝 x] (fun _ : R3 => (0 : SphereL2)) := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact ambientBesselField_eq_zero hO hD s hs G hG K hz y hy
  unfold directionalFDeriv
  rw [he.fderiv_eq]
  simp

lemma referenceWeightedZeroBaseField_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceWeightedZeroBaseField hO hD g hg L lam δ R p a G hG x = 0 := by
  unfold referenceWeightedZeroBaseField
  simp only [ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
    ambientBesselField_eq_zero hO hD 2 (by norm_num) G hG K hz x hx,
    ambientSphereL2_eq_zero G hG x (hz x hx),map_zero,sub_self,smul_zero,zero_add]

lemma referenceWeightedZeroBaseBesselField_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceWeightedZeroBaseBesselField hO hD g hg L lam δ R p a G hG x = 0 := by
  unfold referenceWeightedZeroBaseBesselField
  simp only [ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
    ambientBesselField_eq_zero hO hD 2 (by norm_num) G hG K hz x hx,
    ambientSphereL2_eq_zero G hG x (hz x hx),map_zero,sub_self,smul_zero,zero_add]

lemma referenceCovectorFirstBaseField_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceCovectorFirstBaseField hO hD g hg L lam δ R p a b G hG x = 0 := by
  unfold referenceCovectorFirstBaseField
  simp_rw [ambientSphereL2_directionalFDeriv_eq_zero_outside G hG K hK hz x hx,
    ambientBesselField_directionalFDeriv_eq_zero_outside hO hD 1 (by norm_num) G hG K hK hz x hx]
  simp only [map_zero,sub_self,smul_zero,zero_add]

lemma referenceCovectorZeroBaseField_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (a b : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceCovectorZeroBaseField hO hD g hg L lam δ R p a b G hG x = 0 := by
  unfold referenceCovectorZeroBaseField
  simp_rw [referenceWeightedZeroBaseField_eq_zero_outside hO hD g hg L lam δ R p _ G hG K hK hz x hx,
    referenceWeightedZeroBaseBesselField_eq_zero_outside hO hD g hg L lam δ R p _ G hG K hK hz x hx]
  simp only [ambientBesselField_eq_zero hO hD 1 (by norm_num) G hG K hz x hx,
    ambientSphereL2_eq_zero G hG x (hz x hx),map_zero,sub_self,smul_zero,
    Finset.sum_const_zero,add_zero,sub_zero]

lemma referenceWeightedFirstBaseTrace_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG x = 0 := by
  unfold referenceWeightedFirstBaseTrace
  simp_rw [referenceCovectorFirstBaseField_eq_zero_outside hO hD g hg L lam δ R p _ _ G hG K hK hz x hx]
  simp only [smul_zero,Finset.sum_const_zero]

lemma hasCompactSupport_referenceWeightedFirstBaseTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG) := by
  exact HasCompactSupport.intro hK
    (fun x hx => referenceWeightedFirstBaseTrace_eq_zero_outside hO hD g hg L lam δ R p h G hG K hK hz x hx)

lemma memLp_referenceWeightedFirstBaseTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    MemLp (referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG) 2 (referenceBaseMeasure g L lam) := by
  exact memLp_referenceBase g hg L lam _
    (contDiff_referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p hδ hR h hh G hG).continuous
    (hasCompactSupport_referenceWeightedFirstBaseTrace hO hD g hg L lam δ R p h G hG K hK hz)

lemma referenceWeightedZeroBaseTrace_eq_zero_outside
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (x : R3) (hx : x ∉ K) :
    referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG x = 0 := by
  unfold referenceWeightedZeroBaseTrace
  simp_rw [referenceCovectorZeroBaseField_eq_zero_outside hO hD g hg L lam δ R p _ _ G hG K hK hz x hx]
  simp only [smul_zero,Finset.sum_const_zero]

lemma hasCompactSupport_referenceWeightedZeroBaseTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG) := by
  exact HasCompactSupport.intro hK
    (fun x hx => referenceWeightedZeroBaseTrace_eq_zero_outside hO hD g hg L lam δ R p h G hG K hK hz x hx)

lemma memLp_referenceWeightedZeroBaseTrace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    MemLp (referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG) 2 (referenceBaseMeasure g L lam) := by
  exact memLp_referenceBase g hg L lam _
    (contDiff_referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p hδ hR h hh G hG).continuous
    (hasCompactSupport_referenceWeightedZeroBaseTrace hO hD g hg L lam δ R p h G hG K hK hz)

end OAI.AnisotropicCalderon.ActualReferenceDDNormalizedCoefficient
