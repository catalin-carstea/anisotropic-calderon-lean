import Calderon.NormalizedPrincipalMetricSmooth
import Calderon.MetricLocalDivergence
import Calderon.ActualReferenceDDHigherGeometryJets

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondMetricDrift
open MetricVolume MetricOperator ConnectionError AngularPolynomial RadiusProfile
  ConformalDepth ReferenceDensityBounds NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ActualHorizontalNormBridge ActualReferenceDDHigherGeometryJets PrincipalCommutator
  EnergyBridge SmoothMetricFrame

def normalizedSecondLaplacianScalarJoint (g1 g2 : MatrixField) (L : ℝ) (z : ℝ × R3) : ℝ :=
  3 / referenceNormalizationTraceFamily g1 g2 L z

def normalizedSecondDriftCoordinateJoint (g1 g2 : MatrixField) (L : ℝ) (k : Fin 3) (z : ℝ × R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    referenceNormalizedPrincipalMatrix g1 g2 L z.1 z.2 i j *
      (referenceConnectionFamily g1 L z (coordinateDirection i) (coordinateDirection j) k -
        referenceConnectionFamily g2 0 z (coordinateDirection i) (coordinateDirection j) k)

def normalizedSecondDriftFrameJoint (g1 g2 : MatrixField) (L : ℝ) (a : Fin 3) (z : ℝ × R3) : ℝ :=
  ∑ k : Fin 3, referenceCoFrameEntry g1 L k a z *
    normalizedSecondDriftCoordinateJoint g1 g2 L k z

def normalizedSecondLaplacian (g1 g2 : MatrixField) (L lam : ℝ) (u : R3 → ℝ) (x : R3) : ℝ :=
  normalizedSecondLaplacianScalarJoint g1 g2 L (lam,x) *
    (vol (dilatedMetric g2 lam) x)⁻¹ *
      AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
        (vol (dilatedMetric g2 lam))
        (fun y => MetricOperator.matrixOperatorMap ((dilatedMetric g2 lam y)⁻¹)
          (gradient u y)) x

lemma referenceMetric_zero_eq (g : MatrixField) : referenceMetric g 0 = g :=
by
  funext x
  simp only [referenceMetric, EnergyBridge.conformalMatrix, zero_mul, mul_zero, neg_zero,
    Real.exp_zero, one_smul]

lemma referenceConnection_zero_eq (g : MatrixField) (lam : ℝ) (x : R3) :
  referenceConnectionFamily g 0 (lam,x) =
    ConnectionError.coordinateConnectionField
      (inverseMetricOperator (dilatedMetric g lam))
      (MetricOperator.metricOperatorField (dilatedMetric g lam)) x :=
by
  unfold referenceConnectionFamily
  rw [referenceMetric_zero_eq]

lemma normalizedSecondLaplacianScalarJoint_pos (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (z : ℝ × R3) :
  0 < normalizedSecondLaplacianScalarJoint g1 g2 L z :=
by
  unfold normalizedSecondLaplacianScalarJoint
  exact div_pos (by norm_num)
    (referenceNormalizationTraceFamily_pos g1 g2 hg1 hg2 L z)

theorem normalizedSecondLaplacian_eq_hessian_trace (g1 g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (L lam : ℝ) (u : R3 → ℝ)
    (hu : ContDiff ℝ ∞ u) (x : R3) :
  normalizedSecondLaplacian g1 g2 L lam u x =
    normalizedSecondLaplacianScalarJoint g1 g2 L (lam,x) *
      ∑ i : Fin 3, ∑ j : Fin 3, (dilatedMetric g2 lam x)⁻¹ i j *
        RadiusProfile.coordinateHessian u
          (fun X Y => referenceConnectionFamily g2 0 (lam,x) X Y)
          x (coordinateDirection i) (coordinateDirection j) :=
by
  have hentry : ∀ i j, DifferentiableAt ℝ
      (fun y => dilatedMetric g2 lam y i j) x :=
    fun i j => (dilatedMetric_smooth_entries g2 hg2 lam i j).differentiable (by simp) x
  have hpos : (dilatedMetric g2 lam x).PosDef := dilatedMetric_posDef g2 hg2 lam x
  have hsym : ∀ᶠ y in 𝓝 x, (dilatedMetric g2 lam y).IsHermitian :=
    Filter.Eventually.of_forall (fun y => (dilatedMetric_posDef g2 hg2 lam y).isHermitian)
  have hsecond : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hd := densityWeightedDivergence_eq_metricHessian_trace_local
    (dilatedMetric g2 lam) u x hentry hpos hsym hsecond
  have hd' : AngularPolynomial.densityWeightedDivergence
      (EuclideanSpace.basisFun (Fin 3) ℝ) (vol (dilatedMetric g2 lam))
      (fun y => MetricOperator.matrixOperatorMap ((dilatedMetric g2 lam y)⁻¹)
        (gradient u y)) x =
      vol (dilatedMetric g2 lam) x *
        ∑ i : Fin 3, ∑ j : Fin 3, (dilatedMetric g2 lam x)⁻¹ i j *
          RadiusProfile.coordinateHessian u
            (fun X Y => referenceConnectionFamily g2 0 (lam,x) X Y)
            x (coordinateDirection i) (coordinateDirection j) := by
    simpa only [referenceConnection_zero_eq, inverseMetricOperator,
      coordinateDirection, coordinateVector] using hd
  have hv : vol (dilatedMetric g2 lam) x ≠ 0 :=
    (vol_pos_of_posDef _ (dilatedMetric_posDef g2 hg2 lam) x).ne'
  unfold normalizedSecondLaplacian
  rw [hd']
  calc
    _ = normalizedSecondLaplacianScalarJoint g1 g2 L (lam,x) *
        ((vol (dilatedMetric g2 lam) x)⁻¹ * vol (dilatedMetric g2 lam) x) *
        (∑ i : Fin 3, ∑ j : Fin 3, (dilatedMetric g2 lam x)⁻¹ i j *
          RadiusProfile.coordinateHessian u
            (fun X Y => referenceConnectionFamily g2 0 (lam,x) X Y)
            x (coordinateDirection i) (coordinateDirection j)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hv, mul_one]

theorem normalizedSecondLaplacian_eq_reference_hessian_and_drift (g1 g2 : MatrixField)
    (hg2 : IsAdmissibleMetric g2) (L lam : ℝ) (u : R3 → ℝ)
    (hu : ContDiff ℝ ∞ u) (x : R3) :
  normalizedSecondLaplacian g1 g2 L lam u x =
    (∑ i : Fin 3, ∑ j : Fin 3,
      referenceNormalizedPrincipalMatrix g1 g2 L lam x i j *
        RadiusProfile.coordinateHessian u
          (fun X Y => referenceConnectionFamily g1 L (lam,x) X Y)
          x (coordinateDirection i) (coordinateDirection j)) +
    ∑ k : Fin 3, normalizedSecondDriftCoordinateJoint g1 g2 L k (lam,x) *
      directionalFDeriv (coordinateDirection k) u x :=
by
  classical
  have hQ (i j : Fin 3) : referenceNormalizedPrincipalMatrix g1 g2 L lam x i j =
      normalizedSecondLaplacianScalarJoint g1 g2 L (lam,x) *
        (dilatedMetric g2 lam x)⁻¹ i j := rfl
  have hH (i j : Fin 3) :
      RadiusProfile.coordinateHessian u
        (fun X Y => referenceConnectionFamily g2 0 (lam,x) X Y)
        x (coordinateDirection i) (coordinateDirection j) =
      RadiusProfile.coordinateHessian u
        (fun X Y => referenceConnectionFamily g1 L (lam,x) X Y)
        x (coordinateDirection i) (coordinateDirection j) +
      ∑ k : Fin 3,
        (referenceConnectionFamily g1 L (lam,x) (coordinateDirection i) (coordinateDirection j) k -
          referenceConnectionFamily g2 0 (lam,x) (coordinateDirection i) (coordinateDirection j) k) *
          directionalFDeriv (coordinateDirection k) u x := by
    unfold RadiusProfile.coordinateHessian
    rw [covector_coordinate_sum (fderiv ℝ u x)
        (referenceConnectionFamily g2 0 (lam,x) (coordinateDirection i) (coordinateDirection j)),
      covector_coordinate_sum (fderiv ℝ u x)
        (referenceConnectionFamily g1 L (lam,x) (coordinateDirection i) (coordinateDirection j))]
    simp only [directionalFDeriv, coordinateDirection, coordinateVector,
      sub_mul, Finset.sum_sub_distrib]
    ring
  rw [normalizedSecondLaplacian_eq_hessian_trace g1 g2 hg2 L lam u hu x]
  have hprincipal :
      normalizedSecondLaplacianScalarJoint g1 g2 L (lam,x) *
        (∑ i : Fin 3, ∑ j : Fin 3, (dilatedMetric g2 lam x)⁻¹ i j *
          RadiusProfile.coordinateHessian u
            (fun X Y => referenceConnectionFamily g2 0 (lam,x) X Y)
            x (coordinateDirection i) (coordinateDirection j)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        referenceNormalizedPrincipalMatrix g1 g2 L lam x i j *
          RadiusProfile.coordinateHessian u
            (fun X Y => referenceConnectionFamily g2 0 (lam,x) X Y)
            x (coordinateDirection i) (coordinateDirection j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hQ]
    ring
  rw [hprincipal]
  simp_rw [hH, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  unfold normalizedSecondDriftCoordinateJoint
  simp_rw [Finset.sum_mul, directionalFDeriv]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma normalizedSecondDriftFrame_coordinate_conversion (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (L lam : ℝ) (x : R3) (j : Fin 3) :
  (∑ a : Fin 3, normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) *
      referenceMetricGramFrame g1 L (lam,x) a j) =
    normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x) :=
by
  classical
  have hcf (k : Fin 3) :
      (∑ a : Fin 3, referenceCoFrameEntry g1 L k a (lam,x) *
        referenceMetricGramFrame g1 L (lam,x) a j) = coordinateDirection k j := by
    have h := congrArg (fun v : R3 => v j)
      (coordinateDirection_eq_sum_referenceGramFrame g1 hg1 L lam x k)
    simpa [coordinateDirection, eq_comm] using h.symm
  unfold normalizedSecondDriftFrameJoint
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have he : (∑ k : Fin 3, ∑ a : Fin 3,
      referenceCoFrameEntry g1 L k a (lam,x) *
        normalizedSecondDriftCoordinateJoint g1 g2 L k (lam,x) *
          referenceMetricGramFrame g1 L (lam,x) a j) =
      ∑ k : Fin 3, normalizedSecondDriftCoordinateJoint g1 g2 L k (lam,x) *
        coordinateDirection k j := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← hcf k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he]
  simp [coordinateDirection, EuclideanSpace.single_apply, eq_comm]

lemma contDiff_normalizedSecondDriftCoordinateJoint (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (k : Fin 3) :
  ContDiff ℝ ∞ (normalizedSecondDriftCoordinateJoint g1 g2 L k) :=
by
  have h1 (i j : Fin 3) : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      referenceConnectionFamily g1 L z (coordinateDirection i) (coordinateDirection j) k) :=
    (contDiff_piLp_apply (p := 2) (i := k)).comp
      (((contDiff_referenceConnectionFamily g1 hg1 L).clm_apply contDiff_const).clm_apply contDiff_const)
  have h2 (i j : Fin 3) : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      referenceConnectionFamily g2 0 z (coordinateDirection i) (coordinateDirection j) k) :=
    (contDiff_piLp_apply (p := 2) (i := k)).comp
      (((contDiff_referenceConnectionFamily g2 hg2 0).clm_apply contDiff_const).clm_apply contDiff_const)
  unfold normalizedSecondDriftCoordinateJoint
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (contDiff_referenceNormalizedPrincipalMatrix_entry_joint g1 g2 hg1 hg2 L i j).mul
      ((h1 i j).sub (h2 i j))))

lemma contDiff_normalizedSecondDriftFrameJoint (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (a : Fin 3) :
  ContDiff ℝ ∞ (normalizedSecondDriftFrameJoint g1 g2 L a) :=
by
  unfold normalizedSecondDriftFrameJoint
  exact ContDiff.sum (fun k _ =>
    (contDiff_referenceCoFrameEntry g1 hg1 L k a).mul
      (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L k))

theorem exists_normalizedSecondDrift_uniform_coordinate_word_bounds (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) (N : ℕ) :
  ∃ C : ℝ, 1 ≤ C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
    ∀ w : List (Fin 3), w.length ≤ N →
    (∀ k, |coordinateFieldWordPartial w
      (fun y => normalizedSecondDriftCoordinateJoint g1 g2 L k (lam,y)) x| ≤ C) ∧
    (∀ a, |coordinateFieldWordPartial w
      (fun y => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y)) x| ≤ C) :=
by
  obtain ⟨C1,hC1,h1⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun k : Fin 3 => normalizedSecondDriftCoordinateJoint g1 g2 L k)
    (fun k => contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L k) K hK N
  obtain ⟨C2,hC2,h2⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun a : Fin 3 => normalizedSecondDriftFrameJoint g1 g2 L a)
    (fun a => contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a) K hK N
  refine ⟨C1+C2,by linarith,?_⟩
  intro lam hlam x hx w hw
  constructor
  · intro k
    have ht := (h1 lam hlam x hx k w hw).trans (by linarith : C1 ≤ C1+C2)
    simpa only [Real.norm_eq_abs] using ht
  · intro a
    have ht := (h2 lam hlam x hx a w hw).trans (by linarith : C2 ≤ C1+C2)
    simpa only [Real.norm_eq_abs] using ht

end OAI.AnisotropicCalderon.ActualNormalizedSecondMetricDrift
