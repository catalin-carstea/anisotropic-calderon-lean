import Calderon.ActualConstantOneFirstAngularLift
import Calderon.ActualFirstCorrectionSobolevFamilies
import Calderon.ActualHorizontalGeometry
import Calderon.ActualScalarCutoffJointCoefficients
import Calderon.ActualDensityPrincipalFrameCoefficientBound
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualHorizontalNormBridge ActualNormalizedSecondMetricDrift
attribute [local irreducible] harmonicSphereSubspace referenceNativeMovingAdjointParametricCorrection
  referenceFrameConnectionCoefficient referenceMetricGramFrame normalizedSecondDriftFrameJoint
  referenceDensityPrincipalFrameCoefficient sphereSobolevInclusionL constantOneFirstRaisingThreeHalf

theorem exists_compact_constantForcing_actual_coefficient_caps
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧
      ‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)‖ ≤ M ∧
      (∀ i : Fin 3, ‖constantOneFirstRaisingThreeHalf hF i‖ ≤ M) ∧
      ∀ q ∈ Icc (0:ℝ) 1, ∀ y ∈ K, ∀ ell : R3 →L[ℝ] ℝ, ‖ell‖ ≤ 1 → ∀ i j k : Fin 3,
      ‖(sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2:ℝ) ((q,y),ell) i)‖ ≤ M ∧
      |referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j| ≤ M ∧
      |normalizedSecondDriftFrameJoint g g2 L i (q,y)| ≤ M ∧
      |referenceDensityPrincipalFrameCoefficient g g2 L q y i j| ≤ 3 := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J : Set ((ℝ × R3) × (R3 →L[ℝ] ℝ)) :=
    (Icc (0:ℝ) 1 ×ˢ K) ×ˢ closedBall (0 : R3 →L[ℝ] ℝ) 1
  have hJ : IsCompact J := (isCompact_Icc.prod hK).prod (isCompact_closedBall _ _)
  let F (i : Fin 3) (t : (ℝ × R3) × (R3 →L[ℝ] ℝ)) :=
    I.comp (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2:ℝ) t i)
  have hFcont (i : Fin 3) : Continuous (F i) :=
    (contDiff_const.clm_comp (contDiff_referenceNativeMovingAdjointParametricCorrection
      hF hO hD g hg L (3/2:ℝ) i)).continuous
  have hRaw (i : Fin 3) := hJ.exists_bound_of_continuousOn (hFcont i).continuousOn
  choose c hc using hRaw
  obtain ⟨Cc,hCc⟩ := (Set.finite_range c).bddAbove
  let Mc := max Cc 1
  have hMc : 1 ≤ Mc := le_max_right _ _
  have hCorr (i : Fin 3) (t : (ℝ × R3) × (R3 →L[ℝ] ℝ)) (ht : t ∈ J) : ‖F i t‖ ≤ Mc :=
    (hc i t ht).trans ((hCc ⟨i,rfl⟩).trans (le_max_left _ _))
  obtain ⟨Mg,hMg,hGeom⟩ := exists_reference_geometry_uniform_bounds g hg L K hK
  obtain ⟨Mb,hMb,hDrift⟩ := exists_compact_referenceDensity_cutoff_scalar_coefficients_bound
    g g2 hg hg2 L (fun _ => (0:ℝ)) contDiff_const K hK
  obtain ⟨Ca,hCa⟩ := (Set.finite_range (fun i : Fin 3 => ‖constantOneFirstRaisingThreeHalf hF i‖)).bddAbove
  let Ma := max Ca 1
  have hMa : 1 ≤ Ma := le_max_right _ _
  have hAngular (i : Fin 3) : ‖constantOneFirstRaisingThreeHalf hF i‖ ≤ Ma :=
    (hCa ⟨i,rfl⟩).trans (le_max_left _ _)
  let M := Mc+Mg+Mb+Ma+‖I‖+3
  have hI0 : 0 ≤ ‖I‖ := norm_nonneg I
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hMcM : Mc ≤ M := by dsimp [M]; linarith
  have hMgM : Mg ≤ M := by dsimp [M]; linarith
  have hMbM : Mb ≤ M := by dsimp [M]; linarith
  have hMaM : Ma ≤ M := by dsimp [M]; linarith
  have hIM : ‖I‖ ≤ M := by dsimp [M]; linarith
  refine ⟨M,hM,hIM,fun i => (hAngular i).trans hMaM,?_⟩
  intro q hq y hy ell hell i j k
  have ht : ((q,y),ell) ∈ J := ⟨⟨hq,hy⟩,by simpa only [mem_closedBall,dist_zero_right] using hell⟩
  exact ⟨(hCorr i _ ht).trans hMcM,((hGeom q hq y hy).2.2.2 i k j).trans hMgM,
    ((hDrift q hq y hy i j).2.2).trans hMbM,
    abs_referenceDensityPrincipalFrameCoefficient_le_three g g2 hg hg2 L q y i j⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
