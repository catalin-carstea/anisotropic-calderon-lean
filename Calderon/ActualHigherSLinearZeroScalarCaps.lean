import Calderon.ActualHigherSZeroCoefficientBounds
import Calderon.ActualHigherSCoordinateWeightBounds
/-! Independent original-hypothesis scalar producer for linear zero and 207 words.
Full expansion/signature archived in linear-zero-scalar-upfront-v001. UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLinearZeroScalarCaps
open EnergyBridge ConnectionError ReferenceDensityBounds ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift ActualHigherSZeroCoefficientBounds ConformalDepth
open SmoothMetricFrame MovingFrameConnection

/-- Public local finite compact-family bound; the selected original helper is private. -/
lemma compact_family_cap {X V I : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup V] [Fintype I] (K : Set X) (hK : IsCompact K)
    (f : I → X → V) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i : I, ∀ x ∈ K, ‖f i x‖ ≤ M := by
  classical
  choose C hC using fun i : I => hK.exists_bound_of_continuousOn (hf i)
  have hs0 : 0 ≤ ∑ i : I, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1+∑ i : I, |C i|,by linarith,?_⟩
  intro i x hx
  apply (hC i x hx).trans
  calc
    C i ≤ |C i| := le_abs_self _
    _ ≤ ∑ j : I, |C j| := Finset.single_le_sum (f := fun j : I => |C j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ 1+∑ j : I, |C j| := by linarith

/-- Constants are fixed before q, every radius profile and every angular input. -/
theorem exists_word_scalar_caps (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (y0 : R3) (rho : ℝ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, 0 < Ar →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      (∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ M) ∧
      (∀ i k j : Fin 3, |referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j| ≤ M) ∧
      (∀ i : Fin 3, |referenceRadiusHorizontalLogDerivative g L q
        (referenceRadius dr Ar p L) x i| ≤ M*actualReferenceBeta g L q dr Ar p x) ∧
      (∀ i : Fin 3, ‖referenceMetricGramFrame g L (q,x) i‖ ≤ M) ∧
      (∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ M) := by
  have hKx : IsCompact (closedBall y0 rho) := isCompact_closedBall y0 rho
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall y0 rho) := isCompact_Icc.prod hKx
  obtain ⟨CQ,hCQ,hQ⟩ := ActualHigherSCoefficientBounds.exists_principal_frame_uniform_bound
    g L y0 rho hg g2 hg2
  obtain ⟨CX,hCX,hX⟩ := compact_family_cap _ hK
    (fun i : Fin 3 => fun z : ℝ × R3 => referenceMetricGramFrame g L z i)
    (fun i => (contDiff_referenceMetricGramFrame g hg L i).continuous.continuousOn)
  obtain ⟨Cb,hCb,hb⟩ := compact_family_cap _ hK
    (fun i : Fin 3 => fun z : ℝ × R3 => normalizedSecondDriftFrameJoint g g2 L i z)
    (fun i => (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).continuous.continuousOn)
  obtain ⟨MG,hMG,hG⟩ := ActualHorizontalNormBridge.exists_reference_geometry_uniform_bounds
    g hg L (closedBall y0 rho) hKx
  obtain ⟨J1,J2,hJ1,hJ2,hJ⟩ := exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at
    g hg (closedBall y0 rho) hKx L hL
  have hCQ0 : 0 ≤ CQ := zero_le_one.trans hCQ
  have hCX0 : 0 ≤ CX := zero_le_one.trans hCX
  have hCb0 : 0 ≤ Cb := zero_le_one.trans hCb
  have hMG0 : 0 ≤ MG := zero_le_one.trans hMG
  have hprod : 0 ≤ J1*CX := mul_nonneg hJ1.le hCX0
  let M : ℝ := 1+CQ+CX+Cb+MG+J1*CX
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hQM : CQ ≤ M := by dsimp only [M]; linarith
  have hXM : CX ≤ M := by dsimp only [M]; linarith
  have hbM : Cb ≤ M := by dsimp only [M]; linarith
  have hGM : MG ≤ M := by dsimp only [M]; linarith
  have hfM : J1*CX ≤ M := by dsimp only [M]; linarith
  refine ⟨M,hM,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx hbeta
  have hbeta0 : 0 ≤ actualReferenceBeta g L q dr Ar p x := zero_le_one.trans hbeta
  have hXn (i : Fin 3) : ‖referenceMetricGramFrame g L (q,x) i‖ ≤ CX := hX i (q,x) ⟨hq,hx⟩
  have hlog : ‖fderiv ℝ (fun y => Real.log (referenceRadius dr Ar p L y)) x‖ ≤
      J1*actualReferenceBeta g L q dr Ar p x := (hJ q hq dr hdr hdr1 Ar hAr p hp x hx).1
  refine ⟨fun i j => ((hQ q hq x hx i j).1).trans hQM,
    fun i k j => ((hG q hq x hx).2.2.2 i k j).trans hGM,?_,
    fun i => (hXn i).trans hXM,?_⟩
  · intro i
    have he : referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i =
        fderiv ℝ (fun y => Real.log (referenceRadius dr Ar p L y)) x
          (referenceMetricGramFrame g L (q,x) i) := by
      unfold referenceRadiusHorizontalLogDerivative
      rw [conformalFrame_coordinateVector_eq g L q x i]
    rw [he,← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (fun y => Real.log (referenceRadius dr Ar p L y)) x‖ *
        ‖referenceMetricGramFrame g L (q,x) i‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (J1*actualReferenceBeta g L q dr Ar p x)*CX :=
        mul_le_mul hlog (hXn i) (norm_nonneg _) (mul_nonneg hJ1.le hbeta0)
      _ = (J1*CX)*actualReferenceBeta g L q dr Ar p x := by ring
      _ ≤ M*actualReferenceBeta g L q dr Ar p x := mul_le_mul_of_nonneg_right hfM hbeta0
  · intro i
    have hi := hb i (q,x) ⟨hq,hx⟩
    rw [Real.norm_eq_abs] at hi
    exact hi.trans hbM
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLinearZeroScalarCaps
