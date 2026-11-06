import Calderon.ActualDensityScalarCutoff
import Calderon.ActualHorizontalGeometry
import Calderon.ActualNormalizedSecondMetricDrift
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SmoothMetricFrame MovingFrameConnection
  ActualHorizontalNormBridge ActualNormalizedSecondMetricDrift
attribute [local irreducible] referenceMetricGramFrame referenceFrameConnectionCoefficient
  referenceFrameConnectionJoint referenceFrameScalarDerivative referenceFrameScalarHessian
  normalizedSecondDriftFrameJoint

private lemma fderiv_joint_slice_apply {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℝ × R3 → V) (q : ℝ) (y X : R3)
    (hF : DifferentiableAt ℝ F (q,y)) :
    fderiv ℝ (fun z => F (q,z)) y X = fderiv ℝ F (q,y) (0,X) := by
  have hp : HasFDerivAt (fun z : R3 => (q,z)) (ContinuousLinearMap.inr ℝ ℝ R3) y :=
    hasFDerivAt_prodMk_right q y
  have h := hF.hasFDerivAt.comp y hp
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using
    congrArg (fun T : R3 →L[ℝ] V => T X) h.fderiv

theorem contDiff_referenceFrameScalarDerivative_joint
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (chi : R3 → ℝ) (hchi : ContDiff ℝ ∞ chi) (i : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × R3 => referenceFrameScalarDerivative g L p.1 chi p.2 i) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ chi) := hchi.fderiv_right (m := ∞) (by simp)
  simpa only [referenceFrameScalarDerivative,Function.comp_def,Prod.mk.eta] using
    (hD.comp contDiff_snd).clm_apply (contDiff_referenceMetricGramFrame g hg L i)

theorem contDiff_referenceFrameScalarHessian_joint
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (chi : R3 → ℝ) (hchi : ContDiff ℝ ∞ chi) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × R3 => referenceFrameScalarHessian g L p.1 chi p.2 i j) := by
  let dj : ℝ × R3 → ℝ := fun p => referenceFrameScalarDerivative g L p.1 chi p.2 j
  have hdj : ContDiff ℝ ∞ dj := contDiff_referenceFrameScalarDerivative_joint g hg L chi hchi j
  have hD : ContDiff ℝ ∞ (fderiv ℝ dj) := hdj.fderiv_right (m := ∞) (by simp)
  have he := contDiff_referenceMetricGramFrame g hg L i
  have hFirst : ContDiff ℝ ∞ (fun p : ℝ × R3 =>
      fderiv ℝ dj p (0,referenceMetricGramFrame g L p i)) :=
    hD.clm_apply (contDiff_const.prodMk he)
  have hGamma (k : Fin 3) : ContDiff ℝ ∞ (fun p : ℝ × R3 =>
      referenceFrameConnectionCoefficient g L p.1 p.2
        (referenceMetricGramFrame g L p i) k j) := by
    have h := contDiff_referenceFrameConnectionJoint g hg L
      (fun p => referenceMetricGramFrame g L p i) he k j
    simpa only [referenceFrameConnectionJoint_eq g hg L] using h
  have hRest : ContDiff ℝ ∞ (fun p : ℝ × R3 => ∑ k : Fin 3,
      referenceFrameConnectionCoefficient g L p.1 p.2
        (referenceMetricGramFrame g L p i) k j * referenceFrameScalarDerivative g L p.1 chi p.2 k) :=
    ContDiff.sum (fun k _ => (hGamma k).mul
      (contDiff_referenceFrameScalarDerivative_joint g hg L chi hchi k))
  have hRep : (fun p : ℝ × R3 => referenceFrameScalarHessian g L p.1 chi p.2 i j) =
      (fun p : ℝ × R3 => fderiv ℝ dj p (0,referenceMetricGramFrame g L p i) -
        ∑ k : Fin 3, referenceFrameConnectionCoefficient g L p.1 p.2
          (referenceMetricGramFrame g L p i) k j * referenceFrameScalarDerivative g L p.1 chi p.2 k) := by
    funext p
    unfold referenceFrameScalarHessian
    have hSlice := fderiv_joint_slice_apply dj p.1 p.2 (referenceMetricGramFrame g L p i)
      (hdj.differentiable (by simp) p)
    exact congrArg (fun t : ℝ => t-∑ k : Fin 3,
      referenceFrameConnectionCoefficient g L p.1 p.2
        (referenceMetricGramFrame g L p i) k j * referenceFrameScalarDerivative g L p.1 chi p.2 k) hSlice
  rw [hRep]
  exact hFirst.sub hRest

theorem exists_compact_referenceDensity_cutoff_scalar_coefficients_bound
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (chi : R3 → ℝ) (hchi : ContDiff ℝ ∞ chi) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0:ℝ) 1, ∀ y ∈ K, ∀ i j : Fin 3,
      |referenceFrameScalarDerivative g L q chi y i| ≤ M ∧
      |referenceFrameScalarHessian g L q chi y i j| ≤ M ∧
      |normalizedSecondDriftFrameJoint g g2 L i (q,y)| ≤ M := by
  let T (ij : Fin 3 × Fin 3) (p : ℝ × R3) :=
    (referenceFrameScalarDerivative g L p.1 chi p.2 ij.1,
      (referenceFrameScalarHessian g L p.1 chi p.2 ij.1 ij.2,
        normalizedSecondDriftFrameJoint g g2 L ij.1 p))
  have hT (ij : Fin 3 × Fin 3) : Continuous (T ij) :=
    (contDiff_referenceFrameScalarDerivative_joint g hg L chi hchi ij.1).continuous.prodMk
      ((contDiff_referenceFrameScalarHessian_joint g hg L chi hchi ij.1 ij.2).continuous.prodMk
        (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L ij.1).continuous)
  have hCompact : IsCompact (Icc (0:ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  have hBounds : ∀ ij : Fin 3 × Fin 3, ∃ M : ℝ, ∀ p ∈ Icc (0:ℝ) 1 ×ˢ K, ‖T ij p‖ ≤ M := by
    intro ij
    exact hCompact.exists_bound_of_continuousOn (hT ij).continuousOn
  choose M hBound using hBounds
  obtain ⟨C0,hC0⟩ := (Set.finite_range M).bddAbove
  refine ⟨max C0 1,le_max_right _ _,?_⟩
  intro q hq y hy i j
  have h : ‖T (i,j) (q,y)‖ ≤ max C0 1 :=
    (hBound (i,j) (q,y) ⟨hq,hy⟩).trans ((hC0 ⟨(i,j),rfl⟩).trans (le_max_left _ _))
  simpa only [T,Prod.norm_def,Real.norm_eq_abs,max_le_iff] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
