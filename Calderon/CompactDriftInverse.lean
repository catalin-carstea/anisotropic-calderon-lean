import Calderon.CompactInverseDerivativeBounds
import Mathlib.Topology.Compactness.Compact
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily
variable {P X Y Z : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def linearDriftOperatorFamily (A D : P × ℝ → X →L[ℝ] Y) (L : ℝ) (p : P × ℝ) : X →L[ℝ] Y :=
  A p+(-L*p.2) • D p

theorem contDiff_linearDriftOperatorFamily (A D : P × ℝ → X →L[ℝ] Y)
    (hA : ContDiff ℝ ∞ A) (hD : ContDiff ℝ ∞ D) (L : ℝ) :
    ContDiff ℝ ∞ (linearDriftOperatorFamily A D L) :=
  hA.add ((contDiff_const.mul contDiff_snd).smul hD)

theorem linearDriftOperatorFamily_zero (A D : P × ℝ → X →L[ℝ] Y) (L : ℝ) (y : P) :
    linearDriftOperatorFamily A D L (y,0) = A (y,0) := by
  simp [linearDriftOperatorFamily]

theorem exists_compact_smallRadius_linearDrift_inverse
    (A D : P × ℝ → X →L[ℝ] Y) (hA : ContDiff ℝ ∞ A) (hD : ContDiff ℝ ∞ D)
    (L : ℝ) (q : Set P) (hq : IsCompact q)
    (hi : ∀ y ∈ q, (A (y,0)).IsInvertible) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧
      (∀ p ∈ q ×ˢ Icc (-delta) delta, (linearDriftOperatorFamily A D L p).IsInvertible) ∧
      ContDiffOn ℝ ∞ (fun p => (linearDriftOperatorFamily A D L p).inverse) (q ×ˢ Icc (-delta) delta) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ q ×ˢ Icc (-delta) delta, ∀ f : Y,
        ‖(linearDriftOperatorFamily A D L p).inverse f‖ ≤ C*‖f‖) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ q ×ˢ Icc (-delta) delta,
        ‖iteratedFDeriv ℝ j (fun t => (linearDriftOperatorFamily A D L t).inverse) p‖ ≤ C := by
  let F := linearDriftOperatorFamily A D L
  have hF := contDiff_linearDriftOperatorFamily A D hA hD L
  have ho : IsOpen {p : P × ℝ | (F p).IsInvertible} :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hF.continuous
  have hsub : q ×ˢ ({0} : Set ℝ) ⊆ {p : P × ℝ | (F p).IsInvertible} := by
    intro p hp
    have hr : p.2 = 0 := hp.2
    change (linearDriftOperatorFamily A D L p).IsInvertible
    obtain ⟨y,r⟩ := p
    simp only at hr
    subst r
    rw [linearDriftOperatorFamily_zero]
    exact hi y hp.1
  obtain ⟨U,V,hU,hV,hqU,h0V,hUV⟩ :=
    generalized_tube_lemma hq isCompact_singleton ho hsub
  obtain ⟨d,hd,hball⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton (0 : ℝ)))
  let delta := min (d/2) eta
  have hdelta : 0 < delta := lt_min (by positivity) heta
  have hiF (p : P × ℝ) (hp : p ∈ q ×ˢ Icc (-delta) delta) : (F p).IsInvertible := by
    apply hUV ⟨hqU hp.1,hball ?_⟩
    rw [mem_ball,dist_zero_right,Real.norm_eq_abs]
    have hr : |p.2| ≤ delta := abs_le.mpr hp.2
    exact lt_of_le_of_lt (hr.trans (min_le_left _ _)) (half_lt_self hd)
  obtain ⟨C,hC,hbound⟩ := uniform_norm_banachInverseFamily F (q ×ˢ Icc (-delta) delta)
    (hq.prod isCompact_Icc) hF.continuous.continuousOn hiF
  refine ⟨delta,hdelta,min_le_right _ _,hiF,
    contDiffOn_banachInverseFamily F _ hF.contDiffOn hiF,⟨C,hC,?_⟩,?_⟩
  · intro p hp f
    exact ((F p).inverse.le_opNorm f).trans (mul_le_mul_of_nonneg_right (hbound p hp) (norm_nonneg f))
  · intro N
    exact exists_compact_banachInverse_derivative_bound F hF (q ×ˢ Icc (-delta) delta)
      (hq.prod isCompact_Icc) hiF N

theorem exists_compact_smallRadius_linearDrift_weighted_inverse
    (A D : P × ℝ → X →L[ℝ] Y) (hA : ContDiff ℝ ∞ A) (hD : ContDiff ℝ ∞ D)
    (W : P × ℝ → Z →L[ℝ] Y) (hW : ContDiff ℝ ∞ W)
    (L : ℝ) (q : Set P) (hq : IsCompact q)
    (hi : ∀ y ∈ q, (A (y,0)).IsInvertible) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧
      (∀ p ∈ q ×ˢ Icc (-delta) delta, (linearDriftOperatorFamily A D L p).IsInvertible) ∧
      ContDiffOn ℝ ∞ (fun p => (linearDriftOperatorFamily A D L p).inverse) (q ×ˢ Icc (-delta) delta) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ q ×ˢ Icc (-delta) delta, ∀ f : Y,
        ‖(linearDriftOperatorFamily A D L p).inverse f‖ ≤ C*‖f‖) ∧
      (∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ q ×ˢ Icc (-delta) delta,
        ‖iteratedFDeriv ℝ j (fun t => (linearDriftOperatorFamily A D L t).inverse) p‖ ≤ C) ∧
      ContDiffOn ℝ ∞ (fun p => (linearDriftOperatorFamily A D L p).inverse.comp (W p)) (q ×ˢ Icc (-delta) delta) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ q ×ˢ Icc (-delta) delta,
        ‖iteratedFDeriv ℝ j (fun t => (linearDriftOperatorFamily A D L t).inverse.comp (W t)) p‖ ≤ C := by
  obtain ⟨delta,hd,he,hiF,hs,hb,hjets⟩ :=
    exists_compact_smallRadius_linearDrift_inverse A D hA hD L q hq hi eta heta
  have hF := contDiff_linearDriftOperatorFamily A D hA hD L
  refine ⟨delta,hd,he,hiF,hs,hb,hjets,
    contDiffOn_banachWeightedInverse _ W _ hF.contDiffOn hiF hW.contDiffOn,?_⟩
  intro N
  exact exists_compact_banachWeightedInverse_derivative_bound _ hF W hW
    (q ×ˢ Icc (-delta) delta) (hq.prod isCompact_Icc) hiF N
end OAI.AnisotropicCalderon.DirichletFamily
