import Calderon.ProfileCovariantJets

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open RadiusProfile AngularPolynomial MetricOperator ConnectionError

def referenceConnectionFamily (g : MatrixField) (L : ℝ) : CoordinateConnectionFamily :=
  fun z => coordinateConnectionField
    (inverseMetricOperator (referenceMetric (dilatedMetric g z.1) L))
    (metricOperatorField (referenceMetric (dilatedMetric g z.1) L)) z.2

lemma contDiff_referenceMetricOperator_joint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      metricOperatorField (referenceMetric (dilatedMetric g z.1) L) z.2) := by
  have hmul : ContDiff ℝ ∞ (fun z : ℝ × R3 => z.1 • z.2) :=
    contDiff_fst.smul contDiff_snd
  have hM := (contDiff_metricOperatorField g hg).comp hmul
  have ha : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      Real.exp (-2 * L * referenceCoordinateDepth z.2)) :=
    (contDiff_const.mul (contDiff_referenceCoordinateDepth.comp contDiff_snd)).exp
  have he : (fun z : ℝ × R3 =>
      metricOperatorField (referenceMetric (dilatedMetric g z.1) L) z.2) =
      fun z => Real.exp (-2 * L * referenceCoordinateDepth z.2) • metricOperatorField g (z.1 • z.2) := by
    funext z
    exact referenceMetric_operator_eq (dilatedMetric g z.1) L z.2
  rw [he]
  exact ha.smul hM

lemma contDiff_referenceInverseMetricOperator_joint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      inverseMetricOperator (referenceMetric (dilatedMetric g z.1) L) z.2) := by
  have hmul : ContDiff ℝ ∞ (fun z : ℝ × R3 => z.1 • z.2) :=
    contDiff_fst.smul contDiff_snd
  have hQ := (contDiff_inverseMetricOperator g hg).comp hmul
  have ha : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      Real.exp (2 * L * referenceCoordinateDepth z.2)) :=
    (contDiff_const.mul (contDiff_referenceCoordinateDepth.comp contDiff_snd)).exp
  have he : (fun z : ℝ × R3 =>
      inverseMetricOperator (referenceMetric (dilatedMetric g z.1) L) z.2) =
      fun z => Real.exp (2 * L * referenceCoordinateDepth z.2) • inverseMetricOperator g (z.1 • z.2) :=
    funext (fun z => inverseMetricOperator_dilatedReference g hg z.1 L z.2)
  rw [he]
  exact ha.smul hQ

lemma contDiff_referenceConnectionFamily (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) : ContDiff ℝ ∞ (referenceConnectionFamily g L) := by
  let M : ℝ × R3 → R3 →L[ℝ] R3 := fun z =>
    metricOperatorField (referenceMetric (dilatedMetric g z.1) L) z.2
  let Q : ℝ × R3 → R3 →L[ℝ] R3 := fun z =>
    inverseMetricOperator (referenceMetric (dilatedMetric g z.1) L) z.2
  have hM : ContDiff ℝ ∞ M := contDiff_referenceMetricOperator_joint g hg L
  have hQ : ContDiff ℝ ∞ Q := contDiff_referenceInverseMetricOperator_joint g hg L
  have heD : (fun z : ℝ × R3 => fderiv ℝ (fun y => M (z.1, y)) z.2) =
      fun z => (fderiv ℝ M z).comp (ContinuousLinearMap.inr ℝ ℝ R3) := by
    funext z
    have hp : HasFDerivAt (fun y : R3 => (z.1, y)) (ContinuousLinearMap.inr ℝ ℝ R3) z.2 :=
      hasFDerivAt_prodMk_right z.1 z.2
    have h := ((hM.differentiable (by simp) z).hasFDerivAt).comp z.2 hp
    change fderiv ℝ (M ∘ fun y : R3 => (z.1, y)) z.2 = _
    exact h.fderiv
  have hD : ContDiff ℝ ∞ (fun z : ℝ × R3 => fderiv ℝ (fun y => M (z.1, y)) z.2) := by
    rw [heD]
    exact (contDiff_infty_iff_fderiv.mp hM).2.clm_comp contDiff_const
  have hK := koszulLinearMap.contDiff.comp hD
  have hComp := ((ContinuousLinearMap.compL ℝ R3 R3 R3).contDiff.comp hQ).clm_comp hK
  change ContDiff ℝ ∞ (fun z : ℝ × R3 =>
    coordinateConnectionLinearMap (Q z) (fderiv ℝ (fun y => M (z.1, y)) z.2))
  exact hComp.const_smul (1 / 2 : ℝ)

lemma exists_dilated_referenceRadius_fixed_uniform_frechet_jets_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (n : ℕ) :
    ∃ J : ℝ, 0 < J ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ n →
        ‖iteratedFDeriv ℝ k (fun y => Real.log (referenceRadius δ R p L y)) x‖ ≤
          J * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ k := by
  choose J hJ using fun i : Fin n =>
    exists_dilated_referenceRadius_fixed_uniform_frechet_jet_bound g hg L hL K hK (i.val + 1) (by omega)
  let S : ℝ := ∑ i : Fin n, J i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => (hJ i).1.le)
  refine ⟨S + 1, by linarith, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx k hk hkn
  let i : Fin n := ⟨k - 1, by omega⟩
  have hi : i.val + 1 = k := by dsimp [i]; omega
  have h := (hJ i).2 lam hlam δ hδ hδ1 R hR p hp x hx
  rw [hi] at h
  have hsingle : J i ≤ S :=
    Finset.single_le_sum (s := Finset.univ) (a := i) (f := J)
      (fun j _ => (hJ j).1.le) (Finset.mem_univ i)
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith)
    (pow_nonneg (Real.sqrt_nonneg _) k))

theorem exists_dilated_referenceRadius_fixed_uniform_covariant_components_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ I : Fin n → Fin 3,
        |covariantCoordinateJet (referenceConnectionFamily g L)
          (fun y => Real.log (referenceRadius δ R p L y)) lam n x I| ≤
          Cn * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ n := by
  obtain ⟨A, hA, hcov⟩ := exists_covariantCoordinateJet_compact_bound
    (referenceConnectionFamily g L) (contDiff_referenceConnectionFamily g hg L) n hn K hK
  obtain ⟨J, hJ, hjets⟩ :=
    exists_dilated_referenceRadius_fixed_uniform_frechet_jets_bound g hg L hL K hK n
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  let a0 : ℝ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha0 : 0 < a0 := by
    dsimp [a0]
    exact one_div_pos.mpr (by linarith [log_exp_add_one_pos T])
  let B : ℝ := max 1 (1 / (a0 * m))
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨A * J * B ^ n + 1, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx I
  let f : R3 → ℝ := fun y => Real.log (referenceRadius δ R p L y)
  let beta : ℝ := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) f x
  have hf : ContDiff ℝ ∞ f := by
    dsimp [f]
    rw [log_referenceRadius δ R p L hδ hR]
    exact contDiff_const.add (contDiff_const.mul
      ((contDiff_scalar_log_softplus δ hδ).comp (contDiff_referenceDepth L)))
  have hbeta : 0 ≤ beta := Real.sqrt_nonneg _
  obtain ⟨hmin, hmax, ht⟩ := hbounds lam hlam x hx
  have ha := logSlope_uniform_lower_bound δ _ T hδ hδ1 ht
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hbLower : a0 * m ≤ beta := by
    dsimp [beta, f]
    rw [log_referenceRadius δ R p L hδ hR,
      metricDifferentialNorm_logProfile _ δ (Real.log R) p _ x hδ
        ((contDiff_referenceDepth L).differentiable (by simp) x)]
    have hpSlope : a0 ≤ (p : ℝ) * logSlope δ (referenceDepth L x) := by
      nlinarith [logSlope_pos δ (referenceDepth L x) hδ]
    exact mul_le_mul hpSlope hmin hm.le
      (mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ _ hδ).le)
  have hBa : 1 ≤ B * beta := by
    have h1 : 1 / (a0 * m) ≤ B := le_max_right _ _
    have h2 := mul_le_mul h1 hbLower (mul_pos ha0 hm).le (show 0 ≤ B by linarith)
    have he : (1 / (a0 * m)) * (a0 * m) = 1 := by field_simp
    rwa [he] at h2
  have h := hcov lam hlam x hx I f hf beta B J hbeta hB hBa hJ.le
    (hjets lam hlam δ hδ hδ1 R hR p hp x hx)
  exact h.trans (by nlinarith [pow_nonneg hbeta n])

end OAI.AnisotropicCalderon.ConformalDepth
