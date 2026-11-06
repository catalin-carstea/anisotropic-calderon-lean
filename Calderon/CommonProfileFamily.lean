import Calderon.FixedProfileBounds

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

def referenceLogRadius (δ R : ℝ) (p : ℕ) (L : ℝ) : R3 → ℝ :=
  fun x => Real.log (referenceRadius δ R p L x)

def referenceProfileNorm (g : MatrixField) (lam δ R : ℝ) (p : ℕ) (L : ℝ) : R3 → ℝ :=
  metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
    (referenceLogRadius δ R p L)

def referenceProfileBounds (g : MatrixField) (K : Set R3) (L c0 c1 J1 J2 D : ℝ) : Prop :=
  (∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
    ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      c0 * (p : ℝ) ≤ referenceProfileNorm g lam δ R p L x ∧
      (∀ X : R3, coordinateHessian (referenceLogRadius δ R p L)
        (fun V W => coordinateConnectionField
          (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
          (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x V W) x X X ≤
        -c1 * referenceProfileNorm g lam δ R p L x *
          ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X, X⟫_ℝ) ∧
      densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
        (vol (referenceMetric (dilatedMetric g lam) L))
        (fun y => inverseMetricOperator (referenceMetric (dilatedMetric g lam) L) y
          (gradient (referenceLogRadius δ R p L) y)) x ≤
        -(3 * c1) * (vol (referenceMetric (dilatedMetric g lam) L) x *
          referenceProfileNorm g lam δ R p L x) ∧
      ‖fderiv ℝ (referenceLogRadius δ R p L) x‖ ≤ J1 * referenceProfileNorm g lam δ R p L x ∧
      ‖fderiv ℝ (fderiv ℝ (referenceLogRadius δ R p L)) x‖ ≤
        J2 * referenceProfileNorm g lam δ R p L x ^ 2 ∧
      ‖fderiv ℝ (referenceProfileNorm g lam δ R p L) x‖ ≤
        D * referenceProfileNorm g lam δ R p L x ^ 2 ∧
      ‖fderiv ℝ (fun y => (referenceProfileNorm g lam δ R p L y)⁻¹) x‖ ≤ D) ∧
  (∀ p : ℕ, 2 ≤ p → ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
      ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
      referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x ^ 2 ≤ ε)

theorem exists_referenceProfileBounds (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : Set R3) (hK : IsCompact K) :
    ∃ L c0 c1 J1 J2 D : ℝ, 0 < L ∧ 0 < c0 ∧ 0 < c1 ∧ 0 < J1 ∧ 0 < J2 ∧ 0 < D ∧
      referenceProfileBounds g K L c0 c1 J1 J2 D := by
  obtain ⟨L, c0, c1, C, T, hL, hc0, hc1, hC, hbounds⟩ :=
    exists_dilated_referenceRadius_uniform_metric_bounds g hg K hK
  obtain ⟨J1, J2, hJ1, hJ2, hjets⟩ :=
    exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at g hg K hK L hL
  obtain ⟨D, hD, hbeta⟩ :=
    exists_dilated_referenceRadius_uniform_beta_derivative_bounds_at g hg K hK L hL
  refine ⟨L, c0, c1, J1, J2, D, hL, hc0, hc1, hJ1, hJ2, hD, ?_⟩
  dsimp [referenceProfileBounds, referenceLogRadius, referenceProfileNorm]
  constructor
  · intro lam hlam δ hδ hδ1 R hR p hp x hx
    obtain ⟨hb, hH, hr⟩ := hbounds lam hlam δ hδ hδ1 R hR p 0 (Nat.zero_le p) x hx
    obtain ⟨hj1, hj2⟩ := hjets lam hlam δ hδ hδ1 R hR p hp x hx
    obtain ⟨hb1, hb2⟩ := hbeta lam hlam δ hδ hδ1 R hR p hp x hx
    refine ⟨hb, hH, ?_, hj1, hj2, hb1, hb2⟩
    exact densityWeightedDivergence_le_of_profile_hessian _
      (dilatedReferenceMetric_smooth_entries g hg lam L)
      (dilatedReferenceMetric_posDef g hg lam L) _
      (contDiff_log_referenceRadius δ R p L hδ hR) c1 x hH
  · intro p hp ε hε
    exact exists_dilated_referenceRadius_uniform_small_amplitude_at g hg K hK L hL p hp ε hε

theorem referenceProfileBounds_choose_degree_radius
    (g : MatrixField) (K : Set R3) (L c0 c1 J1 J2 D : ℝ)
    (hc0 : 0 < c0) (hbounds : referenceProfileBounds g K L c0 c1 J1 J2 D)
    (beta0 ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
        beta0 ≤ referenceProfileNorm g lam δ R p L x ∧
        ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
        referenceRadius δ R p L x * referenceProfileNorm g lam δ R p L x ^ 2 ≤ ε := by
  obtain ⟨q, hq⟩ := exists_nat_gt (beta0 / c0)
  let p := max q 2
  have hp : 2 ≤ p := le_max_right _ _
  have hp1 : 1 ≤ p := by omega
  have hqp : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_max_left q 2
  have hlarge : beta0 ≤ c0 * (p : ℝ) := by
    have hq' : beta0 / c0 ≤ (p : ℝ) := le_trans hq.le hqp
    have h := (div_le_iff₀ hc0).mp hq'
    simpa only [mul_comm] using h
  obtain ⟨R, hR, hr⟩ := hbounds.2 p hp ε hε
  refine ⟨p, hp, R, hR, ?_⟩
  intro lam hlam δ hδ hδ1 x hx
  exact ⟨hlarge.trans (hbounds.1 lam hlam δ hδ hδ1 R hR p hp1 x hx).1,
    (hr lam hlam δ hδ hδ1 x hx).1, (hr lam hlam δ hδ hδ1 x hx).2⟩

end OAI.AnisotropicCalderon.ConformalDepth
