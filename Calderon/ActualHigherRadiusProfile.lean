import Calderon.ProfileFrechetJets
import Calderon.ReferenceWeightedApproximation

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualHigherRadiusProfile
open SphereHarmonic ConformalDepth RadiusProfile ReferenceWeightedApproximation
  ReferenceDensityBounds

/-- Genuine fixed-L actual beta/radius allocation for an arbitrary required
nonnegative integer power, with p0 chosen before p and R before lambda/delta. -/
theorem exists_fixed_actual_reference_beta_power_radius_profile
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (q : ℕ) :
    ∃ p0 : ℕ, q ≤ p0 ∧ 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ R : ℝ, 0 < R ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          1 ≤ actualReferenceBeta g L lam δ R p x ∧
          referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^q ≤ eta ∧
          referenceRadius δ R p L x ≤ eta := by
  obtain ⟨m,C,T,hm,hC,hdepth⟩ := exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  let a0 : ℝ := 1/(1+Real.log (1+Real.exp T))
  have ha0 : 0 < a0 := by dsimp [a0]; positivity [log_exp_add_one_pos T]
  let c0 : ℝ := a0*m
  have hc0 : 0 < c0 := mul_pos ha0 hm
  obtain ⟨u,hu⟩ := exists_nat_gt (1/c0)
  let p0 : ℕ := max q (max u 2)
  have hq0 : q ≤ p0 := le_max_left _ _
  have hp02 : 2 ≤ p0 := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨p0,hq0,hp02,?_⟩
  intro p hp eta heta _heta1
  have hqp : q ≤ p := le_trans hq0 hp
  have hp1 : 1 ≤ p := by omega
  have hup : (u : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast le_trans (le_trans (le_max_left u 2) (le_max_right q (max u 2))) hp
  have hlarge : 1 ≤ (p : ℝ)*c0 := by
    have h := (div_le_iff₀ hc0).mp (le_trans hu.le hup)
    simpa only [mul_comm] using h
  let A : ℝ := (p : ℝ)^q*C^q*(Real.log (1+Real.exp T))^(p-q)
  have hA : 0 ≤ A := by dsimp [A]; positivity [log_exp_add_one_pos T]
  let R : ℝ := eta/(A+1)
  have hden : 0 < A+1 := by positivity
  have hR : 0 < R := div_pos heta hden
  have hEq : R*(A+1)=eta := by dsimp [R]; field_simp
  have hRA : R*A ≤ eta := by nlinarith only [hEq,hR]
  refine ⟨R,hR,?_⟩
  intro lam hlam δ hδ hδ1 x hx
  obtain ⟨hmin,hmax,ht⟩ := hdepth lam hlam x hx
  have hs := logSlope_uniform_lower_bound δ (referenceDepth L x) T hδ hδ1 ht
  have hbeta : 1 ≤ actualReferenceBeta g L lam δ R p x := by
    rw [actualReferenceBeta_eq g L lam δ R p hδ hR x]
    have hmul : a0*m ≤ logSlope δ (referenceDepth L x)*
        metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) x :=
      mul_le_mul hs hmin hm.le (logSlope_pos δ (referenceDepth L x) hδ).le
    have h := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg p)
    calc
      1 ≤ (p : ℝ)*c0 := hlarge
      _ = (p : ℝ)*(a0*m) := rfl
      _ ≤ (p : ℝ)*(logSlope δ (referenceDepth L x)*
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) x) := h
      _ = _ := by ring
  have hupper : actualReferenceBeta g L lam δ R p x ≤ (p : ℝ)*C*logSlope δ (referenceDepth L x) := by
    rw [actualReferenceBeta_eq g L lam δ R p hδ hR x]
    have h := mul_le_mul_of_nonneg_left hmax
      (mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ (referenceDepth L x) hδ).le)
    convert h using 1 <;> ring
  have hpwr := radius_gradient_power_uniform_scale_bound δ (referenceDepth L x) T R C
    (actualReferenceBeta g L lam δ R p x) p q hδ hδ1 ht hR.le hC.le
    (le_trans zero_le_one hbeta) hqp hupper
  have hsmall : referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^q ≤ eta := by
    have h : referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^q ≤ R*A := by
      simpa only [referenceRadius,A,mul_assoc] using hpwr
    exact h.trans hRA
  have hone : 1 ≤ (actualReferenceBeta g L lam δ R p x)^q := by
    simpa only [one_pow] using pow_le_pow_left₀ (show 0 ≤ (1 : ℝ) by norm_num) hbeta q
  have hrpos : 0 ≤ referenceRadius δ R p L x := (referenceRadius_pos δ R p L x hδ hR).le
  have hrBeta : referenceRadius δ R p L x ≤
      referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hrpos
  have hr : referenceRadius δ R p L x ≤ eta := hrBeta.trans hsmall
  exact ⟨hbeta,hsmall,hr⟩

/-- A finite uniform all-order log-radius Frechet witness is constructed
from the native genuine softplus estimates at each positive order. -/
theorem exists_fixed_actual_reference_log_radius_uniform_frechet_jets
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ n : ℕ, 1 ≤ n → n ≤ N →
        ‖iteratedFDeriv ℝ n (fun y => Real.log (referenceRadius δ R p L y)) x‖ ≤
          J^n*(actualReferenceBeta g L lam δ R p x)^n := by
  classical
  have hEach (n : ℕ) : ∃ Jn : ℝ, 0 < Jn ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, 1 ≤ n →
        ‖iteratedFDeriv ℝ n (fun y => Real.log (referenceRadius δ R p L y)) x‖ ≤
          Jn*(actualReferenceBeta g L lam δ R p x)^n := by
    by_cases hn : 1 ≤ n
    · obtain ⟨Jn,hJn,hBounds⟩ := exists_dilated_referenceRadius_fixed_uniform_frechet_jet_bound g hg L hL K hK n hn
      refine ⟨Jn,hJn,?_⟩
      intro lam hlam δ hδ hδ1 R hR p hp x hx _hn
      simpa only [actualReferenceBeta] using hBounds lam hlam δ hδ hδ1 R hR p hp x hx
    · refine ⟨1,by norm_num,?_⟩
      intro lam hlam δ hδ hδ1 R hR p hp x hx hn'
      exact False.elim (hn hn')
  choose Jn hJn hBounds using hEach
  let J : ℝ := 1+∑ k ∈ Finset.range (N+1), |Jn k|
  have hJ : 1 ≤ J := by
    have hs : 0 ≤ ∑ k ∈ Finset.range (N+1), |Jn k| := by positivity
    dsimp [J]
    linarith
  refine ⟨J,hJ,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx n hn hN
  have hCoeff : Jn n ≤ J^n := by
    have hsingle : |Jn n| ≤ ∑ k ∈ Finset.range (N+1), |Jn k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (Jn k)) (Finset.mem_range.mpr (by omega))
    have hle : Jn n ≤ J := by
      have h := (le_abs_self (Jn n)).trans hsingle
      dsimp [J]
      linarith
    exact hle.trans (le_self_pow₀ hJ (by omega))
  have hb0 : 0 ≤ actualReferenceBeta g L lam δ R p x :=
    (actualReferenceBeta_pos g hg L lam δ R p hL hδ hR hp x).le
  exact (hBounds n lam hlam δ hδ hδ1 R hR p hp x hx hn).trans
    (mul_le_mul_of_nonneg_right hCoeff (pow_nonneg hb0 n))

/-- The same actual L,p,R,lambda,delta witnesses simultaneously supply all
selected log jets and the requested highest beta power; no h/r application is inferred. -/
theorem exists_fixed_actual_reference_profile_power_and_log_jets
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (N q : ℕ) :
    ∃ J : ℝ, 1 ≤ J ∧ ∃ p0 : ℕ, q ≤ p0 ∧ 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ R : ℝ, 0 < R ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          1 ≤ actualReferenceBeta g L lam δ R p x ∧
          referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^q ≤ eta ∧
          referenceRadius δ R p L x ≤ eta ∧
          (∀ n : ℕ, 1 ≤ n → n ≤ N →
            ‖iteratedFDeriv ℝ n (fun y => Real.log (referenceRadius δ R p L y)) x‖ ≤
              J^n*(actualReferenceBeta g L lam δ R p x)^n) := by
  obtain ⟨J,hJ,hJets⟩ := exists_fixed_actual_reference_log_radius_uniform_frechet_jets g hg L hL K hK N
  obtain ⟨p0,hq,hp02,hProfile⟩ := exists_fixed_actual_reference_beta_power_radius_profile g hg L hL K hK q
  refine ⟨J,hJ,p0,hq,hp02,?_⟩
  intro p hp eta heta heta1
  obtain ⟨R,hR,hBounds⟩ := hProfile p hp eta heta heta1
  refine ⟨R,hR,?_⟩
  intro lam hlam δ hδ hδ1 x hx
  obtain ⟨hb,hpwr,hr⟩ := hBounds lam hlam δ hδ hδ1 x hx
  refine ⟨hb,hpwr,hr,?_⟩
  intro n hn hN
  exact hJets lam hlam δ hδ hδ1 R hR p (by omega) x hx n hn hN

end OAI.AnisotropicCalderon.ActualHigherRadiusProfile
