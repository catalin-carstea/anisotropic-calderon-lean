import Calderon.FixedParameterProfilePullback
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.FixedParameterProfileBudgets
open FixedParameterProfilePullback ConformalDepth ActualAngularHighDraft ActualScalarPrincipalAdjoint
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)

/-- The exact original fixed-q parameter derivative uses only the first two radius jets. -/
theorem fderiv_radiusProfileMap (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (x : R3) :
    fderiv ℝ (radiusProfileMap q R) x =
      ((0 : R3 →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ R3).prod (fderiv ℝ R x))).prod
        (fderiv ℝ (fderiv ℝ R) x) := by
  have hr := (hR.differentiable (by simp) x).hasFDerivAt
  have hd := ((hR.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  exact (((hasFDerivAt_const q x).prodMk ((hasFDerivAt_id x).prodMk hr)).prodMk hd).fderiv

/-- Canonical product norms give an honest bound for the physical parameter derivative. -/
theorem norm_fderiv_radiusProfileMap_le (q : ℝ) (R : R3 → ℝ)
    (hR : ContDiff ℝ ∞ R) (x : R3) :
    ‖fderiv ℝ (radiusProfileMap q R) x‖ ≤
      1+‖fderiv ℝ R x‖+‖fderiv ℝ (fderiv ℝ R) x‖ := by
  rw [fderiv_radiusProfileMap q R hR x]
  simp only [ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,ContinuousLinearMap.norm_id]
  refine max_le (max_le ?_ (max_le ?_ ?_)) ?_ <;>
    linarith only [norm_nonneg (fderiv ℝ R x),norm_nonneg (fderiv ℝ (fderiv ℝ R) x)]

/-- Select the physical profile-map derivative budget before all final profiles. -/
theorem exists_uniform_higherSParam_derivative_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ KT : ℝ, 0 < KT ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      1 ≤ ReferenceWeightedApproximation.actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(ReferenceWeightedApproximation.actualReferenceBeta g L q dr Ar p x)^2 ≤ eps →
      ‖fderiv ℝ (ActualHigherSFormation.higherSParam L dr Ar p q) x‖ ≤ KT := by
  obtain ⟨J1,hJ1,hjet1⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds g hg L hL K hK 1
  obtain ⟨J2,hJ2,hjet2⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds g hg L hL K hK 2
  refine ⟨1+J1+J2,by positivity,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eps heps heps1 x hx hb hs
  let r := referenceRadius dr Ar p L x
  let beta := ReferenceWeightedApproximation.actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hb12 : beta ≤ beta^2 := by nlinarith only [hb]
  have hrBE : r*beta ≤ eps := (mul_le_mul_of_nonneg_left hb12 hr.le).trans hs
  have hr := contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have h1 : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤ J1*r*beta := by
    simpa only [norm_iteratedFDeriv_one,pow_one,r,beta,ReferenceWeightedApproximation.actualReferenceBeta]
      using (hjet1 q hq dr hdr hdr1 Ar hAr p hp x hx).1
  have h2 : ‖fderiv ℝ (fderiv ℝ (referenceRadius dr Ar p L)) x‖ ≤ J2*r*beta^2 := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    simpa only [r,beta,ReferenceWeightedApproximation.actualReferenceBeta]
      using (hjet2 q hq dr hdr hdr1 Ar hAr p hp x hx).1
  have h1J : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤ J1 := by
    calc
      _ ≤ J1*r*beta := h1
      _ = J1*(r*beta) := mul_assoc _ _ _
      _ ≤ J1*eps := mul_le_mul_of_nonneg_left hrBE hJ1.le
      _ ≤ J1*1 := mul_le_mul_of_nonneg_left heps1 hJ1.le
      _ = J1 := mul_one _
  have h2J : ‖fderiv ℝ (fderiv ℝ (referenceRadius dr Ar p L)) x‖ ≤ J2 := by
    calc
      _ ≤ J2*r*beta^2 := h2
      _ = J2*(r*beta^2) := mul_assoc _ _ _
      _ ≤ J2*eps := mul_le_mul_of_nonneg_left hs hJ2.le
      _ ≤ J2*1 := mul_le_mul_of_nonneg_left heps1 hJ2.le
      _ = J2 := mul_one _
  exact (norm_fderiv_radiusProfileMap_le q (referenceRadius dr Ar p L) hr x).trans
    (by linarith only [h1J,h2J])

section Generic
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
/-- Only true within-jet caps and a true pullback neighborhood enter the physical cap transport. -/
theorem physical_pullback_first_caps (f : P → V) (T : R3 → P) (K : Set P) (x : R3)
    (hf : ContDiffWithinAt ℝ ∞ f K (T x)) (hT : ContDiffAt ℝ ∞ T x)
    (hmem : ∀ᶠ y in 𝓝 x, T y ∈ K) (hU : UniqueDiffWithinAt ℝ K (T x))
    (M : ℝ) (h0 : ‖iteratedFDerivWithin ℝ 0 f K (T x)‖ ≤ M)
    (h1 : ‖iteratedFDerivWithin ℝ 1 f K (T x)‖ ≤ M) :
    ContDiffAt ℝ ∞ (fun y => f (T y)) x ∧ ‖f (T x)‖ ≤ M ∧
      ‖fderiv ℝ (fun y => f (T y)) x‖ ≤ M*‖fderiv ℝ T x‖ := by
  have h0' : ‖f (T x)‖ ≤ M := by simpa only [norm_iteratedFDerivWithin_zero] using h0
  have h1' : ‖fderivWithin ℝ f K (T x)‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_one f hU] using h1
  exact ⟨contDiffAt_comp_of_eventually_mem f T K x hf hT hmem,h0',
    (norm_fderiv_comp_of_eventually_mem f T K x hf hT hmem).trans
      (mul_le_mul_of_nonneg_right h1' (norm_nonneg _))⟩
end Generic

/-- Actual fixed-q coefficient-family caps with the derivative constant chosen before profiles. -/
theorem exists_higherSParam_family_first_caps {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (y0 : R3) (rho d : ℝ) (hrho : 0 < rho) (hd : 0 < d)
    (K : Set R3) (hK : IsCompact K) (f : Tpar → V)
    (hf : ContDiffOn ℝ ∞ f (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)))
    (M : ℝ) (hM : 0 ≤ M)
    (hcap : ∀ n : ℕ, n ≤ 1 → ∀ t ∈ Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1),
      ‖iteratedFDerivWithin ℝ n f (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)) t‖ ≤ M) :
    ∃ KT : ℝ, 0 < KT ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      1 ≤ ReferenceWeightedApproximation.actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(ReferenceWeightedApproximation.actualReferenceBeta g L q dr Ar p x)^2 ≤ eps →
      StrictPhysicalProfileGuard y0 rho d q (referenceRadius dr Ar p L) x →
      ContDiffAt ℝ ∞ (fun y => f (ActualHigherSFormation.higherSParam L dr Ar p q y)) x ∧
      ‖f (ActualHigherSFormation.higherSParam L dr Ar p q x)‖ ≤ M ∧
      ‖fderiv ℝ (fun y => f (ActualHigherSFormation.higherSParam L dr Ar p q y)) x‖ ≤ M*KT := by
  obtain ⟨KT,hKT,hTcap⟩ := exists_uniform_higherSParam_derivative_bound g hg L hL K hK
  refine ⟨KT,hKT,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eps heps heps1 x hx hb hs hguard
  have hmem := higherSParam_eventually_mem y0 rho d L dr Ar q p hdr hAr x hguard
  have hxT := hmem.self_of_nhds
  have hT : ContDiffAt ℝ ∞ (ActualHigherSFormation.higherSParam L dr Ar p q) x :=
    (contDiff_radiusProfileMap q (referenceRadius dr Ar p L)
      (contDiff_referenceRadius_actual dr Ar p L hdr hAr)).contDiffAt
  have hU : UniqueDiffOn ℝ (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)) :=
    (uniqueDiffOn_commonRoom y0 rho hrho hd).prod
      (uniqueDiffOn_convex (convex_closedBall _ _)
        ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  have h := physical_pullback_first_caps f _ _ x (hf _ hxT) hT hmem (hU _ hxT) M
    (hcap 0 (by omega) _ hxT) (hcap 1 (by omega) _ hxT)
  exact ⟨h.1,h.2.1,h.2.2.trans
    (mul_le_mul_of_nonneg_left (hTcap q hq dr hdr hdr1 Ar hAr p hp eps heps heps1 x hx hb hs) hM)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.FixedParameterProfileBudgets
