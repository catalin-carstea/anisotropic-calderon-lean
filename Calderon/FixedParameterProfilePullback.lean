import Calderon.ActualHigherSFormation
import Calderon.ActualScalarPrincipalAdjoint
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.FixedParameterProfilePullback
open ActualAngularHighDraft PrincipalCommutator ActualScalarPrincipalAdjoint ConformalDepth
section Generic
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
/-- Smooth physical pullback from a within-smooth family and a proved base neighborhood guard. -/
theorem contDiffAt_comp_of_eventually_mem (f : P → V) (T : R3 → P) (K : Set P) (x : R3)
    (hf : ContDiffWithinAt ℝ ∞ f K (T x)) (hT : ContDiffAt ℝ ∞ T x)
    (hmem : ∀ᶠ y in 𝓝 x, T y ∈ K) : ContDiffAt ℝ ∞ (fun y => f (T y)) x := by
  have hh := hf.comp x (hT.contDiffWithinAt (s := T ⁻¹' K)) (fun _ hy => hy)
  exact hh.contDiffAt hmem

/-- Exact first derivative of that physical pullback, with the original within derivative. -/
theorem fderiv_comp_of_eventually_mem (f : P → V) (T : R3 → P) (K : Set P) (x : R3)
    (hf : ContDiffWithinAt ℝ ∞ f K (T x)) (hT : ContDiffAt ℝ ∞ T x)
    (hmem : ∀ᶠ y in 𝓝 x, T y ∈ K) :
    fderiv ℝ (fun y => f (T y)) x = (fderivWithin ℝ f K (T x)).comp (fderiv ℝ T x) := by
  have hg := (hf.differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hh := hg.comp x ((hT.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt (s := T ⁻¹' K))
    (fun _ hy => hy)
  exact (hh.hasFDerivAt hmem).fderiv

theorem norm_fderiv_comp_of_eventually_mem (f : P → V) (T : R3 → P) (K : Set P) (x : R3)
    (hf : ContDiffWithinAt ℝ ∞ f K (T x)) (hT : ContDiffAt ℝ ∞ T x)
    (hmem : ∀ᶠ y in 𝓝 x, T y ∈ K) :
    ‖fderiv ℝ (fun y => f (T y)) x‖ ≤ ‖fderivWithin ℝ f K (T x)‖*‖fderiv ℝ T x‖ := by
  rw [fderiv_comp_of_eventually_mem f T K x hf hT hmem]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- Only a proved parameter-neighborhood pullback is used to transport a family graph. -/
theorem comp_eventuallyEq_of_eqOn (f g : P → V) (T : R3 → P) (K : Set P) (x : R3)
    (he : Set.EqOn f g K) (hmem : ∀ᶠ y in 𝓝 x, T y ∈ K) :
    (fun y => f (T y)) =ᶠ[𝓝 x] (fun y => g (T y)) := hmem.mono (fun y hy => he hy)
end Generic
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)

def radiusProfileMap (q : ℝ) (R : R3 → ℝ) (x : R3) : Tpar := ((q,(x,R x)),fderiv ℝ R x)

def StrictPhysicalProfileGuard (y0 : R3) (rho d q : ℝ) (R : R3 → ℝ) (x : R3) : Prop :=
  q ∈ Icc (0 : ℝ) 1 ∧ x ∈ ball y0 rho ∧ R x ∈ Ioo (-d) d ∧ fderiv ℝ R x ∈ ball 0 1

/-- Fixed q may lie at either endpoint; strictness is needed only in the varying physical variables. -/
theorem eventually_radiusProfileMap_mem (y0 : R3) (rho d q : ℝ) (R : R3 → ℝ)
    (hR : ContDiff ℝ ∞ R) (x : R3) (hx : StrictPhysicalProfileGuard y0 rho d q R x) :
    ∀ᶠ y in 𝓝 x, radiusProfileMap q R y ∈
      Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1) := by
  have hY : ∀ᶠ y in 𝓝 x, y ∈ ball y0 rho := isOpen_ball.mem_nhds hx.2.1
  have hr : ∀ᶠ y in 𝓝 x, R y ∈ Ioo (-d) d := hR.continuous.continuousAt.preimage_mem_nhds
    (isOpen_Ioo.mem_nhds hx.2.2.1)
  have hd : ∀ᶠ y in 𝓝 x, fderiv ℝ R y ∈ ball 0 1 :=
    (hR.fderiv_right (m := ∞) (by simp)).continuous.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds hx.2.2.2)
  filter_upwards [hY,hr,hd] with y hy hry hdy
  exact ⟨⟨hx.1,ball_subset_closedBall hy,⟨hry.1.le,hry.2.le⟩⟩,ball_subset_closedBall hdy⟩

lemma contDiff_radiusProfileMap (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (radiusProfileMap q R) :=
  (contDiff_const.prodMk (contDiff_id.prodMk hR)).prodMk (hR.fderiv_right (m := ∞) (by simp))

/-- Actual higherSParam inherits the same honest local guard and smoothness. -/
theorem higherSParam_eventually_mem (y0 : R3) (rho d L dr Ar q : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (x : R3)
    (hx : StrictPhysicalProfileGuard y0 rho d q (referenceRadius dr Ar p L) x) :
    ∀ᶠ y in 𝓝 x, ActualHigherSFormation.higherSParam L dr Ar p q y ∈
      Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1) :=
  eventually_radiusProfileMap_mem y0 rho d q (referenceRadius dr Ar p L)
    (contDiff_referenceRadius_actual dr Ar p L hdr hAr) x hx

/-- Original fixed-q profile pullback: actual smoothness and its exact first-derivative estimate. -/
theorem higherSParam_pullback {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Tpar → V) (y0 : R3) (rho d L dr Ar q : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (x : R3)
    (hf : ContDiffOn ℝ ∞ f (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)))
    (hx : StrictPhysicalProfileGuard y0 rho d q (referenceRadius dr Ar p L) x) :
    ContDiffAt ℝ ∞ (fun y => f (ActualHigherSFormation.higherSParam L dr Ar p q y)) x ∧
    ‖fderiv ℝ (fun y => f (ActualHigherSFormation.higherSParam L dr Ar p q y)) x‖ ≤
      ‖fderivWithin ℝ f (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1))
        (ActualHigherSFormation.higherSParam L dr Ar p q x)‖*
      ‖fderiv ℝ (ActualHigherSFormation.higherSParam L dr Ar p q) x‖ := by
  have hmem := higherSParam_eventually_mem y0 rho d L dr Ar q p hdr hAr x hx
  have hT : ContDiffAt ℝ ∞ (ActualHigherSFormation.higherSParam L dr Ar p q) x :=
    (contDiff_radiusProfileMap q (referenceRadius dr Ar p L)
      (contDiff_referenceRadius_actual dr Ar p L hdr hAr)).contDiffAt
  exact ⟨contDiffAt_comp_of_eventually_mem f _ _ x (hf _ hmem.self_of_nhds) hT hmem,
    norm_fderiv_comp_of_eventually_mem f _ _ x (hf _ hmem.self_of_nhds) hT hmem⟩
/-- Original radius smallness gives the strict varying-coordinate guard uniformly before profiles. -/
theorem exists_uniform_strict_higherSParam_guard (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (y0 : R3) (rho d : ℝ) (hd : 0 < d)
    (K : Set R3) (hK : IsCompact K) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 → ∀ x ∈ K,
      x ∈ ball y0 rho →
      1 ≤ ReferenceWeightedApproximation.actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(ReferenceWeightedApproximation.actualReferenceBeta g L q dr Ar p x)^2 ≤ eps →
      StrictPhysicalProfileGuard y0 rho d q (referenceRadius dr Ar p L) x := by
  obtain ⟨C,hC,hJet⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds g hg L hL K hK 1
  let eps0 : ℝ := min 1 (min (d/2) (1/(2*(C+1))))
  have he0 : 0 < eps0 := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have he1 : eps0 ≤ 1 := min_le_left _ _
  have heD : eps0 ≤ d/2 := (min_le_right _ _).trans (min_le_left _ _)
  have heC : eps0 ≤ 1/(2*(C+1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨eps0,he0,he1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eps heps heps0 x hx hxBall hb hs
  let r := referenceRadius dr Ar p L x
  let beta := ReferenceWeightedApproximation.actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hb2 : 1 ≤ beta^2 := by nlinarith only [hb]
  have hb12 : beta ≤ beta^2 := by nlinarith only [hb]
  have hrE0 : r ≤ r*beta^2 := by
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left hb2 hr.le)
  have hrE : r ≤ eps := hrE0.trans hs
  have hrLo : -d < r := (show -d < 0 by linarith only [hd]).trans hr
  have hrHi : r < d := (hrE.trans (heps0.trans heD)).trans_lt (by linarith only [hd])
  have hrBE : r*beta ≤ eps := (mul_le_mul_of_nonneg_left hb12 hr.le).trans hs
  have hDn : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤ C*eps := by
    have hj := (hJet q hq dr hdr hdr1 Ar hAr p hp x hx).1
    have hj' : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ ≤ C*r*beta := by
      simpa only [norm_iteratedFDeriv_one,pow_one,r,beta,
        ReferenceWeightedApproximation.actualReferenceBeta] using hj
    exact hj'.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrBE hC.le)
  have hCsmall : C*(1/(2*(C+1))) < 1 := by
    calc
      _ = C/(2*(C+1)) := by ring
      _ < 1 := (div_lt_one (by positivity)).2 (by linarith only [hC])
  have hDn1 : ‖fderiv ℝ (referenceRadius dr Ar p L) x‖ < 1 :=
    (hDn.trans (mul_le_mul_of_nonneg_left (heps0.trans heC) hC.le)).trans_lt hCsmall
  refine ⟨hq,hxBall,⟨hrLo,hrHi⟩,?_⟩
  simpa only [mem_ball,dist_zero_right] using hDn1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.FixedParameterProfilePullback
