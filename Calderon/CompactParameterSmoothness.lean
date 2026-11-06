import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology
universe u
namespace OAI.AnisotropicCalderon.CompactParameterSmoothness

variable {K H E : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def applyContinuousFamily (A : C(K,H →L[ℝ] E)) (h : H) : C(K,E) :=
  ⟨fun theta => A theta h,A.continuous.clm_apply continuous_const⟩

lemma norm_applyContinuousFamily_le (A : C(K,H →L[ℝ] E)) (h : H) :
    ‖applyContinuousFamily A h‖ ≤ ‖A‖ * ‖h‖ := by
  apply (ContinuousMap.norm_le (applyContinuousFamily A h) (mul_nonneg (norm_nonneg A) (norm_nonneg h))).mpr
  intro theta
  exact (A theta).le_opNorm h |>.trans
    (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm theta) (norm_nonneg h))

def transposeAt (A : C(K,H →L[ℝ] E)) : H →L[ℝ] C(K,E) :=
  ({toFun := applyContinuousFamily A
    map_add' := by intros; ext; simp [applyContinuousFamily]
    map_smul' := by intros; ext; simp [applyContinuousFamily]} : H →ₗ[ℝ] C(K,E)).mkContinuous
      ‖A‖ (norm_applyContinuousFamily_le A)

lemma transposeAt_apply (A : C(K,H →L[ℝ] E)) (h : H) (theta : K) :
    transposeAt A h theta = A theta h := rfl

lemma norm_transposeAt_le (A : C(K,H →L[ℝ] E)) : ‖transposeAt A‖ ≤ ‖A‖ :=
  (transposeAt A).opNorm_le_bound (norm_nonneg A) (norm_applyContinuousFamily_le A)

def transposeContinuousFamily :
    C(K,H →L[ℝ] E) →L[ℝ] (H →L[ℝ] C(K,E)) := by
  let T : C(K,H →L[ℝ] E) →ₗ[ℝ] (H →L[ℝ] C(K,E)) :=
    { toFun := fun A => transposeAt (K := K) (H := H) (E := E) A
      map_add' := by intros; ext; simp [transposeAt_apply]
      map_smul' := by intros; ext; simp [transposeAt_apply] }
  have hb : ∀ A : C(K,H →L[ℝ] E), ‖T A‖ ≤ 1 * ‖A‖ := by
    intro A
    change ‖transposeAt A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using norm_transposeAt_le A
  exact LinearMap.mkContinuous (E := C(K,H →L[ℝ] E)) (F := H →L[ℝ] C(K,E)) T 1 hb

lemma transposeContinuousFamily_apply (A : C(K,H →L[ℝ] E)) (h : H) (theta : K) :
    transposeContinuousFamily A h theta = A theta h := rfl

lemma norm_transposeContinuousFamily_le :
    @norm (C(K,H →L[ℝ] E) →L[ℝ] (H →L[ℝ] C(K,E)))
      (ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
        (E := C(K,H →L[ℝ] E)) (F := H →L[ℝ] C(K,E)))
      (transposeContinuousFamily (K := K) (H := H) (E := E)) ≤ 1 := by
  unfold transposeContinuousFamily
  exact LinearMap.mkContinuous_norm_le (𝕜 := ℝ) (𝕜₂ := ℝ)
    (σ₁₂ := RingHom.id ℝ) (E := C(K,H →L[ℝ] E)) (F := H →L[ℝ] C(K,E))
    _ zero_le_one _

theorem hasFDerivAt_of_uniform_slice_derivative
    (F : H → C(K,E)) (D : H → C(K,H →L[ℝ] E)) (x : H)
    (hD : ContinuousAt D x)
    (hFD : ∀ y theta, HasFDerivAt (fun z => F z theta) (D y theta) y) :
    HasFDerivAt F (transposeContinuousFamily (D x)) x := by
  apply HasFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro eps heps
  have hev : ∀ᶠ y in 𝓝 x, ‖D y - D x‖ < eps := by
    have hs : ContinuousAt (fun y : H => D y - D x) x := hD.sub continuousAt_const
    have hn0 : ContinuousAt (fun A : C(K,H →L[ℝ] E) => ‖A‖) (D x - D x) :=
      (continuous_norm (E := C(K,H →L[ℝ] E))).continuousAt
    have hz : ‖(0 : C(K,H →L[ℝ] E))‖ = 0 := by
      change dist (0 : C(K,H →L[ℝ] E)) 0 = 0
      exact dist_self _
    have hn : Tendsto (fun y => ‖D y - D x‖) (𝓝 x) (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, sub_self, hz] using
        (hn0.comp (f := fun y : H => D y - D x) (x := x) hs).tendsto
    exact hn.eventually (Iio_mem_nhds heps)
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp hev
  filter_upwards [Metric.ball_mem_nhds x hdelta] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg heps.le (norm_nonneg _))).mpr
  intro theta
  let g : H → E := fun z => F z theta - F x theta - D x theta (z-x)
  have hgd (z : H) : HasFDerivAt g (D z theta - D x theta) z := by
    have hh : HasFDerivAt (fun w => D x theta (w-x)) (D x theta) z := by
      simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using
        (D x theta).hasFDerivAt.comp z (hasFDerivAt_id z |>.sub_const x)
    change HasFDerivAt ((fun w => F w theta - F x theta) -
      fun w => D x theta (w-x)) (D z theta - D x theta) z
    exact ((hFD z theta).sub_const (F x theta)).sub hh
  have hbound (z : H) (hz : z ∈ Metric.ball x delta) : ‖D z theta - D x theta‖ ≤ eps := by
    exact ((D z - D x).norm_coe_le_norm theta).trans (hball hz).le
  have hg := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hgd z).hasFDerivWithinAt) hbound (convex_ball x delta)
    (Metric.mem_ball_self hdelta) hy
  simpa [g,transposeContinuousFamily_apply,ContinuousMap.sub_apply] using hg

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

def compactPullback (g : H × V → E) (hg : Continuous g) (v : C(K,V)) : H → C(K,E) :=
  fun x => ⟨fun theta => g (x,v theta),hg.comp (continuous_const.prodMk v.continuous)⟩

lemma compactPullback_apply (g : H × V → E) (hg : Continuous g) (v : C(K,V))
    (x : H) (theta : K) : compactPullback g hg v x theta = g (x,v theta) := rfl

lemma continuous_compactPullback (g : H × V → E) (hg : Continuous g) (v : C(K,V)) :
    Continuous (compactPullback g hg v) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hg.comp (continuous_fst.prodMk (v.continuous.comp continuous_snd))

def basePartial (g : H × V → E) (z : H × V) : H →L[ℝ] E :=
  (fderiv ℝ g z).comp (ContinuousLinearMap.inl ℝ H V)

lemma hasFDerivAt_base_slice (g : H × V → E) (hg : Differentiable ℝ g)
    (y : H) (v : V) : HasFDerivAt (fun x => g (x,v)) (basePartial g (y,v)) y :=
  (hg (y,v)).hasFDerivAt.comp y (hasFDerivAt_prodMk_left y v)

lemma contDiff_basePartial (n : ℕ) (g : H × V → E) (hg : ContDiff ℝ (n+1) g) :
    ContDiff ℝ n (basePartial g) := by
  exact ((ContinuousLinearMap.compL ℝ H (H × V) E).flip
    (ContinuousLinearMap.inl ℝ H V)).contDiff.comp (hg.fderiv_right (by simp))

theorem contDiff_compactPullback (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (g : H × V → E) (hg : ContDiff ℝ n g) (v : C(K,V)),
      ContDiff ℝ n (compactPullback g hg.continuous v) := by
  induction n with
  | zero =>
      intro E _ _ g hg v
      exact contDiff_zero.mpr (continuous_compactPullback g hg.continuous v)
  | succ n ih =>
      intro E _ _ g hg v
      have hp := contDiff_basePartial n g hg
      have hDC := ih (H →L[ℝ] E) (basePartial g) hp v
      have hT : ContDiff ℝ n (transposeContinuousFamily (K := K) (H := H) (E := E)) :=
        ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(K,H →L[ℝ] E))
          (F := H →L[ℝ] C(K,E)) (n := n)
          (transposeContinuousFamily (K := K) (H := H) (E := E))
      refine contDiff_succ_iff_hasFDerivAt.mpr
        ⟨fun x => transposeContinuousFamily (compactPullback (basePartial g) hp.continuous v x),
          hT.comp hDC,?_⟩
      intro x
      apply hasFDerivAt_of_uniform_slice_derivative
        (compactPullback g hg.continuous v)
        (compactPullback (basePartial g) hp.continuous v) x hDC.continuous.continuousAt
      intro y theta
      exact hasFDerivAt_base_slice g (hg.differentiable (by simp)) y (v theta)

theorem contDiff_infty_compactPullback (g : H × V → E) (hg : ContDiff ℝ ∞ g)
    (v : C(K,V)) : ContDiff ℝ ∞ (compactPullback g hg.continuous v) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n _
  exact contDiff_compactPullback n E g (hg.of_le (by simp)) v

end OAI.AnisotropicCalderon.CompactParameterSmoothness
