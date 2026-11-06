import Mathlib

noncomputable section
open MeasureTheory Set
namespace OAI.AnisotropicCalderon.FixedSurfaceFlux

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev Coefficients := R3 → Matrix (Fin 3) (Fin 3) ℝ

def coordinateVector (i : Fin 3) : R3 := EuclideanSpace.single i 1

def secondOrderOperator (a : Coefficients) (b : R3 → Fin 3 → ℝ)
    (c : R3 → ℝ) (f : R3 → ℝ) (y : R3) : ℝ :=
  (∑ i, ∑ j, a y i j *
    fderiv ℝ (fun z => fderiv ℝ f z (coordinateVector j)) y (coordinateVector i)) +
  (∑ i, b y i * fderiv ℝ f y (coordinateVector i)) + c y * f y

/-- Standard regularity and compact-support data for a fixed integration measure.
No conclusion about the parameter integral is included among these fields. -/
structure FixedSurfaceData (μ : Measure R3) (K U V : Set R3)
    (H : R3 → R3 → ℝ) : Prop where
  finite_measure : IsFiniteMeasure μ
  compact_support : IsCompact K
  compact_in_domain : K ⊆ U
  open_space_domain : IsOpen U
  open_parameter_domain : IsOpen V
  mass_off_compact : μ Kᶜ = 0
  joint_smoothness : ContDiffOn ℝ 2 (Function.uncurry H) (U ×ˢ V)

/-- A fixed compactly supported finite-measure integral commutes with the
parameter-only linear second-order operator. Coefficients may be arbitrary. -/
def CommutationStatement : Prop :=
  ∀ (μ : Measure R3) (K U V : Set R3) (H : R3 → R3 → ℝ),
    FixedSurfaceData μ K U V H →
    ∀ (a : Coefficients) (b : R3 → Fin 3 → ℝ) (c : R3 → ℝ),
      ∀ y ∈ V,
        secondOrderOperator a b c (fun z => ∫ x, H x z ∂μ) y =
          ∫ x, secondOrderOperator a b c (H x) y ∂μ

/-- The required harmonicity corollary, with pointwise PDE only on the
compact set carrying the fixed measure. -/
def HarmonicityStatement : Prop :=
  ∀ (μ : Measure R3) (K U V : Set R3) (H : R3 → R3 → ℝ),
    FixedSurfaceData μ K U V H →
    ∀ (a : Coefficients) (b : R3 → Fin 3 → ℝ) (c : R3 → ℝ),
      (∀ x ∈ K, ∀ y ∈ V, secondOrderOperator a b c (H x) y = 0) →
      ∀ y ∈ V,
        secondOrderOperator a b c (fun z => ∫ x, H x z ∂μ) y = 0


open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ae_mem_of_measure_compl {μ : Measure R3} {K : Set R3} (h : μ Kᶜ = 0) :
    ∀ᵐ x ∂μ, x ∈ K :=
  ae_iff.2 h

omit [NormedSpace ℝ E] in
/-- Continuous functions on the compact carrier are integrable. -/
lemma integrable_of_continuousOn {μ : Measure R3} [IsFiniteMeasure μ] {K : Set R3}
    {f : R3 → E} (hK : IsCompact K) (hμ : μ Kᶜ = 0) (hf : ContinuousOn f K) :
    Integrable f μ := by
  have h := hf.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_mem_of_measure_compl hμ)] at h

lemma continuousOn_slice {F : Type*} [TopologicalSpace F] {U V K : Set R3}
    {g : R3 → R3 → F} (hg : ContinuousOn (Function.uncurry g) (U ×ˢ V)) (hKU : K ⊆ U)
    {z : R3} (hz : z ∈ V) : ContinuousOn (fun x => g x z) K :=
  hg.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hx => ⟨hKU hx, hz⟩)

/-- The partial derivative in the second variable is the joint derivative composed
with the second inclusion. -/
lemma hasFDerivAt_partial {U V : Set R3} {f : R3 → R3 → E} {m : WithTop ℕ∞}
    (hf : ContDiffOn ℝ m (Function.uncurry f) (U ×ˢ V)) (hm : 1 ≤ m)
    (hU : IsOpen U) (hV : IsOpen V) {x z : R3} (hx : x ∈ U) (hz : z ∈ V) :
    HasFDerivAt (f x) ((fderiv ℝ (Function.uncurry f) (x, z)).comp
      (ContinuousLinearMap.inr ℝ R3 R3)) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (x, z) :=
    (hf.differentiableOn (lt_of_lt_of_le zero_lt_one hm).ne').differentiableAt
      ((hU.prod hV).mem_nhds ⟨hx, hz⟩)
  exact hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right x z)

lemma contDiffOn_partial {U V : Set R3} {f : R3 → R3 → E} {m n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ m (Function.uncurry f) (U ×ˢ V)) (hnm : n + 1 ≤ m)
    (hU : IsOpen U) (hV : IsOpen V) :
    ContDiffOn ℝ n (Function.uncurry fun x z => fderiv ℝ (f x) z) (U ×ˢ V) := by
  have h1 : ContDiffOn ℝ n (fun p : R3 × R3 => (fderiv ℝ (Function.uncurry f) p).comp
      (ContinuousLinearMap.inr ℝ R3 R3)) (U ×ˢ V) :=
    (hf.fderiv_of_isOpen (hU.prod hV) hnm).clm_comp contDiffOn_const
  refine h1.congr ?_
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  exact (hasFDerivAt_partial hf (le_trans le_add_self hnm) hU hV hx hz).fderiv

/-- Differentiation under the integral sign, with domination from compactness. -/
lemma hasFDerivAt_integral {μ : Measure R3} [IsFiniteMeasure μ] {K U V : Set R3}
    {f : R3 → R3 → E} {m : WithTop ℕ∞}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U) (hV : IsOpen V) (hμ : μ Kᶜ = 0)
    (hf : ContDiffOn ℝ m (Function.uncurry f) (U ×ˢ V)) (hm : 1 ≤ m)
    {y : R3} (hy : y ∈ V) :
    HasFDerivAt (fun z => ∫ x, f x z ∂μ) (∫ x, fderiv ℝ (f x) y ∂μ) y := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV y hy
  have hsV : Metric.closedBall y (r / 2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrV
  have hs : Metric.closedBall y (r / 2) ∈ 𝓝 y := Metric.closedBall_mem_nhds y (by linarith)
  have hcont1 : ContinuousOn (Function.uncurry fun x z => fderiv ℝ (f x) z) (U ×ˢ V) :=
    (contDiffOn_partial hf (n := 0) (by simpa using hm) hU hV).continuousOn
  have hcont0 : ContinuousOn (Function.uncurry f) (U ×ˢ V) := hf.continuousOn
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall y (r / 2))).exists_bound_of_continuousOn
    (hcont1.mono (prod_mono hKU hsV))
  have hKae := ae_mem_of_measure_compl hμ
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun z x => f x z)
    (F' := fun z x => fderiv ℝ (f x) z) (bound := fun _ => C) hs ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hs] with z hz
    exact (integrable_of_continuousOn hK hμ
      (continuousOn_slice hcont0 hKU (hsV hz))).aestronglyMeasurable
  · exact integrable_of_continuousOn hK hμ (continuousOn_slice hcont0 hKU hy)
  · exact (integrable_of_continuousOn hK hμ
      (continuousOn_slice hcont1 hKU hy)).aestronglyMeasurable
  · filter_upwards [hKae] with x hx z hz
    exact hC (x, z) ⟨hx, hz⟩
  · exact integrable_const C
  · filter_upwards [hKae] with x hx z hz
    exact (hasFDerivAt_partial hf hm hU hV (hKU hx) (hsV hz)).differentiableAt.hasFDerivAt

-- Prove these exact two frozen statements. Helper lemmas belong in this file.
theorem integral_secondOrder_commute : CommutationStatement := by
  intro μ K U V H D a b c y hy
  have := D.finite_measure
  have hK := D.compact_support
  have hKU := D.compact_in_domain
  have hU := D.open_space_domain
  have hV := D.open_parameter_domain
  have hμ := D.mass_off_compact
  have hH := D.joint_smoothness
  have hH1 : ContDiffOn ℝ 1 (Function.uncurry fun x z => fderiv ℝ (H x) z) (U ×ˢ V) :=
    contDiffOn_partial hH (by norm_num) hU hV
  have hG : ∀ j, ContDiffOn ℝ 1
      (Function.uncurry fun x z => fderiv ℝ (H x) z (coordinateVector j)) (U ×ˢ V) :=
    fun j => hH1.clm_apply contDiffOn_const
  have hG0 : ∀ j, ContinuousOn (Function.uncurry fun x z =>
      fderiv ℝ (fun w => fderiv ℝ (H x) w (coordinateVector j)) z) (U ×ˢ V) :=
    fun j => (contDiffOn_partial (hG j) (n := 0) (by norm_num) hU hV).continuousOn
  have i0 : Integrable (fun x => H x y) μ :=
    integrable_of_continuousOn hK hμ (continuousOn_slice hH.continuousOn hKU hy)
  have i1 : ∀ z ∈ V, Integrable (fun x => fderiv ℝ (H x) z) μ := fun z hz =>
    integrable_of_continuousOn hK hμ (continuousOn_slice hH1.continuousOn hKU hz)
  have i1' : ∀ i, Integrable (fun x => fderiv ℝ (H x) y (coordinateVector i)) μ := fun i =>
    integrable_of_continuousOn hK hμ
      ((continuousOn_slice hH1.continuousOn hKU hy).clm_apply continuousOn_const)
  have i2 : ∀ j, Integrable
      (fun x => fderiv ℝ (fun w => fderiv ℝ (H x) w (coordinateVector j)) y) μ := fun j =>
    integrable_of_continuousOn hK hμ (continuousOn_slice (hG0 j) hKU hy)
  have i2' : ∀ i j, Integrable (fun x => fderiv ℝ
      (fun w => fderiv ℝ (H x) w (coordinateVector j)) y (coordinateVector i)) μ :=
    fun i j => integrable_of_continuousOn hK hμ
      ((continuousOn_slice (hG0 j) hKU hy).clm_apply continuousOn_const)
  have d1 : ∀ z ∈ V, ∀ v, fderiv ℝ (fun w => ∫ x, H x w ∂μ) z v =
      ∫ x, fderiv ℝ (H x) z v ∂μ := by
    intro z hz v
    rw [(hasFDerivAt_integral hK hKU hU hV hμ hH (by norm_num) hz).fderiv,
      ContinuousLinearMap.integral_apply (i1 z hz)]
  have d2 : ∀ i j, fderiv ℝ (fun z => fderiv ℝ (fun w => ∫ x, H x w ∂μ) z (coordinateVector j))
      y (coordinateVector i) =
      ∫ x, fderiv ℝ (fun z => fderiv ℝ (H x) z (coordinateVector j)) y (coordinateVector i) ∂μ := by
    intro i j
    have heq : (fun z => fderiv ℝ (fun w => ∫ x, H x w ∂μ) z (coordinateVector j)) =ᶠ[𝓝 y]
        fun z => ∫ x, fderiv ℝ (H x) z (coordinateVector j) ∂μ := by
      filter_upwards [hV.mem_nhds hy] with z hz using d1 z hz (coordinateVector j)
    rw [heq.fderiv_eq, (hasFDerivAt_integral hK hKU hU hV hμ (hG j) le_rfl hy).fderiv,
      ContinuousLinearMap.integral_apply (i2 j)]
  have hA : Integrable (fun x => ∑ i, ∑ j, a y i j *
      fderiv ℝ (fun z => fderiv ℝ (H x) z (coordinateVector j)) y (coordinateVector i)) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (i2' i j).const_mul _
  have hB : Integrable (fun x => ∑ i, b y i * fderiv ℝ (H x) y (coordinateVector i)) μ :=
    integrable_finsetSum _ fun i _ => (i1' i).const_mul _
  have hAB : Integrable (fun x => (∑ i, ∑ j, a y i j *
      fderiv ℝ (fun z => fderiv ℝ (H x) z (coordinateVector j)) y (coordinateVector i)) +
      ∑ i, b y i * fderiv ℝ (H x) y (coordinateVector i)) μ := hA.add hB
  unfold secondOrderOperator
  simp_rw [d2, d1 y hy]
  rw [integral_add hAB (i0.const_mul _), integral_add hA hB, integral_const_mul]
  congr 2
  · refine Eq.symm ((integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (i2' i j).const_mul (a y i j)).trans ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (integral_finsetSum _ fun j _ => (i2' i j).const_mul (a y i j)).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_const_mul _ _
  · refine Eq.symm ((integral_finsetSum _ fun i _ => (i1' i).const_mul (b y i)).trans ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_const_mul _ _

theorem integral_secondOrder_harmonic : HarmonicityStatement := by
  intro μ K U V H D a b c h y hy
  rw [integral_secondOrder_commute μ K U V H D a b c y hy]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_mem_of_measure_compl D.mass_off_compact] with x hx
  exact h x hx y hy


end OAI.AnisotropicCalderon.FixedSurfaceFlux
