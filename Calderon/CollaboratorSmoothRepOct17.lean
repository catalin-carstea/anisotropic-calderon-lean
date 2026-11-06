import Calderon.CollaboratorLocalSobolevRawTwoJetBoundOct17
import TauCeti.Analysis.Sobolev.Wkp.LocalApproximation
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-! Smooth representatives of functions that are locally in every `W^{k,2}` (helper for
tasks 07–09).

Route: on a ball `ball x ρ`, Tau Ceti's local approximation gives test functions converging to
the `W^{k+2,2}` datum in `W^{k+2,2}(ball x (ρ/2))`. The pointwise Sobolev bound from
`LocalSobolevRawTwoJetBound` (translated to arbitrary centres) makes their derivatives through
order `k` uniformly Cauchy on `ball x (ρ/4)`, so the uniform limit is `C^k` there and equals the
function almost everywhere. Continuous representatives agree on overlaps, which glues the local
smooth representatives along a countable cover. -/

set_option maxSynthPendingDepth 10

noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.Regularity.SmoothRepAux
open TauCeti
open Filter Topology

theorem norm_iteratedFDeriv_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h : E → F) :
    ∀ (n l : ℕ) (x : E), ‖iteratedFDeriv ℝ l (iteratedFDeriv ℝ n h) x‖ =
      ‖iteratedFDeriv ℝ (l + n) h x‖ := by
  intro n
  induction n with
  | zero =>
    intro l x
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.norm_iteratedFDeriv_comp_left h x l
  | succ n ih =>
    intro l x
    rw [iteratedFDeriv_succ_eq_comp_left]
    refine (LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm
      (fderiv ℝ (iteratedFDeriv ℝ n h)) x l).trans ?_
    rw [norm_iteratedFDeriv_fderiv, ih]
    rw [show l + 1 + n = l + (n + 1) by omega]

theorem translate_component_bound (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (r : ℝ) (hr : 0 < r) :
    ∃ K : ENNReal, K ≠ ⊤ ∧ ∀ (y : R3) (g : R3 → F), ContDiffOn ℝ ∞ g (ball y r) →
      ‖g y‖ₑ ≤ K *
          (eLpNorm (iteratedFDeriv ℝ 0 g) 2 ((volume : Measure R3).restrict (ball y r)) +
            eLpNorm (iteratedFDeriv ℝ 1 g) 2 ((volume : Measure R3).restrict (ball y r)) +
            eLpNorm (iteratedFDeriv ℝ 2 g) 2 ((volume : Measure R3).restrict (ball y r))) := by
  obtain ⟨K, hK, hb⟩ :=
    ExteriorSource.Literature.LocalSobolevJet.component_bound F (0 : R3) r hr
  refine ⟨K, hK, fun y g hg => ?_⟩
  have hmp : MeasurePreserving (fun z : R3 => z + y)
      ((volume : Measure R3).restrict (ball 0 r)) ((volume : Measure R3).restrict (ball y r)) := by
    have h1 := (measurePreserving_add_right (volume : Measure R3) y).restrict_preimage
      (measurableSet_ball (x := y) (ε := r))
    convert h1 using 2
    ext z; simp [dist_eq_norm]
  have hcd : ContDiffOn ℝ ∞ (fun z => g (z + y)) (ball 0 r) := by
    refine hg.comp (contDiff_id.add contDiff_const).contDiffOn ?_
    intro z hz; simpa [dist_eq_norm] using hz
  have heq : ∀ l : ℕ, eLpNorm (iteratedFDeriv ℝ l (fun z => g (z + y))) 2
      ((volume : Measure R3).restrict (ball 0 r)) =
      eLpNorm (iteratedFDeriv ℝ l g) 2 ((volume : Measure R3).restrict (ball y r)) := by
    intro l
    have : iteratedFDeriv ℝ l (fun z => g (z + y)) = (iteratedFDeriv ℝ l g) ∘ (fun z => z + y) := by
      funext z; exact iteratedFDeriv_comp_add_right l y z
    rw [this]
    exact eLpNorm_comp_measurePreserving
      (ExteriorSource.Literature.LocalSobolevJet.aestronglyMeasurable_iteratedFDeriv y r hg l) hmp
  have := hb _ hcd
  simp only [heq, zero_add] at this
  exact this

theorem finiteDimensional_cmm (n : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ) :=
  FiniteDimensional.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ) :
      ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ →ₗ[ℝ]
        MultilinearMap ℝ (fun _ : Fin n => R3) ℝ)
    ContinuousMultilinearMap.toMultilinearMap_injective

attribute [instance] finiteDimensional_cmm

open ExteriorSource.Literature.LocalSobolevJet in
theorem deriv_bound (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, ∀ (m : ℕ), n + 2 ≤ m → ∀ (U : Opens R3)
      (u : TauCeti.Wkp (volume : Measure R3) U 2 m) (h : R3 → ℝ), ContDiff ℝ ∞ h →
      (TauCeti.Wkp.value m u : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict U] h →
      ∀ y : R3, ball y r ⊆ U → ‖iteratedFDeriv ℝ n h y‖ ≤ C * ‖u‖ := by
  obtain ⟨K, hK, hb⟩ :=
    translate_component_bound (ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ) r hr
  refine ⟨3 * K.toReal, fun m hm U u h hh hu y hy => ?_⟩
  have hg : ContDiff ℝ ∞ (iteratedFDeriv ℝ n h) :=
    hh.iteratedFDeriv_right (by exact_mod_cast le_top)
  have hgy : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ n h) (ball y r) := hg.contDiffOn
  have hhU : ContDiffOn ℝ ∞ h U := hh.contDiffOn
  have hl : ∀ l : ℕ, l ≤ 2 → eLpNorm (iteratedFDeriv ℝ l (iteratedFDeriv ℝ n h)) 2
      ((volume : Measure R3).restrict (ball y r)) ≤ ENNReal.ofReal ‖u‖ := by
    intro l hl
    have h1 : eLpNorm (iteratedFDeriv ℝ l (iteratedFDeriv ℝ n h)) 2
        ((volume : Measure R3).restrict (ball y r)) =
        eLpNorm (iteratedFDeriv ℝ (l + n) h) 2 ((volume : Measure R3).restrict (ball y r)) :=
      eLpNorm_congr_norm_ae (aestronglyMeasurable_iteratedFDeriv y r hgy l)
        (aestronglyMeasurable_iteratedFDeriv y r hh.contDiffOn (l + n))
        (Filter.Eventually.of_forall fun x => norm_iteratedFDeriv_iteratedFDeriv h n l x)
    rw [h1]
    refine le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono hy le_rfl)) ?_
    exact eLpNorm_iteratedFDeriv_le U m u hhU hu (l + n) (by omega)
  have : ‖iteratedFDeriv ℝ n h y‖ₑ ≤
      K * (ENNReal.ofReal ‖u‖ + ENNReal.ofReal ‖u‖ + ENNReal.ofReal ‖u‖) :=
    (hb y _ hgy).trans (mul_le_mul_right (add_le_add (add_le_add (hl 0 (by norm_num))
      (hl 1 (by norm_num))) (hl 2 (by norm_num))) K)
  exact norm_le_of_enorm_le _ hK (norm_nonneg u) this

theorem tendstoUniformlyOn_curryLeft {m : ℕ} {V : Set R3}
    {F : ℕ → R3 → ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => R3) ℝ}
    {G : R3 → ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => R3) ℝ}
    (h : TendstoUniformlyOn F G atTop V) :
    TendstoUniformlyOn (fun j x => (F j x).curryLeft) (fun x => (G x).curryLeft) atTop V := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with j hj x hx
  have e : (G x).curryLeft - (F j x).curryLeft = (G x - F j x).curryLeft := by
    ext; simp
  rw [dist_eq_norm, e, ContinuousMultilinearMap.curryLeft_norm, ← dist_eq_norm]
  exact hj x hx

theorem limit_contDiffOn {V : Set R3} (hV : IsOpen V) (k : ℕ) (φ : ℕ → R3 → ℝ)
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hC : ∀ n ≤ k, UniformCauchySeqOn (fun j => iteratedFDeriv ℝ n (φ j)) atTop V) :
    ∃ f : R3 → ℝ, ContDiffOn ℝ k f V ∧ ∀ y ∈ V, Tendsto (fun j => φ j y) atTop (𝓝 (f y)) := by
  let G : (n : ℕ) → R3 → ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) ℝ :=
    fun n y => limUnder atTop (fun j => iteratedFDeriv ℝ n (φ j) y)
  have hT : ∀ n ≤ k, TendstoUniformlyOn (fun j => iteratedFDeriv ℝ n (φ j)) (G n) atTop V :=
    fun n hn => (hC n hn).tendstoUniformlyOn_of_tendsto
      (fun y hy => ((hC n hn).cauchySeq hy).tendsto_limUnder)
  let p : R3 → FormalMultilinearSeries ℝ R3 ℝ := fun y n => G n y
  have hser : ∀ j, HasFTaylorSeriesUpTo (⊤ : ℕ∞) (φ j) (ftaylorSeries ℝ (φ j)) :=
    fun j => contDiff_iff_ftaylorSeries.1 (hφ j)
  have hp : HasFTaylorSeriesUpToOn (k : ℕ∞) (fun y => (G 0 y).curry0) p V := by
    refine ⟨fun x _ => rfl, ?_, ?_⟩
    · intro m hm x hx
      have hm' : m < k := by exact_mod_cast hm
      refine (hasFDerivAt_of_tendstoUniformlyOn (l := atTop) hV
        (f := fun j => iteratedFDeriv ℝ m (φ j))
        (f' := fun j x => (iteratedFDeriv ℝ (m + 1) (φ j) x).curryLeft)
        (tendstoUniformlyOn_curryLeft (hT (m + 1) (by omega)))
        (fun j x _ => (hser j).fderiv m (by exact_mod_cast WithTop.coe_lt_top _) x)
        (fun x hx => (hT m hm'.le).tendsto_at hx) hx).hasFDerivWithinAt
    · intro m hm
      have hm' : m ≤ k := by exact_mod_cast hm
      exact (hT m hm').continuousOn (Eventually.of_forall (f := atTop) fun j =>
        ((hφ j).continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).continuousOn).frequently
  refine ⟨_, hp.contDiffOn, fun y hy => ?_⟩
  have h0 := ((continuousMultilinearCurryFin0 ℝ R3 ℝ).continuous.tendsto (G 0 y)).comp
    ((hT 0 (by omega)).tendsto_at hy)
  refine h0.congr fun j => ?_
  simp [Function.comp]

open scoped Distributions in
theorem local_order (w : R3 → ℝ) (x : R3) (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ)
    (W : TauCeti.Wkp (volume : Measure R3) (⟨ball x ρ, isOpen_ball⟩ : Opens R3) 2 (k + 2))
    (hW : ⇑(TauCeti.Wkp.value (k + 2) W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] w) :
    ∃ f : R3 → ℝ, ContDiffOn ℝ k f (ball x (ρ / 4)) ∧
      f =ᵐ[(volume : Measure R3).restrict (ball x (ρ / 4))] w := by
  let Ω : Opens R3 := ⟨ball x ρ, isOpen_ball⟩
  let U : Opens R3 := ⟨ball x (ρ / 2), isOpen_ball⟩
  have hcl : closure (U : Set R3) = closedBall x (ρ / 2) := closure_ball x (by positivity)
  have hcompact : IsCompact (closure (U : Set R3)) := by
    rw [hcl]; exact isCompact_closedBall x _
  have hclosure : closure (U : Set R3) ⊆ Ω := by
    rw [hcl]; exact closedBall_subset_ball (by linarith)
  have hUO : U ≤ Ω := SetLike.coe_subset_coe.mp (subset_closure.trans hclosure)
  obtain ⟨ψ, hψ⟩ := TauCeti.Wkp.exists_testFunction_approximation_restrictL
    (mu := (volume : Measure R3)) (p := 2) (by norm_num) hcompact hclosure (k + 2) W
  let u : ℕ → TauCeti.Wkp (volume : Measure R3) U 2 (k + 2) := fun j =>
    TauCeti.Wkp.restrictL hUO (k + 2)
      (TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure R3)) (p := 2) (k + 2) (ψ j))
  have hu : Tendsto u atTop (𝓝 (TauCeti.Wkp.restrictL hUO (k + 2) W)) := hψ
  have hψs : ∀ j, ContDiff ℝ ∞ (ψ j : R3 → ℝ) := fun j => (ψ j).contDiff
  have hval : ∀ j, (TauCeti.Wkp.value (k + 2) (u j) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict U] (ψ j : R3 → ℝ) := by
    intro j
    refine (TauCeti.Wkp.value_restrictL_ae hUO (k + 2) _).trans ?_
    rw [TauCeti.Wkp.value_ofTestFunctionₗ]
    exact ae_restrict_of_ae_restrict_of_subset (show (U : Set R3) ⊆ Ω from hUO)
      (TauCeti.testFunctionLp_apply_ae 2 (ψ j))
  have hsub : ∀ y ∈ ball x (ρ / 4), ball y (ρ / 4) ⊆ (U : Set R3) := by
    intro y hy z hz
    show z ∈ ball x (ρ / 2)
    rw [mem_ball] at hy hz ⊢
    linarith [dist_triangle z y x]
  have hC : ∀ n ≤ k, UniformCauchySeqOn (fun j => iteratedFDeriv ℝ n (ψ j : R3 → ℝ)) atTop
      (ball x (ρ / 4)) := by
    intro n hn
    obtain ⟨C, hCb⟩ := deriv_bound n (ρ / 4) (by positivity)
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq (ε / (|C| + 1)) (by positivity)
    refine ⟨N, fun a ha b hb y hy => ?_⟩
    have hd : (TauCeti.Wkp.value (k + 2) (u a - u b) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict U] (⇑(ψ a) - ⇑(ψ b)) := by
      rw [← TauCeti.Wkp.valueL_apply, map_sub, TauCeti.Wkp.valueL_apply,
        TauCeti.Wkp.valueL_apply]
      filter_upwards [Lp.coeFn_sub (TauCeti.Wkp.value (k + 2) (u a))
        (TauCeti.Wkp.value (k + 2) (u b)), hval a, hval b] with z hz ha hb
      rw [hz, Pi.sub_apply, ha, hb, Pi.sub_apply]
    have hb' := hCb (k + 2) (by omega) U (u a - u b) (⇑(ψ a) - ⇑(ψ b))
      ((hψs a).sub (hψs b)) hd y (hsub y hy)
    rw [iteratedFDeriv_sub_apply ((hψs a).contDiffAt.of_le (by exact_mod_cast le_top))
      ((hψs b).contDiffAt.of_le (by exact_mod_cast le_top))] at hb'
    rw [dist_eq_norm]
    have h1 : ‖u a - u b‖ < ε / (|C| + 1) := by rw [← dist_eq_norm]; exact hN a ha b hb
    calc _ ≤ C * ‖u a - u b‖ := hb'
      _ ≤ |C| * ‖u a - u b‖ := by gcongr; exact le_abs_self C
      _ ≤ |C| * (ε / (|C| + 1)) := by gcongr
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]
  obtain ⟨f, hf, hlim⟩ := limit_contDiffOn isOpen_ball k (fun j => (ψ j : R3 → ℝ)) hψs hC
  refine ⟨f, hf, ?_⟩
  have hvL : Tendsto (fun j => TauCeti.Wkp.value (k + 2) (u j)) atTop
      (𝓝 (TauCeti.Wkp.value (k + 2) (TauCeti.Wkp.restrictL hUO (k + 2) W))) := by
    simp only [← TauCeti.Wkp.valueL_apply]
    exact ((TauCeti.Wkp.valueL (k + 2)).continuous.tendsto _).comp hu
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvL).exists_seq_tendsto_ae
  have hall : ∀ᵐ z ∂(volume : Measure R3).restrict U,
      ∀ j, (TauCeti.Wkp.value (k + 2) (u j) : R3 → ℝ) z = ψ j z := ae_all_iff.2 hval
  have hWU : (TauCeti.Wkp.value (k + 2) (TauCeti.Wkp.restrictL hUO (k + 2) W) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict U] w :=
    (TauCeti.Wkp.value_restrictL_ae hUO (k + 2) W).trans
      (ae_restrict_of_ae_restrict_of_subset (show (U : Set R3) ⊆ Ω from hUO) hW)
  have hVU : ball x (ρ / 4) ⊆ (U : Set R3) := ball_subset_ball (by linarith)
  have hres := ae_restrict_of_ae_restrict_of_subset hVU (hae.and (hall.and hWU))
  filter_upwards [hres, ae_restrict_mem measurableSet_ball] with z hz hzV
  obtain ⟨h1, h2, h3⟩ := hz
  have h4 : Tendsto (fun i => ψ (ns i) z) atTop (𝓝 (w z)) := by
    rw [← h3]; exact h1.congr fun i => h2 (ns i)
  exact tendsto_nhds_unique ((hlim z hzV).comp hns.tendsto_atTop) h4

theorem local_smooth (w : R3 → ℝ) (x : R3) (ρ : ℝ) (hρ : 0 < ρ)
    (hW : ∀ k : ℕ,
      ∃ W : TauCeti.Wkp (volume : Measure R3) (⟨ball x ρ, isOpen_ball⟩ : Opens R3) 2 k,
        ⇑(TauCeti.Wkp.value k W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] w) :
    ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f (ball x (ρ / 4)) ∧
      f =ᵐ[(volume : Measure R3).restrict (ball x (ρ / 4))] w := by
  have h : ∀ k : ℕ, ∃ f : R3 → ℝ, ContDiffOn ℝ k f (ball x (ρ / 4)) ∧
      f =ᵐ[(volume : Measure R3).restrict (ball x (ρ / 4))] w := by
    intro k
    obtain ⟨W, hW'⟩ := hW (k + 2)
    exact local_order w x ρ hρ k W hW'
  choose f hf hfw using h
  refine ⟨f 0, contDiffOn_infty.2 fun k => ?_, hfw 0⟩
  have heq : Set.EqOn (f k) (f 0) (ball x (ρ / 4)) :=
    Measure.eqOn_open_of_ae_eq ((hfw k).trans (hfw 0).symm) isOpen_ball
      (hf k).continuousOn (hf 0).continuousOn
  exact (hf k).congr fun y hy => (heq hy).symm

end OAI.AnisotropicCalderon.Regularity.SmoothRepAux

namespace OAI.AnisotropicCalderon.Regularity
open TauCeti
open Filter Topology

open SmoothRepAux in
/-- A function that is locally in every `W^{k,2}` has a smooth representative. -/
theorem exists_contDiffOn_ae_eq {O : Set R3} (hO : IsOpen O) {w : R3 → ℝ}
    (hloc : ∀ x ∈ O, ∃ ρ > 0, ball x ρ ⊆ O ∧ ∀ k : ℕ,
      ∃ W : Wkp (volume : Measure R3) (⟨ball x ρ, isOpen_ball⟩ : Opens R3) 2 k,
        ⇑(Wkp.value k W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] w) :
    ∃ w' : R3 → ℝ, ContDiffOn ℝ ∞ w' O ∧ w' =ᵐ[(volume : Measure R3).restrict O] w := by
  have hloc' : ∀ x ∈ O, ∃ r > 0, ball x r ⊆ O ∧ ∃ f : R3 → ℝ, ContDiffOn ℝ ∞ f (ball x r) ∧
      f =ᵐ[(volume : Measure R3).restrict (ball x r)] w := by
    intro x hx
    obtain ⟨ρ, hρ, hρO, hW⟩ := hloc x hx
    exact ⟨ρ / 4, by positivity, (ball_subset_ball (by linarith)).trans hρO,
      local_smooth w x ρ hρ hW⟩
  choose r hr hrO f hf hfw using hloc'
  classical
  let w' : R3 → ℝ := fun y => if hy : y ∈ O then f y hy y else 0
  have key : ∀ z (hz : z ∈ O), ∀ y ∈ ball z (r z hz), w' y = f z hz y := by
    intro z hz y hy
    have hyO : y ∈ O := hrO z hz hy
    have hw' : w' y = f y hyO y := by simp [w', hyO]
    rw [hw']
    let S := ball z (r z hz) ∩ ball y (r y hyO)
    have hS : IsOpen S := isOpen_ball.inter isOpen_ball
    have hyS : y ∈ S := ⟨hy, mem_ball_self (hr y hyO)⟩
    have e1 : f z hz =ᵐ[(volume : Measure R3).restrict S] w :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hfw z hz)
    have e2 : f y hyO =ᵐ[(volume : Measure R3).restrict S] w :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hfw y hyO)
    exact (Measure.eqOn_open_of_ae_eq (e2.trans e1.symm) hS
      ((hf y hyO).continuousOn.mono Set.inter_subset_right)
      ((hf z hz).continuousOn.mono Set.inter_subset_left) hyS)
  refine ⟨w', fun z hz => ?_, ?_⟩
  · have hev : w' =ᶠ[𝓝 z] f z hz :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self (hr z hz))) (key z hz)
    exact (((hf z hz).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (hr z hz)))).congr_of_eventuallyEq
      hev).contDiffWithinAt
  · obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : O => ball (i : R3) (r i i.2)) (fun i => isOpen_ball)
    have hO' : O = ⋃ i ∈ T, ball (i : R3) (r i i.2) := by
      rw [hTU]
      ext y
      simp only [Set.mem_iUnion]
      exact ⟨fun hy => ⟨⟨y, hy⟩, mem_ball_self (hr y hy)⟩,
        fun ⟨i, hi⟩ => hrO i i.2 hi⟩
    rw [hO', Filter.EventuallyEq, ae_restrict_biUnion_iff _ hT]
    intro i _
    filter_upwards [hfw i i.2, ae_restrict_mem measurableSet_ball] with y hy hyb
    rw [key i i.2 y hyb, hy]

end OAI.AnisotropicCalderon.Regularity
